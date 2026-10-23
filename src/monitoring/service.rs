use std::time::Duration;

use jetstream::prelude::*;
use tokio::sync::{broadcast, broadcast::error::RecvError, mpsc};

use crate::{
    compute::Resources,
    monitoring::{
        coordinate::Coordinate,
        resources::{MIN_INTERVAL, Sampler},
    },
};

/// What the room says when a subscription ends normally. This is the
/// value a plain `Stream` has nowhere to put.
#[derive(Debug, Clone, JetStreamWireFormat)]
pub struct Closed {
    /// The number of the last event the subscription sent, or 0 if it sent none.
    pub last_seq: u64,
}

#[service(uses(super::{Closed, Sequenced}))]
pub trait Monitor {
    #[subscription]
    fn monitor(&self, ctx: Context) -> Subscription<Sequenced, Closed>;
}

#[derive(Debug, Clone, JetStreamWireFormat)]
pub enum Event {
    Heartbeat,
    Coordinate(super::coordinate::Coordinate),
    Resources(Resources),
}

/// An event, and its place in the node's order.
///
/// The node numbers every event it publishes, from 1, one after another, in the one
/// place that sees them all. A subscriber that was too slow loses events, and the
/// numbers are how it finds out: a jump from `n` to anything but `n + 1` is a gap.
#[derive(Debug, Clone, JetStreamWireFormat)]
pub struct Sequenced {
    /// This event's number: the first the node publishes is 1.
    pub seq: u64,
    /// What happened.
    pub event: Event,
}

/// How many events a slow subscriber may fall behind before it loses the oldest.
const BEHIND: usize = 256;

/// How many events wait for the loop to number them.
const WAITING: usize = 64;

/// How often a node publishes the resources it has available.
const RESOURCES_EVERY: Duration = Duration::from_secs(5);

#[derive(Debug)]
pub struct NodeMonitor {
    /// Every numbered event. Subscribers [`subscribe`](broadcast::Sender::subscribe).
    events: broadcast::Sender<Sequenced>,
    /// Where a source hands an event to be numbered and published.
    inbox: mpsc::Sender<Event>,
    monitor_loop: tokio::task::JoinHandle<()>,
    cancel: broadcast::Sender<()>,
}

impl NodeMonitor {
    /// A monitor that publishes a heartbeat every second and this node's available
    /// resources every `resources_every`, and whatever a source [`publish`]es.
    /// Must be called inside a tokio runtime.
    ///
    /// [`publish`]: NodeMonitor::publish
    fn new(resources_every: Duration) -> Self {
        Self::with_room(resources_every, BEHIND)
    }

    /// As [`new`](NodeMonitor::new), with room for `behind` events in the channel
    /// subscribers read from.
    fn with_room(resources_every: Duration, behind: usize) -> Self {
        let (events, _) = broadcast::channel(behind);
        let (inbox, mut waiting) = mpsc::channel(WAITING);
        let (cancel_tx, mut cancel_rx) = broadcast::channel(1);

        let mut beat = tokio::time::interval(Duration::from_secs(1));
        let mut sampler = Sampler::new();
        // The first reading waits out the sampler's warm-up: CPU usage is a
        // difference between two reads, and one taken sooner would say idle.
        let mut resources =
            tokio::time::interval_at(tokio::time::Instant::now() + MIN_INTERVAL, resources_every);
        // A slow tick is skipped, not made up for with a burst of readings.
        resources.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

        let publish_to = events.clone();
        let monitor_loop = tokio::spawn(async move {
            // The only writer, so the count needs no atomic: it is this task's.
            let mut seq = 0u64;
            let mut publish = |event: Event| {
                seq += 1;
                publish_to.send(Sequenced { seq, event }).ok();
            };
            loop {
                tokio::select! {
                    _ = beat.tick() => publish(Event::Heartbeat),
                    _ = resources.tick() => publish(Event::Resources(sampler.measure().available)),
                    Some(event) = waiting.recv() => publish(event),
                    _ = cancel_rx.recv() => break,
                };
            }
        });
        Self {
            events,
            inbox,
            monitor_loop,
            cancel: cancel_tx,
        }
    }

    /// Hand `event` to the loop, which numbers it and sends it to every subscriber.
    ///
    /// It waits if the loop is behind. If the loop has stopped the event comes back.
    async fn publish(&self, event: Event) -> std::result::Result<(), Event> {
        self.inbox.send(event).await.map_err(|rejected| rejected.0)
    }
}

impl Default for NodeMonitor {
    fn default() -> Self {
        Self::new(RESOURCES_EVERY)
    }
}

impl Drop for NodeMonitor {
    fn drop(&mut self) {
        self.cancel.send(()).ok();
    }
}

impl Monitor for NodeMonitor {
    fn monitor(&self, _ctx: Context) -> Subscription<Sequenced, Closed> {
        let mut events = self.events.subscribe();
        Subscription::producing(64, move |producer| async move {
            let mut last_seq = 0u64;
            // Everything arrives from the node's own loop, numbered, heartbeats
            // included, so this only forwards. A subscriber that has gone is found
            // out by the next send, which is never more than a heartbeat away.
            loop {
                match events.recv().await {
                    Ok(event) => {
                        let seq = event.seq;
                        if producer.send(event).await.is_err() {
                            return;
                        }
                        last_seq = seq;
                    }
                    // Too slow: some events were dropped. Carry on from the oldest
                    // one still held; the jump in `seq` tells the subscriber.
                    Err(RecvError::Lagged(_)) => continue,
                    // The node has gone: the stream ends normally.
                    Err(RecvError::Closed) => break,
                }
            }
            producer.finish(Closed { last_seq }).await
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compute::{Cpu, Memory};

    /// A resources value no machine would report, so a test can tell it from the
    /// node's own readings.
    fn marker(n: u64) -> Event {
        Event::Resources(Resources {
            cpu: Cpu::millicores(n),
            memory: Memory::bytes(n),
        })
    }

    fn is_marker(event: &Event, n: u64) -> bool {
        matches!(event, Event::Resources(r) if r.cpu == Cpu::millicores(n) && r.memory == Memory::bytes(n))
    }

    /// The node publishes what it has available, on its own schedule, to whoever is
    /// listening: no one asked, and no subscriber had to.
    #[tokio::test]
    async fn a_node_publishes_its_available_resources() {
        let monitor = NodeMonitor::new(Duration::from_millis(50));
        let mut events = monitor.events.subscribe();

        let found = tokio::time::timeout(Duration::from_secs(5), async {
            loop {
                if let Ok(Sequenced {
                    event: Event::Resources(available),
                    ..
                }) = events.recv().await
                {
                    return available;
                }
            }
        })
        .await
        .expect("no Resources event within five seconds");

        // It is what the machine has free: some memory, and no more CPU than the
        // machine has cores.
        let capacity = Sampler::new().measure().capacity;
        assert!(
            found.fits(capacity) && found.memory.as_bytes() > 0,
            "{found:?}"
        );
    }

    #[tokio::test]
    async fn heartbeats_still_come() {
        let monitor = NodeMonitor::new(Duration::from_secs(3600));
        let mut events = monitor.events.subscribe();
        let beat = tokio::time::timeout(Duration::from_secs(5), async {
            loop {
                if let Ok(Sequenced {
                    event: Event::Heartbeat,
                    ..
                }) = events.recv().await
                {
                    return;
                }
            }
        })
        .await;
        assert!(beat.is_ok(), "no heartbeat within five seconds");
    }

    /// **Every event has the next number**, whoever published it: the node's own
    /// heartbeats and what a source hands in share one count.
    #[tokio::test]
    async fn events_are_numbered_one_after_another() {
        let monitor = NodeMonitor::new(Duration::from_secs(3600));
        let mut events = monitor.events.subscribe();
        for n in 1..=3 {
            monitor.publish(marker(n)).await.unwrap();
        }

        let mut seen = Vec::new();
        tokio::time::timeout(Duration::from_secs(5), async {
            while seen
                .iter()
                .filter(|s: &&Sequenced| matches!(s.event, Event::Resources(_)))
                .count()
                < 3
            {
                seen.push(events.recv().await.unwrap());
            }
        })
        .await
        .expect("the published events never arrived");

        for (i, sequenced) in seen.iter().enumerate() {
            assert_eq!(sequenced.seq, i as u64 + 1, "{seen:?}");
        }
    }

    /// What a source publishes reaches a subscriber in the order it was handed in.
    #[tokio::test]
    async fn a_published_event_arrives_in_order() {
        let monitor = NodeMonitor::new(Duration::from_secs(3600));
        let mut events = monitor.events.subscribe();
        monitor.publish(marker(11)).await.unwrap();
        monitor.publish(marker(22)).await.unwrap();

        let mut order = Vec::new();
        tokio::time::timeout(Duration::from_secs(5), async {
            while order.len() < 2 {
                let sequenced = events.recv().await.unwrap();
                if is_marker(&sequenced.event, 11) || is_marker(&sequenced.event, 22) {
                    order.push(sequenced);
                }
            }
        })
        .await
        .expect("the published events never arrived");

        assert!(is_marker(&order[0].event, 11) && is_marker(&order[1].event, 22));
        assert!(order[0].seq < order[1].seq);
    }

    /// **A subscriber that falls behind can tell.** It loses the oldest events, and
    /// the numbers after the loss jump by the number it lost.
    #[tokio::test]
    async fn a_slow_subscriber_sees_the_gap() {
        let monitor = NodeMonitor::with_room(Duration::from_secs(3600), 4);
        let mut events = monitor.events.subscribe();
        for n in 1..=20 {
            monitor.publish(marker(n)).await.unwrap();
        }

        let skipped = match tokio::time::timeout(Duration::from_secs(5), events.recv()).await {
            Ok(Err(RecvError::Lagged(skipped))) => skipped,
            other => panic!("expected the subscriber to have lagged, got {other:?}"),
        };
        assert!(skipped > 0);
        // Nothing was read before, so the next event held is number `skipped + 1`.
        let next = events.recv().await.unwrap();
        assert_eq!(next.seq, skipped + 1, "{next:?}");
    }

    /// With the node gone a subscriber's channel closes.
    #[tokio::test]
    async fn dropping_the_node_closes_its_subscribers() {
        let monitor = NodeMonitor::new(Duration::from_secs(3600));
        let mut events = monitor.events.subscribe();
        drop(monitor);
        let end = tokio::time::timeout(Duration::from_secs(5), async {
            loop {
                if let Err(RecvError::Closed) = events.recv().await {
                    return;
                }
            }
        })
        .await;
        assert!(end.is_ok(), "the channel never closed");
    }
}
