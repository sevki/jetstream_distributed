use std::time::Duration;

use jetstream::prelude::*;

use crate::{compute::Resources, coordinate::Coordinate};

/// What the room says when a subscription ends normally. This is the
/// value a plain `Stream` has nowhere to put.
#[derive(Debug, Clone, JetStreamWireFormat)]
pub struct Closed {
    pub last_seq: u64,
}

#[service(uses(super::{Closed, Event}))]
pub trait Monitor {
    #[subscription]
    fn monitor(&self, ctx: Context) -> Subscription<Event, Closed>;
}

#[derive(Debug, Clone, JetStreamWireFormat)]
pub enum Event {
    Heartbeat,
    Coordinate(Coordinate),
    Resources(Resources),
}

#[derive(Debug)]
struct NodeMonitor {
    events: tokio::sync::broadcast::Receiver<Event>,
}

impl Monitor for NodeMonitor {
    fn monitor(&self, ctx: Context) -> Subscription<Event, Closed> {
        Subscription::producing(64, async move |producer| {
            loop {
                todo!()
            }
        })
    }
}
