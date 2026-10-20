//! The cooperative drain: `Supervisor::drain` fences an actor, lets the handler that
//! is running finish, drops the service, and leaves the mailbox answering `FENCED`.
//!
//! Tested, not proved: the ownership fence is the proved part, and what is checked
//! here is that the drain around it does what its documentation says.

use std::future::Future;
use std::num::NonZeroU32;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Duration;

use jetstream::prelude::*;
use jetstream_distributed::actor::service::{
    ActorRef, Capacity, Fence, LocalSupervisor, Status, Supervisor,
};
use jetstream_distributed::id::Id;
use jetstream_distributed::scheduling::discovery::{Discovery, DiscoveryError};
use tokio::sync::Notify;

use actorb_protocol::{ActorBChannel, ActorBService};

const ROOM: Capacity = Capacity::Bounded(NonZeroU32::new(16).unwrap());
const B: Id = Id(2);
const ME: Id = Id(7);

#[service]
trait ActorB {
    /// Returns how many calls `B` has handled, counting this one.
    async fn b(&self, ctx: Context) -> Result<u64>;
}

/// Sets a flag when it is dropped: the service was released.
struct Dropped(Arc<AtomicBool>);

impl Drop for Dropped {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

/// A `B` whose handler says it has started and then waits to be let go.
struct Gated {
    handled: Arc<AtomicU64>,
    started: Arc<Notify>,
    release: Arc<Notify>,
    _dropped: Dropped,
}

impl ActorB for Gated {
    async fn b(&self, _ctx: Context) -> Result<u64> {
        let n = self.handled.fetch_add(1, Ordering::SeqCst) + 1;
        self.started.notify_one();
        self.release.notified().await;
        Ok(n)
    }
}

/// A `B` whose handler waits to be let go and then panics.
struct PanicsWhenReleased {
    started: Arc<Notify>,
    release: Arc<Notify>,
}

impl ActorB for PanicsWhenReleased {
    async fn b(&self, _ctx: Context) -> Result<u64> {
        self.started.notify_one();
        self.release.notified().await;
        panic!("the handler panicked while the actor was draining");
    }
}

/// A `B` that just counts.
#[derive(Default)]
struct Counting(AtomicU64);

impl ActorB for Counting {
    async fn b(&self, _ctx: Context) -> Result<u64> {
        Ok(self.0.fetch_add(1, Ordering::SeqCst) + 1)
    }
}

fn open() -> impl Fence + 'static {
    || true
}

/// Wait for `fut`, but not for ever.
async fn within<T>(fut: impl Future<Output = T>) -> T {
    tokio::time::timeout(Duration::from_secs(5), fut)
        .await
        .expect("it happened within five seconds")
}

/// Wait until `cond` holds.
async fn until(cond: impl Fn() -> bool) {
    within(async {
        while !cond() {
            tokio::time::sleep(Duration::from_millis(2)).await;
        }
    })
    .await
}

async fn channel_to_b(supervisor: &LocalSupervisor) -> Result<ActorBChannel> {
    let transport = supervisor
        .transport::<ActorBChannel>(B, Context::default())
        .await?;
    let channel = ActorBChannel::new(64, transport);
    channel.negotiate_version(u32::MAX).await?;
    Ok(channel)
}

/// **The drain is cooperative.** A handler that is running when `drain` is asked for
/// is finished, not cancelled; a request queued behind it is answered `FENCED` and
/// never handled; `drain` returns only once the handler is done; and the service is
/// released then, not before.
#[tokio::test]
async fn a_drain_lets_the_running_handler_finish_then_fences_and_releases() {
    let supervisor = Arc::new(LocalSupervisor::new(ME));
    let handled = Arc::new(AtomicU64::new(0));
    let started = Arc::new(Notify::new());
    let release = Arc::new(Notify::new());
    let dropped = Arc::new(AtomicBool::new(false));
    supervisor
        .spawn::<ActorBChannel, _, _>(
            B,
            ROOM,
            ActorBService {
                inner: Gated {
                    handled: handled.clone(),
                    started: started.clone(),
                    release: release.clone(),
                    _dropped: Dropped(dropped.clone()),
                },
            },
            open(),
        )
        .await
        .unwrap();
    let channel = Arc::new(channel_to_b(&supervisor).await.unwrap());

    // A handler is running.
    let first = tokio::spawn({
        let channel = channel.clone();
        async move { channel.b(Context::default()).await }
    });
    within(started.notified()).await;
    assert_eq!(supervisor.status(B), Status::Running);

    // The drain is asked for. It must not return while the handler runs.
    let drain = tokio::spawn({
        let supervisor = supervisor.clone();
        async move { supervisor.drain(B).await }
    });
    until(|| supervisor.status(B) == Status::Draining).await;
    assert!(!drain.is_finished(), "drain waits for the running handler");
    assert!(
        !dropped.load(Ordering::SeqCst),
        "and the service is still held"
    );
    assert_eq!(
        supervisor.discover(ActorRef(B)),
        Err(DiscoveryError::NotFound),
        "a draining actor is not where a caller should go"
    );
    assert!(
        supervisor
            .transport::<ActorBChannel>(B, Context::default())
            .await
            .is_err(),
        "and a new session is refused"
    );

    // A request arrives behind the running one, and is on the mailbox's queue before
    // the handler is let go, so the loop meets it with the fence and not with the
    // retire signal. (If the pause were too short the test would pass for the wrong
    // reason, never fail for one.)
    let second = tokio::spawn({
        let channel = channel.clone();
        async move { channel.b(Context::default()).await }
    });
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Let the handler go: the request that was running completes, normally.
    release.notify_one();
    assert_eq!(within(first).await.unwrap().unwrap(), 1);
    within(drain).await.unwrap().unwrap();

    assert_eq!(supervisor.status(B), Status::Retired);
    assert!(dropped.load(Ordering::SeqCst), "the service was released");
    let refused = within(second).await.unwrap().unwrap_err();
    assert_eq!(refused.code(), Some("FENCED"));
    assert_eq!(
        handled.load(Ordering::SeqCst),
        1,
        "the queued one never ran"
    );

    // A session made before the drain is answered, not left waiting.
    let stale = within(channel.b(Context::default())).await.unwrap_err();
    assert_eq!(stale.code(), Some("FENCED"));
    assert_eq!(handled.load(Ordering::SeqCst), 1);

    // Draining again is a no-op.
    within(supervisor.drain(B)).await.unwrap();
    assert_eq!(supervisor.status(B), Status::Retired);
}

/// **A drained actor can come back, on the same mailbox.** The session that was made
/// before the drain, and was being told `FENCED`, is served by the new service.
#[tokio::test]
async fn a_retired_actor_comes_back_and_its_old_sessions_work() {
    let supervisor = LocalSupervisor::new(ME);
    supervisor
        .spawn::<ActorBChannel, _, _>(
            B,
            ROOM,
            ActorBService {
                inner: Counting::default(),
            },
            open(),
        )
        .await
        .unwrap();
    let channel = channel_to_b(&supervisor).await.unwrap();
    assert_eq!(channel.b(Context::default()).await.unwrap(), 1);

    within(supervisor.drain(B)).await.unwrap();
    let refused = within(channel.b(Context::default())).await.unwrap_err();
    assert_eq!(refused.code(), Some("FENCED"));

    // It cannot be re-hosted while it is being served, but a retired one can.
    supervisor
        .spawn::<ActorBChannel, _, _>(
            B,
            ROOM,
            ActorBService {
                inner: Counting::default(),
            },
            open(),
        )
        .await
        .expect("a retired actor can be hosted again");
    assert_eq!(supervisor.status(B), Status::Running);
    assert_eq!(supervisor.discover(ActorRef(B)), Ok(vec![ME]));
    assert!(
        supervisor
            .spawn::<ActorBChannel, _, _>(
                B,
                ROOM,
                ActorBService {
                    inner: Counting::default()
                },
                open(),
            )
            .await
            .is_err(),
        "and not twice"
    );

    // The old session, on the old mailbox, reaches the new service (a fresh count).
    assert_eq!(within(channel.b(Context::default())).await.unwrap(), 1);
}

/// What `drain` refuses: an actor that was never hosted.
#[tokio::test]
async fn draining_an_actor_that_is_not_hosted_is_an_error() {
    let supervisor = LocalSupervisor::new(ME);
    assert!(supervisor.drain(B).await.is_err());
    assert_eq!(supervisor.status(B), Status::Absent);
}

/// If the handler that is running panics, the actor is stopped, not retired, and
/// `drain` says so instead of reporting a release that did not happen.
#[tokio::test]
async fn a_handler_that_panics_while_the_actor_drains_stops_it() {
    let supervisor = Arc::new(LocalSupervisor::new(ME));
    let started = Arc::new(Notify::new());
    let release = Arc::new(Notify::new());
    supervisor
        .spawn::<ActorBChannel, _, _>(
            B,
            ROOM,
            ActorBService {
                inner: PanicsWhenReleased {
                    started: started.clone(),
                    release: release.clone(),
                },
            },
            open(),
        )
        .await
        .unwrap();
    let channel = Arc::new(channel_to_b(&supervisor).await.unwrap());
    let call = tokio::spawn({
        let channel = channel.clone();
        async move { channel.b(Context::default()).await }
    });
    within(started.notified()).await;

    let drain = tokio::spawn({
        let supervisor = supervisor.clone();
        async move { supervisor.drain(B).await }
    });
    until(|| supervisor.status(B) == Status::Draining).await;
    release.notify_one();

    assert!(
        within(drain).await.unwrap().is_err(),
        "the drain did not complete"
    );
    assert!(
        within(call).await.unwrap().is_err(),
        "the caller is told, not left waiting"
    );
    until(|| supervisor.status(B) == Status::Stopped).await;
}
