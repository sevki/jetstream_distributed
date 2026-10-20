//! The supervisor sketch: actors hosted by id, found by `Discovery`, and called as if
//! they were values.
//!
//! `ActorAImpl<B: ActorB>` is the same generic caller as in `actor_mailbox.rs`. What
//! changes is where its `B` comes from: not a mailbox the test built, but a transport
//! the supervisor handed out for an actor id.

use std::num::NonZeroU32;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use jetstream::prelude::*;
use jetstream_distributed::actor::service::{
    ActorId, ActorRef, Capacity, Fence, LocalSupervisor, Status, Supervisor,
};
use jetstream_distributed::id::Id;
use jetstream_distributed::scheduling::discovery::{Discovery, DiscoveryError};

use actora_protocol::{ActorAChannel, ActorAService};
use actorb_protocol::{ActorBChannel, ActorBService};

const ROOM: Capacity = Capacity::Bounded(NonZeroU32::new(16).unwrap());

const A: ActorId = 1;
const B: ActorId = 2;

/// The node these tests' supervisor runs on.
const ME: Id = Id(7);

#[service]
trait ActorB {
    /// Returns how many calls `B` has handled, counting this one.
    async fn b(&self, ctx: Context) -> Result<u64>;
}

#[service]
trait ActorA {
    async fn a(&self, ctx: Context) -> Result<u64>;
}

#[derive(Default)]
struct ActorBImpl {
    handled: std::sync::atomic::AtomicU64,
}

impl ActorB for ActorBImpl {
    async fn b(&self, _ctx: Context) -> Result<u64> {
        Ok(self
            .handled
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            + 1)
    }
}

struct ActorAImpl<B> {
    b: B,
}

impl<B: ActorB + Send + Sync> ActorA for ActorAImpl<B> {
    async fn a(&self, ctx: Context) -> Result<u64> {
        self.b.b(ctx).await
    }
}

/// A fence that always lets the host serve.
fn open() -> impl Fence + 'static {
    || true
}

/// Host a fresh `B` as actor `B`.
async fn host_b(supervisor: &LocalSupervisor) -> Result<()> {
    supervisor
        .spawn::<ActorBChannel, _, _>(
            B,
            ROOM,
            ActorBService {
                inner: ActorBImpl::default(),
            },
            open(),
        )
        .await
}

/// A channel to the actor `id`, which speaks `B`'s protocol.
async fn channel_to_b(supervisor: &LocalSupervisor, id: ActorId) -> Result<ActorBChannel> {
    let transport = supervisor
        .transport::<ActorBChannel>(id, Context::default())
        .await?;
    let channel = ActorBChannel::new(64, transport);
    channel.negotiate_version(u32::MAX).await?;
    Ok(channel)
}

/// `A` is hosted, `B` is hosted, `A` is handed a channel to `B` by the supervisor, and
/// a caller reaches `A` through the supervisor too. Nothing in `ActorAImpl` mentions a
/// mailbox, a session or a supervisor.
#[tokio::test]
async fn actors_find_each_other_by_id() {
    let supervisor = LocalSupervisor::new(ME);

    host_b(&supervisor).await.unwrap();
    let a = ActorAImpl {
        b: channel_to_b(&supervisor, B).await.unwrap(),
    };
    supervisor
        .spawn::<ActorAChannel, _, _>(A, ROOM, ActorAService { inner: a }, open())
        .await
        .unwrap();

    assert_eq!(supervisor.status(A), Status::Running);
    assert_eq!(supervisor.status(B), Status::Running);

    let transport = supervisor
        .transport::<ActorAChannel>(A, Context::default())
        .await
        .unwrap();
    let a = ActorAChannel::new(64, transport);
    a.negotiate_version(u32::MAX).await.unwrap();

    assert_eq!(a.a(Context::default()).await.unwrap(), 1);
    assert_eq!(a.a(Context::default()).await.unwrap(), 2);
}

/// What the supervisor refuses: an id it has never heard of, hosting one twice, and
/// asking an actor for a protocol it does not speak.
#[tokio::test]
async fn the_supervisor_refuses_what_it_cannot_do() {
    let supervisor = LocalSupervisor::new(ME);

    assert_eq!(supervisor.status(B), Status::Absent, "nobody is hosted yet");
    assert!(
        supervisor
            .transport::<ActorBChannel>(B, Context::default())
            .await
            .is_err(),
        "and there is nothing to reach"
    );

    host_b(&supervisor).await.unwrap();
    assert!(host_b(&supervisor).await.is_err(), "an id is hosted once");

    assert!(
        supervisor
            .transport::<ActorAChannel>(B, Context::default())
            .await
            .is_err(),
        "B does not speak A's protocol, and is not mis-cast as if it did"
    );
}

/// The supervisor answers the scheduler's own `Discovery` trait about an actor: it
/// is on this node while it runs, and `NotFound` — not here — otherwise. A resource
/// that is not an actor is not one it knows.
#[tokio::test]
async fn discovery_places_a_running_actor_on_this_node() {
    let supervisor = LocalSupervisor::new(ME);
    assert_eq!(
        supervisor.discover(ActorRef(B)),
        Err(DiscoveryError::NotFound)
    );

    host_b(&supervisor).await.unwrap();
    assert_eq!(supervisor.discover(ActorRef(B)), Ok(vec![ME]));
    assert_eq!(
        supervisor.discover(ActorRef(A)),
        Err(DiscoveryError::NotFound),
        "only B is hosted"
    );
}

/// A `B` whose handler panics.
struct PanickingB;

impl ActorB for PanickingB {
    async fn b(&self, _ctx: Context) -> Result<u64> {
        panic!("the handler panicked");
    }
}

/// A handler that panics ends the actor's drain. The supervisor must not go on
/// reporting the actor as running — a transport to it would queue requests for a
/// drain that is gone — Discovery must stop placing it here, and the id can be
/// hosted again.
#[tokio::test]
async fn an_actor_whose_handler_panicked_is_stopped_and_can_be_restarted() {
    let supervisor = LocalSupervisor::new(ME);
    supervisor
        .spawn::<ActorBChannel, _, _>(B, ROOM, ActorBService { inner: PanickingB }, open())
        .await
        .unwrap();

    // The call is answered with an error as the drain unwinds. This channel is kept:
    // it is a session on the mailbox from before the stop.
    let old = Arc::new(channel_to_b(&supervisor, B).await.unwrap());
    assert!(old.b(Context::default()).await.is_err());

    // The task ends a moment after the answer; wait for the supervisor to see it.
    let stopped = async {
        while supervisor.status(B) == Status::Running {
            tokio::task::yield_now().await;
        }
    };
    tokio::time::timeout(std::time::Duration::from_secs(5), stopped)
        .await
        .expect("the supervisor noticed the drain had ended");

    assert_eq!(supervisor.status(B), Status::Stopped);
    assert_eq!(
        supervisor.discover(ActorRef(B)),
        Err(DiscoveryError::NotFound),
        "a stopped actor is not placed here"
    );
    assert!(
        supervisor
            .transport::<ActorBChannel>(B, Context::default())
            .await
            .is_err(),
        "no new requests are queued for a drain that is gone"
    );

    // A call on the old session now queues on a mailbox with no drain.
    let waiting = tokio::spawn({
        let old = old.clone();
        async move { old.b(Context::default()).await }
    });
    tokio::task::yield_now().await;

    // Restarted, it serves: the new drain takes over the same mailbox, so the call
    // the old session queued is answered by it and not stranded.
    host_b(&supervisor)
        .await
        .expect("the stopped id can be hosted again");
    assert_eq!(supervisor.status(B), Status::Running);
    let stranded = tokio::time::timeout(std::time::Duration::from_secs(5), waiting)
        .await
        .expect("a call queued before the restart was served by the new drain")
        .unwrap();
    assert_eq!(stranded.unwrap(), 1);

    // And a session made after the restart reaches the same drain.
    let channel = channel_to_b(&supervisor, B).await.unwrap();
    assert_eq!(channel.b(Context::default()).await.unwrap(), 2);
}

/// The fence `spawn` is given is the one the drain asks: while it says no, a request
/// to a hosted actor is answered `FENCED` and its handler does not run.
#[tokio::test]
async fn the_fence_given_to_spawn_gates_the_actors_requests() {
    let supervisor = LocalSupervisor::new(ME);
    let owner = Arc::new(AtomicBool::new(true));
    supervisor
        .spawn::<ActorBChannel, _, _>(
            B,
            ROOM,
            ActorBService {
                inner: ActorBImpl::default(),
            },
            {
                let owner = owner.clone();
                move || owner.load(Ordering::SeqCst)
            },
        )
        .await
        .unwrap();
    let channel = channel_to_b(&supervisor, B).await.unwrap();

    assert_eq!(channel.b(Context::default()).await.unwrap(), 1);

    owner.store(false, Ordering::SeqCst);
    let refused = channel.b(Context::default()).await.unwrap_err();
    assert_eq!(refused.code(), Some("FENCED"));

    owner.store(true, Ordering::SeqCst);
    assert_eq!(
        channel.b(Context::default()).await.unwrap(),
        2,
        "the refused call never reached the handler"
    );
}
