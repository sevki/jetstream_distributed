//! Hosting an actor under a fence, calling it, and draining it.
//!
//! A [`LocalSupervisor`] hosts actors on one node, each behind its own mailbox. The
//! actor is an ordinary service; it is handed a [`Fence`], which is the question "may
//! this host still act for its actor?". In a deployment the fence is the ownership
//! registry's `may_write(host, epoch)`. Here it is a flag, so the example can close it.
//!
//! What it shows, in order: an actor is hosted and called; the fence closes and the
//! next request is refused `FENCED` without reaching the actor; the actor is drained
//! and its service dropped; and discovery stops pointing at it.
//!
//! Run it with `cargo run --example actor_hosting`.

use std::num::NonZeroU32;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use jetstream::prelude::*;
use jetstream_distributed::actor::service::{
    ActorRef, Capacity, LocalSupervisor, Status, Supervisor,
};
use jetstream_distributed::id::Id;
use jetstream_distributed::scheduling::discovery::{Discovery, DiscoveryError};

use counter_protocol::{CounterChannel, CounterService};

/// How many requests the actor's mailbox holds before a sender has to wait.
const ROOM: Capacity = Capacity::Bounded(NonZeroU32::new(16).unwrap());

/// This node, and the actor it hosts. Both are plain [`Id`]s.
const ME: Id = Id(1);
const COUNTER: Id = Id(42);

#[service]
trait Counter {
    /// How many calls the counter has handled, counting this one.
    async fn next(&self, ctx: Context) -> Result<u64>;
}

#[derive(Default)]
struct CounterImpl(AtomicU64);

impl Counter for CounterImpl {
    async fn next(&self, _ctx: Context) -> Result<u64> {
        Ok(self.0.fetch_add(1, Ordering::SeqCst) + 1)
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let supervisor = LocalSupervisor::new(ME);

    // The fence starts open. Anything `Fn() -> bool` is a fence.
    let owner = Arc::new(AtomicBool::new(true));
    let fence = {
        let owner = owner.clone();
        move || owner.load(Ordering::SeqCst)
    };

    // Host the actor. `spawn` requires a fence: a host with no way to be told it
    // lost the actor is not something the supervisor will run.
    supervisor
        .spawn::<CounterChannel, _, _>(
            COUNTER,
            ROOM,
            CounterService {
                inner: CounterImpl::default(),
            },
            fence,
        )
        .await?;
    assert_eq!(supervisor.status(COUNTER), Status::Running);

    // Call it. A transport onto the actor's mailbox becomes an ordinary generated
    // channel, so the caller cannot tell it from a remote one.
    let transport = supervisor
        .transport::<CounterChannel>(COUNTER, Context::default())
        .await?;
    let counter = CounterChannel::new(64, transport);
    counter.negotiate_version(u32::MAX).await?;
    assert_eq!(counter.next(Context::default()).await?, 1);
    assert_eq!(counter.next(Context::default()).await?, 2);
    println!("hosted and called: the counter is at 2");

    // Discovery, asked about this actor, names this node.
    assert_eq!(supervisor.discover(ActorRef(COUNTER)).await, Ok(vec![ME]));

    // The actor's epoch moves on: ownership passed to another host. The fence
    // closes, and the next request is refused without reaching the actor.
    owner.store(false, Ordering::SeqCst);
    let refused = counter.next(Context::default()).await.unwrap_err();
    assert_eq!(refused.code(), Some("FENCED"));
    println!("fence closed: the next call was answered FENCED");

    // Drain it. A handler that was running would be finished, not cancelled; here
    // there is none. The service is dropped and the mailbox stays, answering FENCED.
    supervisor.drain(COUNTER).await?;
    assert_eq!(supervisor.status(COUNTER), Status::Retired);
    assert_eq!(
        supervisor.discover(ActorRef(COUNTER)).await,
        Err(DiscoveryError::NotFound),
        "a retired actor is not where a caller should go"
    );
    println!("drained: the actor is retired and no longer discoverable here");
    Ok(())
}
