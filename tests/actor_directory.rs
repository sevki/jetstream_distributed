//! The directory sketch: actors found by id, and called as if they were values.
//!
//! `ActorAImpl<B: ActorB>` is the same generic caller as in `actor_mailbox.rs`. What
//! changes is where its `B` comes from: not a mailbox the test built, but a transport
//! the directory handed out for an actor id.

use std::num::NonZeroU32;

use jetstream::prelude::*;
use jetstream_distributed::actor::service::{
    ActorId, Capacity, Directory, LocalDirectory, Placement,
};

use actora_protocol::{ActorAChannel, ActorAService};
use actorb_protocol::{ActorBChannel, ActorBService};

const ROOM: Capacity = Capacity::Bounded(NonZeroU32::new(16).unwrap());

const A: ActorId = 1;
const B: ActorId = 2;

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

/// Host a fresh `B` as actor `B`.
async fn host_b(directory: &LocalDirectory) -> Result<()> {
    directory
        .spawn::<ActorBChannel, _>(
            B,
            ROOM,
            ActorBService {
                inner: ActorBImpl::default(),
            },
        )
        .await
}

/// A channel to the actor `id`, which speaks `B`'s protocol.
async fn channel_to_b(directory: &LocalDirectory, id: ActorId) -> Result<ActorBChannel> {
    let transport = directory
        .transport::<ActorBChannel>(id, Context::default())
        .await?;
    let channel = ActorBChannel::new(64, transport);
    channel.negotiate_version(u32::MAX).await?;
    Ok(channel)
}

/// `A` is hosted, `B` is hosted, `A` is handed a channel to `B` by the directory, and
/// a caller reaches `A` through the directory too. Nothing in `ActorAImpl` mentions a
/// mailbox, a session or a directory.
#[tokio::test]
async fn actors_find_each_other_by_id() {
    let directory = LocalDirectory::new();

    directory
        .spawn::<ActorBChannel, _>(
            B,
            ROOM,
            ActorBService {
                inner: ActorBImpl::default(),
            },
        )
        .await
        .unwrap();
    let a = ActorAImpl {
        b: channel_to_b(&directory, B).await.unwrap(),
    };
    directory
        .spawn::<ActorAChannel, _>(A, ROOM, ActorAService { inner: a })
        .await
        .unwrap();

    assert_eq!(directory.placement(A).await.unwrap(), Placement::Local);
    assert_eq!(directory.placement(B).await.unwrap(), Placement::Local);

    let transport = directory
        .transport::<ActorAChannel>(A, Context::default())
        .await
        .unwrap();
    let a = ActorAChannel::new(64, transport);
    a.negotiate_version(u32::MAX).await.unwrap();

    assert_eq!(a.a(Context::default()).await.unwrap(), 1);
    assert_eq!(a.a(Context::default()).await.unwrap(), 2);
}

/// What the directory refuses: an id it has never heard of, hosting one twice, and
/// asking an actor for a protocol it does not speak.
#[tokio::test]
async fn the_directory_refuses_what_it_cannot_do() {
    let directory = LocalDirectory::new();

    assert!(directory.placement(B).await.is_err(), "nobody is hosted yet");
    assert!(
        directory
            .transport::<ActorBChannel>(B, Context::default())
            .await
            .is_err(),
        "and there is nothing to reach"
    );

    host_b(&directory).await.unwrap();
    assert!(host_b(&directory).await.is_err(), "an id is hosted once");

    assert!(
        directory
            .transport::<ActorAChannel>(B, Context::default())
            .await
            .is_err(),
        "B does not speak A's protocol, and is not mis-cast as if it did"
    );
}
