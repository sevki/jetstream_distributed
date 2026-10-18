//! Calling an actor through its mailbox, without the caller knowing.
//!
//! `ActorA` calls `ActorB` as `self.b.b(ctx).await`, the way it would call any
//! implementation. In these tests the `B` it holds is a generated channel whose
//! transport is a [`Session`] on `B`'s mailbox, and `B`'s implementation is
//! served from the other end of that mailbox by [`serve`]. `ActorAImpl` is
//! generic over `B: ActorB` and cannot tell.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use jetstream_distributed::actor::service::{serve, Delivery, Mailbox, Session};
use jetstream::prelude::*;

use actorb_protocol::{ActorBChannel, ActorBService};

#[service]
pub trait ActorB {
    /// The `n`th call from `from`. Returns how many calls `B` has handled.
    async fn b(&self, ctx: Context, from: u64, n: u64) -> Result<u64>;
}

#[service]
pub trait ActorA {
    async fn a(&self, ctx: Context, from: u64, n: u64) -> Result<u64>;
}

/// `B`'s implementation. It checks the two things an actor promises.
#[derive(Clone, Default)]
struct ActorBImpl {
    /// Set while a call is being handled: another call arriving meanwhile means
    /// the actor was run twice at once.
    busy: Arc<AtomicBool>,
    /// The last `n` seen from each caller, and the total handled.
    seen: Arc<Mutex<(HashMap<u64, u64>, u64)>>,
}

impl ActorB for ActorBImpl {
    async fn b(&self, _ctx: Context, from: u64, n: u64) -> Result<u64> {
        assert!(
            !self.busy.swap(true, Ordering::SeqCst),
            "one thing at a time: a second call began before the first finished"
        );
        // Give a concurrent call every chance to overlap.
        tokio::task::yield_now().await;
        let total = {
            let mut seen = self.seen.lock().unwrap();
            let expected = seen.0.get(&from).map_or(0, |last| last + 1);
            assert_eq!(n, expected, "caller {from}: in the order sent, none skipped");
            seen.0.insert(from, n);
            seen.1 += 1;
            seen.1
        };
        self.busy.store(false, Ordering::SeqCst);
        Ok(total)
    }
}

/// `A` holds whatever `B` is. It knows only the trait.
struct ActorAImpl<B> {
    b: B,
}

impl<B: ActorB + Send + Sync> ActorA for ActorAImpl<B> {
    async fn a(&self, ctx: Context, from: u64, n: u64) -> Result<u64> {
        self.b.b(ctx, from, n).await
    }
}

/// `B` running behind a mailbox, and a way to get a channel to it.
struct Hosted {
    mailbox: Mailbox<Delivery<ActorBChannel>>,
    b: ActorBImpl,
}

fn host_b() -> Hosted {
    let mailbox = Mailbox::new();
    let b = ActorBImpl::default();
    let mut service = ActorBService { inner: b.clone() };
    let drain = mailbox.clone();
    tokio::spawn(async move { serve(drain, &mut service).await });
    Hosted { mailbox, b }
}

impl Hosted {
    /// A channel to `B` whose transport is a session on its mailbox.
    async fn channel(&self) -> ActorBChannel {
        let session = Session::new(self.mailbox.clone(), Context::default());
        let channel = ActorBChannel::new(64, Box::new(session));
        channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the actor speaks this version");
        channel
    }
}

#[tokio::test]
async fn a_calls_b_without_knowing_there_is_a_mailbox() {
    let hosted = host_b();
    let a = ActorAImpl {
        b: hosted.channel().await,
    };

    assert_eq!(a.a(Context::default(), 1, 0).await.unwrap(), 1);
    assert_eq!(a.a(Context::default(), 1, 1).await.unwrap(), 2);
    assert_eq!(hosted.b.seen.lock().unwrap().1, 2);
}

/// A `B` that never answers.
#[derive(Clone, Default)]
struct StuckB;

impl ActorB for StuckB {
    async fn b(&self, _ctx: Context, _from: u64, _n: u64) -> Result<u64> {
        std::future::pending().await
    }
}

/// A request in flight when the drain is aborted is answered with an error rather
/// than left pending — and only that request. The ones behind it are served by the
/// drain that replaces it, and the same channel goes on working afterwards.
///
/// The last half is the point of answering with a *tagged response*. An error put
/// on the reply stream instead would read as the lane having failed: every call
/// outstanding would fail with it, and calls made later would never be answered.
#[tokio::test]
async fn aborting_the_drain_mid_request_answers_only_that_request() {
    const WAIT: std::time::Duration = std::time::Duration::from_secs(5);
    let mailbox: Mailbox<Delivery<ActorBChannel>> = Mailbox::new();
    let mut stuck = ActorBService { inner: StuckB };
    let drain = tokio::spawn({
        let mailbox = mailbox.clone();
        async move { serve(mailbox, &mut stuck).await }
    });

    let session = Session::new(mailbox.clone(), Context::default());
    let channel = Arc::new(ActorBChannel::new(64, Box::new(session)));
    channel
        .negotiate_version(u32::MAX)
        .await
        .expect("the actor speaks this version");

    // The first request reaches the handler, which never returns; the second is
    // queued behind it, in the same round or the next.
    let first = tokio::spawn({
        let channel = channel.clone();
        async move { channel.b(Context::default(), 1, 0).await }
    });
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    let second = tokio::spawn({
        let channel = channel.clone();
        async move { channel.b(Context::default(), 1, 1).await }
    });
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    drain.abort();

    let answer = tokio::time::timeout(WAIT, first)
        .await
        .expect("the abandoned request was answered, not left pending")
        .unwrap();
    assert!(answer.is_err(), "and the answer says it was not served");

    // A drain that works takes over the same mailbox.
    let b = ActorBImpl::default();
    // The handler checks callers arrive in the order sent from 0, so the one that
    // was abandoned is the one that was never handled: tell it so.
    b.seen.lock().unwrap().0.insert(1, 0);
    let mut service = ActorBService { inner: b.clone() };
    tokio::spawn({
        let mailbox = mailbox.clone();
        async move { serve(mailbox, &mut service).await }
    });

    tokio::time::timeout(WAIT, second)
        .await
        .expect("the request behind it was served by the new drain")
        .unwrap()
        .expect("and succeeded");
    // And the channel the abandoned call went down is still a working channel.
    tokio::time::timeout(WAIT, channel.b(Context::default(), 1, 2))
        .await
        .expect("a later call on the same channel is answered")
        .expect("and succeeds");
}

/// The same `A`, over the implementation itself: no mailbox, no channel. The
/// caller's code is identical, which is the point.
#[tokio::test]
async fn the_same_a_over_the_implementation() {
    let a = ActorAImpl {
        b: ActorBImpl::default(),
    };
    assert_eq!(a.a(Context::default(), 1, 0).await.unwrap(), 1);
}

/// Many callers at once, each calling in order. `B` is run one call at a time,
/// and each caller's calls arrive in the order it made them.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn many_callers_one_actor() {
    const CALLERS: u64 = 6;
    const EACH: u64 = 100;
    let hosted = host_b();

    let mut callers = Vec::new();
    for from in 0..CALLERS {
        let a = ActorAImpl {
            b: hosted.channel().await,
        };
        callers.push(tokio::spawn(async move {
            for n in 0..EACH {
                a.a(Context::default(), from, n).await.unwrap();
            }
        }));
    }
    for caller in callers {
        tokio::time::timeout(std::time::Duration::from_secs(20), caller)
            .await
            .expect("every call was answered")
            .unwrap();
    }
    assert_eq!(hosted.b.seen.lock().unwrap().1, CALLERS * EACH);
}
