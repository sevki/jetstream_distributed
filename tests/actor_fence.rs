//! The ownership fence in front of a request: `serve_fenced` asks it before it
//! gives each request to the service.
//!
//! This is tested, not proved: the fence itself is the proved part, and what is
//! checked here is that the drain asks it first, every time.

use std::num::NonZeroU32;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use jetstream::prelude::*;
use jetstream_distributed::actor::service::{Capacity, Delivery, Mailbox, Session, serve_fenced};

use actorb_protocol::{ActorBChannel, ActorBService};

const ROOM: Capacity = Capacity::Bounded(NonZeroU32::new(16).unwrap());

#[service]
trait ActorB {
    /// Returns how many calls `B` has handled, counting this one.
    async fn b(&self, ctx: Context) -> Result<u64>;
}

struct Counting(Arc<AtomicU64>);

impl ActorB for Counting {
    async fn b(&self, _ctx: Context) -> Result<u64> {
        Ok(self.0.fetch_add(1, Ordering::SeqCst) + 1)
    }
}

/// While the fence says no, a request is answered `FENCED` and the handler never
/// runs; the drain survives, and serves again once the fence says yes. A drain
/// that did not ask would count every call.
#[tokio::test]
async fn a_request_the_fence_refuses_is_answered_fenced_and_never_handled() {
    let handled = Arc::new(AtomicU64::new(0));
    let owner = Arc::new(AtomicBool::new(true));

    let mailbox = Mailbox::<Delivery<ActorBChannel>>::new(ROOM);
    tokio::spawn({
        let mailbox = mailbox.clone();
        let handled = handled.clone();
        let owner = owner.clone();
        async move {
            let mut service = ActorBService {
                inner: Counting(handled),
            };
            serve_fenced(mailbox, &mut service, &move || owner.load(Ordering::SeqCst)).await
        }
    });
    let channel = ActorBChannel::new(
        64,
        Box::new(Session::new(mailbox, Context::default())),
    );
    channel.negotiate_version(u32::MAX).await.unwrap();

    assert_eq!(channel.b(Context::default()).await.unwrap(), 1);

    // The epoch moves on: this host is no longer the owner.
    owner.store(false, Ordering::SeqCst);
    let refused = channel.b(Context::default()).await.unwrap_err();
    assert_eq!(refused.code(), Some("FENCED"));
    assert_eq!(handled.load(Ordering::SeqCst), 1, "the handler did not run");

    // The drain is still there, and asks again.
    owner.store(true, Ordering::SeqCst);
    assert_eq!(channel.b(Context::default()).await.unwrap(), 2);
}
