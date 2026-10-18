//! Two actors, each behind its own mailbox.
//!
//! `ActorAImpl` calls `ActorB` as `self.b.b(ctx).await`. The `B` it holds is a
//! generated channel whose transport is a [`Session`] on `B`'s mailbox, and `B`'s
//! implementation is served from the other end by [`serve`], one request at a
//! time. `ActorAImpl` is generic over `B: ActorB` and cannot tell. `main` reaches
//! `A` the same way, through `A`'s mailbox.

use jetstream::prelude::*;
use jetstream_distributed::actor::service::{Delivery, Mailbox, Session, serve};

use actora_protocol::{ActorAChannel, ActorAService};
use actorb_protocol::{ActorBChannel, ActorBService};

#[service]
trait ActorA {
    async fn a(&self, ctx: Context) -> Result<()>;
}

#[service]
trait ActorB {
    async fn b(&self, ctx: Context) -> Result<()>;
}

struct ActorAImpl<B> {
    b: B,
}

impl<B> ActorA for ActorAImpl<B>
where
    B: ActorB + Send + Sync,
{
    async fn a(&self, ctx: Context) -> Result<()> {
        eprintln!("A: calling B");
        self.b.b(ctx).await?;
        eprintln!("A: B answered");
        Ok(())
    }
}

struct ActorBImpl;

impl ActorB for ActorBImpl {
    async fn b(&self, _ctx: Context) -> Result<()> {
        eprintln!("B: handling a call");
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // B, behind its mailbox.
    let b_mailbox = Mailbox::<Delivery<ActorBChannel>>::new();
    let mut b = ActorBService { inner: ActorBImpl };
    tokio::spawn({
        let mailbox = b_mailbox.clone();
        async move { serve(mailbox, &mut b).await }
    });
    let b_channel = ActorBChannel::new(64, Box::new(Session::new(b_mailbox, Context::default())));
    b_channel.negotiate_version(u32::MAX).await?;

    // A, holding a channel to B, behind its own mailbox.
    let a_mailbox = Mailbox::<Delivery<ActorAChannel>>::new();
    let mut a = ActorAService {
        inner: ActorAImpl { b: b_channel },
    };
    tokio::spawn({
        let mailbox = a_mailbox.clone();
        async move { serve(mailbox, &mut a).await }
    });
    let a_channel = ActorAChannel::new(64, Box::new(Session::new(a_mailbox, Context::default())));
    a_channel.negotiate_version(u32::MAX).await?;

    for _ in 0..2 {
        a_channel.a(Context::default()).await?;
    }
    Ok(())
}
