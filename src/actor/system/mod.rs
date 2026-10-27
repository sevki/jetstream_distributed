#![cfg(feature = "service")]
//! An actor system: how a caller reaches an actor, wherever it is.
//!
//! Three things already exist and this puts them in order:
//!
//! * a [`Supervisor`] says what runs **here**, and hands out a transport onto a
//!   local actor's mailbox;
//! * a [`Discovery`] says where an actor **lives**, as locations;
//! * a [`Placement`] decides which host should run something new.
//!
//! What a system adds is [`connect`](ActorSystem::connect), and the order it asks
//! in: the supervisor first, because a local actor needs no network and no
//! lookup, and only if the actor is not running here, discovery and then a dial.
//! A system implements the accessors and [`dial`](ActorSystem::dial), which is the
//! one transport-specific part; the order is not theirs to re-decide.
//!
//! What comes back is a `Box<dyn ClientTransport<P>>`, the same thing
//! [`Supervisor::transport`] returns, so a caller builds an ordinary generated
//! channel on it and cannot tell a local actor from a remote one.
//!
//! Discovery may be stale, and nothing here depends on its being right: a request
//! that reaches a host that no longer owns the actor is answered `FENCED`. Asking
//! again and retrying is the caller's, and is not implemented here.

use std::future::Future;

use jetstream::prelude::*;

use crate::actor::service::{ActorRef, Status, Supervisor};
use crate::scheduling::{discovery::Discovery, placement::Placement};

/// A supervisor, a discovery and a placement, and a way to dial a location.
pub trait ActorSystem: Sync + Send {
    /// What runs here.
    type Supervisor: Supervisor;
    /// Where an actor lives.
    type Discovery: Discovery<Resource = ActorRef> + Sync;
    /// Which host should run something new.
    type Placement: Placement;

    /// What runs on this node.
    fn supervisor(&self) -> &Self::Supervisor;

    /// Where actors live.
    fn discovery(&self) -> &Self::Discovery;

    /// Where new things go.
    fn placement(&mut self) -> &mut Self::Placement;

    /// A transport to the actor at `location`, which is something
    /// [`discovery`](Self::discovery) returned.
    fn dial<P>(
        &mut self,
        location: <Self::Discovery as Discovery>::Location,
        from: Context,
    ) -> impl Future<Output = Result<Box<dyn ClientTransport<P>>>> + Send
    where
        P: Protocol<Error = Error> + 'static;

    /// A transport to `actor`: onto its mailbox if it is running here, otherwise
    /// to the first location discovery gives for it.
    ///
    /// An error if it is neither running here nor discoverable, or if the dial
    /// fails.
    fn connect<P>(
        &mut self,
        actor: ActorRef,
        from: Context,
    ) -> impl Future<Output = Result<Box<dyn ClientTransport<P>>>> + Send
    where
        P: Protocol<Error = Error> + 'static,
    {
        async move {
            if self.supervisor().status(actor.0) == Status::Running {
                return self.supervisor().transport::<P>(actor.0, from).await;
            }
            let location = self
                .discovery()
                .discover(actor)
                .await
                .map_err(|why| Error::new(format!("actor {}: {why}", actor.0)))?
                .into_iter()
                .next()
                .ok_or_else(|| Error::new(format!("actor {} is nowhere", actor.0)))?;
            self.dial::<P>(location, from).await
        }
    }
}

mod iroh;
pub mod quic;
