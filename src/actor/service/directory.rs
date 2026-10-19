//! **A sketch**: how a caller gets hold of an actor by id, without knowing where it
//! runs.
//!
//! Wiring `A` to `B` by hand means building `B`'s mailbox, spawning [`serve`] on it,
//! making a [`Session`] and handing that to `BChannel::new`. A [`Directory`] is that,
//! behind two calls:
//!
//! ```text
//! directory.spawn::<BChannel, _>(B, capacity, BService { inner })   // host it
//! let transport = directory.transport::<BChannel>(B, me).await?;    // reach it
//! let b = BChannel::new(64, transport);                              // then, as ever,
//! b.b(ctx).await                                                     // call it
//! ```
//!
//! What the caller holds is still an ordinary generated channel, so `ActorAImpl<B:
//! ActorB>` is unchanged and cannot tell a local actor from a remote one. The seam is
//! the **transport**, not the channel: generated channel types are per-service, so a
//! trait cannot return one for an arbitrary protocol, but every one of them is built
//! on a `ClientTransport<P>`, and that is what a directory can hand out. For a local
//! actor it is a [`Session`] on its mailbox; for a remote one it would be a lane over a
//! byte stream ([`Connection`](super::Connection)).
//!
//! # Not decided
//!
//! This is a sketch to argue with, and it is deliberately the smallest thing that
//! compiles. It does **not** settle:
//!
//! * **Placement across nodes.** [`LocalDirectory`] hosts every actor in one process.
//!   Who decides where an actor runs, and how a caller on another node finds out, is
//!   the open question — and the registry's answer to it needs the atomic update the
//!   ownership model assumes, which is what Raft is for here.
//! * **Ownership.** The ownership registry holds one actor's record. A directory
//!   needs one record, epoch floor and fence *per actor*, and nothing in this file
//!   fences anything: it hands each request to the service in mailbox order.
//! * **Identity.** `transport` is told who is calling. In a real deployment that
//!   comes from the connection and not from an argument; here there is no
//!   connection to take it from.
//! * **Teardown.** A channel built on a session's transport runs tasks of its own,
//!   and [`Session::closer`] is how they are let go. A boxed transport has lost its
//!   session, so there is no closer to keep. Dropping a [`LocalDirectory`] stops the
//!   actors' drains, which ends their requests but not the callers' tasks.
//!
//! The name is not `ActorSystem` because that is already the Verus model's state
//! struct ([`crate::actor::model`]).

use std::{
    any::{Any, TypeId},
    collections::HashMap,
    future::Future,
    sync::Mutex,
};

use jetstream::prelude::{
    jetstream_rpc::{
        client::ClientTransport,
        context::{Context, RemoteAddr},
        server::Server,
    },
    *,
};

use super::{Capacity, Delivery, Mailbox, Session, serve};

/// An actor's number. The model's `ActorId` is a `nat`; the executable steps and the
/// wire use `u64`.
pub type ActorId = u64;

/// Where an actor is hosted, as far as this directory knows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Placement {
    /// In this process.
    Local,
    /// On another node, reachable at this address.
    Remote(RemoteAddr),
}

/// Finds actors by id, and hosts them.
pub trait Directory: Send + Sync {
    /// Where `id` is hosted. An error if the directory has never heard of it.
    fn placement(&self, id: ActorId) -> impl Future<Output = Result<Placement>> + Send;

    /// Host `id` here: give it a mailbox of the given capacity, and serve `service`
    /// from the other end of it, one request at a time.
    ///
    /// `C` is the protocol callers' channels speak (`BChannel`) and `S` the one the
    /// service speaks (`BService<Impl>`): the same requests and responses, as for
    /// [`serve`]. An error if `id` is already hosted.
    fn spawn<C, S>(
        &self,
        id: ActorId,
        capacity: Capacity,
        service: S,
    ) -> impl Future<Output = Result<()>> + Send
    where
        C: Protocol<Error = Error> + 'static,
        S: Server<Request = C::Request, Response = C::Response> + 'static;

    /// A transport to `id`, calling as `from`. Wrap it in the service's channel:
    /// `BChannel::new(64, transport)`.
    ///
    /// An error if `id` is unknown, or hosts a service that does not speak `P`.
    fn transport<P>(
        &self,
        id: ActorId,
        from: Context,
    ) -> impl Future<Output = Result<Box<dyn ClientTransport<P>>>> + Send
    where
        P: Protocol<Error = Error> + 'static;
}

/// One hosted actor: its mailbox, whatever protocol that is, and the drain.
struct Slot {
    /// The protocol the mailbox speaks, so a caller asking for another is refused
    /// instead of mis-cast.
    protocol: TypeId,
    /// A `Mailbox<Delivery<C>>`.
    mailbox: Box<dyn Any + Send + Sync>,
    drain: tokio::task::JoinHandle<()>,
}

impl Drop for Slot {
    fn drop(&mut self) {
        self.drain.abort();
    }
}

/// Every actor in one process. The simplest thing that satisfies [`Directory`].
#[derive(Default)]
pub struct LocalDirectory {
    slots: Mutex<HashMap<ActorId, Slot>>,
}

impl LocalDirectory {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Directory for LocalDirectory {
    async fn placement(&self, id: ActorId) -> Result<Placement> {
        match self.slots.lock().expect("directory lock").contains_key(&id) {
            true => Ok(Placement::Local),
            false => Err(Error::new(format!("no actor {id}"))),
        }
    }

    async fn spawn<C, S>(&self, id: ActorId, capacity: Capacity, mut service: S) -> Result<()>
    where
        C: Protocol<Error = Error> + 'static,
        S: Server<Request = C::Request, Response = C::Response> + 'static,
    {
        let mut slots = self.slots.lock().expect("directory lock");
        if slots.contains_key(&id) {
            return Err(Error::new(format!("actor {id} is already hosted")));
        }
        let mailbox = Mailbox::<Delivery<C>>::new(capacity);
        let drain = tokio::spawn({
            let mailbox = mailbox.clone();
            async move { serve(mailbox, &mut service).await }
        });
        slots.insert(
            id,
            Slot {
                protocol: TypeId::of::<C>(),
                mailbox: Box::new(mailbox),
                drain,
            },
        );
        Ok(())
    }

    async fn transport<P>(&self, id: ActorId, from: Context) -> Result<Box<dyn ClientTransport<P>>>
    where
        P: Protocol<Error = Error> + 'static,
    {
        let slots = self.slots.lock().expect("directory lock");
        let slot = slots
            .get(&id)
            .ok_or_else(|| Error::new(format!("no actor {id}")))?;
        if slot.protocol != TypeId::of::<P>() {
            return Err(Error::new(format!(
                "actor {id} does not speak that protocol"
            )));
        }
        let mailbox = slot
            .mailbox
            .downcast_ref::<Mailbox<Delivery<P>>>()
            .expect("the protocol was checked")
            .clone();
        Ok(Box::new(Session::new(mailbox, from)))
    }
}
