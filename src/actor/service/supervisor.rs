//! **A sketch**: what runs on this node, and how a caller reaches it.
//!
//! Wiring `A` to `B` by hand means building `B`'s mailbox, spawning [`serve_fenced`]
//! on it, making a [`Session`] and handing that to `BChannel::new`. A [`Supervisor`]
//! is that, behind two calls:
//!
//! ```text
//! supervisor.spawn::<BChannel, _, _>(B, capacity, BService { inner }, fence).await?; // host it
//! let transport = supervisor.transport::<BChannel>(B, me).await?;                  // reach it
//! let b = BChannel::new(64, transport);                                            // then, as ever,
//! b.b(ctx).await                                                                   // call it
//! ```
//!
//! What the caller holds is still an ordinary generated channel, so `ActorAImpl<B:
//! ActorB>` is unchanged and cannot tell a local actor from a remote one. The seam is
//! the **transport**, not the channel: generated channel types are per-service, so a
//! trait cannot return one for an arbitrary protocol, but every one of them is built
//! on a `ClientTransport<P>`, and that is what a supervisor can hand out. For a local
//! actor it is a [`Session`] on its mailbox; for a remote one it would be a lane over a
//! byte stream ([`Connection`](super::Connection)).
//!
//! # Two questions, two traits
//!
//! * **What runs here** is the [`Supervisor`]'s: it owns the actors this node hosts,
//!   their mailboxes and their drains. It says nothing about actors anywhere else.
//! * **Where an actor lives** is [`Discovery`](crate::scheduling::discovery::Discovery)'s,
//!   the trait the scheduler already uses, asked about an [`ActorRef`]. A
//!   [`LocalSupervisor`] answers it for the actors it hosts; an answer for the rest of
//!   the cluster would come from the ownership registry's record.
//!
//! The supervisor never decides who may host an actor. [`Supervisor::spawn`] is
//! **given** the [`Fence`] the ownership layer's grant yields, and every request goes
//! through it ([`serve_fenced`]): a supervisor that could host an actor without one
//! would be a way around the ownership protocol. Discovery may be stale, and nothing
//! depends on its being right: a request that reaches a host that no longer owns the
//! actor is answered `FENCED`. A caller is then expected to ask Discovery again and
//! retry; nothing in this file does that, and it is the composition described under
//! *Not decided*.
//!
//! # Not decided
//!
//! This is a sketch to argue with, and it is deliberately the smallest thing that
//! compiles. It does **not** settle:
//!
//! * **Reaching an actor on another node.** Nothing here makes a lane to a remote
//!   host. The composition that asks Discovery, then hands out a [`Session`] for a
//!   local actor or a [`Connection`](super::Connection) lane for a remote one, is the
//!   next piece, and it needs the roster keyed by `RemoteAddr` (#35).
//! * **Draining.** [`Supervisor::status`] says an actor has stopped and
//!   [`Supervisor::spawn`] replaces a stopped one, which is how it is restarted. A
//!   cooperative handover that lets the running handler finish and then removes the
//!   slot is not here yet.
//! * **Ownership of the fence's inputs.** The caller builds the fence; nothing here
//!   ties it to a registry, a host or an epoch.
//! * **Identity.** `transport` is told who is calling. In a real deployment that
//!   comes from the connection and not from an argument; here there is no
//!   connection to take it from.
//! * **Teardown.** A channel built on a session's transport runs tasks of its own,
//!   and [`Session::closer`] is how they are let go. A boxed transport has lost its
//!   session, so there is no closer to keep. Dropping a [`LocalSupervisor`] stops the
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
    jetstream_rpc::{client::ClientTransport, context::Context, server::Server},
    *,
};

use super::{Capacity, Delivery, Fence, Mailbox, Session, serve_fenced};
use crate::host::HostId;
use crate::scheduling::{
    Resource,
    discovery::{Discovery, DiscoveryError},
};

/// An actor's number. The model's `ActorId` is a `nat`; the executable steps and the
/// wire use `u64`.
pub type ActorId = u64;

/// An actor, as a [`Resource`] to ask [`Discovery`] about.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorRef(pub ActorId);

impl Resource for ActorRef {}

/// Whether an actor is running on this node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// Hosted here, and its drain is running.
    Running,
    /// Was hosted here, and its drain has ended: its handler panicked. A new
    /// [`Supervisor::transport`] is refused. A session obtained earlier still holds
    /// the mailbox and can queue requests, and the ones already queued stay there;
    /// they wait for [`Supervisor::spawn`] to host the id again, which serves them
    /// from the same mailbox.
    Stopped,
    /// Never hosted here.
    Absent,
}

/// Owns the actors that run on this node.
pub trait Supervisor: Send + Sync {
    /// Whether `id` is running here.
    fn status(&self, id: ActorId) -> Status;

    /// Host `id` here: give it a mailbox of the given capacity, and serve `service`
    /// from the other end of it, one request at a time, each one only if `fence`
    /// still lets this host serve ([`serve_fenced`]).
    ///
    /// `C` is the protocol callers' channels speak (`BChannel`) and `S` the one the
    /// service speaks (`BService<Impl>`): the same requests and responses, as for
    /// [`serve`](super::serve). An error if `id` is already [`Status::Running`]; a
    /// [`Status::Stopped`] one is replaced, which is how an actor whose handler
    /// panicked is restarted: if it speaks the same protocol the new drain takes over
    /// the **same mailbox** (and `capacity` is ignored), so sessions obtained before
    /// the stop and the requests queued behind the panic are served, not stranded.
    /// A different protocol gets a fresh mailbox, and the old one is not served.
    fn spawn<C, S, F>(
        &self,
        id: ActorId,
        capacity: Capacity,
        service: S,
        fence: F,
    ) -> impl Future<Output = Result<()>> + Send
    where
        C: Protocol<Error = Error> + 'static,
        S: Server<Request = C::Request, Response = C::Response> + 'static,
        F: Fence + 'static;

    /// A transport to `id` on this node, calling as `from`. Wrap it in the service's
    /// channel: `BChannel::new(64, transport)`.
    ///
    /// An error if `id` is not [`Status::Running`] here, or hosts a service that
    /// does not speak `P`.
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

impl Slot {
    /// Whether the drain is still running. It ends only if the service's handler
    /// panicked (or the runtime is shutting down): `serve_fenced` loops for as long
    /// as the mailbox is held, and the slot holds it.
    fn running(&self) -> bool {
        !self.drain.is_finished()
    }
}

impl Drop for Slot {
    fn drop(&mut self) {
        self.drain.abort();
    }
}

/// Every actor on one node, in one process. The simplest thing that satisfies
/// [`Supervisor`].
pub struct LocalSupervisor {
    me: HostId,
    slots: Mutex<HashMap<ActorId, Slot>>,
}

impl LocalSupervisor {
    /// A supervisor for the node `me`, with nothing hosted.
    pub fn new(me: HostId) -> Self {
        Self {
            me,
            slots: Mutex::new(HashMap::new()),
        }
    }

    /// The node this supervisor runs on.
    pub fn host(&self) -> HostId {
        self.me
    }
}

/// What this supervisor knows about where an actor is: itself, if it is running one.
/// It has no view of any other node, so an actor it does not host is `NotFound`,
/// which is "not here" and not "nowhere".
impl Discovery for LocalSupervisor {
    fn discover<W: Resource>(&self, what: W) -> std::result::Result<Vec<HostId>, DiscoveryError> {
        let Some(ActorRef(id)) = (&what as &dyn Any).downcast_ref::<ActorRef>() else {
            return Err(DiscoveryError::NotFound);
        };
        match self.status(*id) {
            Status::Running => Ok(vec![self.me]),
            Status::Stopped | Status::Absent => Err(DiscoveryError::NotFound),
        }
    }
}

impl Supervisor for LocalSupervisor {
    fn status(&self, id: ActorId) -> Status {
        match self.slots.lock().expect("supervisor lock").get(&id) {
            Some(slot) if slot.running() => Status::Running,
            Some(_) => Status::Stopped,
            None => Status::Absent,
        }
    }

    async fn spawn<C, S, F>(
        &self,
        id: ActorId,
        capacity: Capacity,
        mut service: S,
        fence: F,
    ) -> Result<()>
    where
        C: Protocol<Error = Error> + 'static,
        S: Server<Request = C::Request, Response = C::Response> + 'static,
        F: Fence + 'static,
    {
        let mut slots = self.slots.lock().expect("supervisor lock");
        // A slot whose drain has ended is not hosting anything: replacing it is how
        // an actor whose handler panicked is restarted.
        if slots.get(&id).is_some_and(Slot::running) {
            return Err(Error::new(format!("actor {id} is already hosted")));
        }
        // Sessions made before a stop hold this mailbox, and `Round::drop` put the
        // requests behind the panic back on it. A new mailbox would strand both.
        let reused = slots
            .get(&id)
            .filter(|old| old.protocol == TypeId::of::<C>())
            .and_then(|old| old.mailbox.downcast_ref::<Mailbox<Delivery<C>>>())
            .cloned();
        let mailbox = reused.unwrap_or_else(|| Mailbox::<Delivery<C>>::new(capacity));
        let drain = tokio::spawn({
            let mailbox = mailbox.clone();
            async move { serve_fenced(mailbox, &mut service, &fence).await }
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
        let slots = self.slots.lock().expect("supervisor lock");
        let slot = slots
            .get(&id)
            .ok_or_else(|| Error::new(format!("no actor {id}")))?;
        if !slot.running() {
            // A new session would queue behind a drain that is gone.
            return Err(Error::new(format!("actor {id} has stopped")));
        }
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
