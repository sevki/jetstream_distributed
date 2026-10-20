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
//! # Draining
//!
//! [`Supervisor::drain`] is the cooperative way for a host to stop being an actor's
//! host, as the handover needs: **fence first, let the running handler finish, then
//! let go.**
//!
//! 1. The actor's own fence is closed, so it starts no further request. Anything
//!    queued, and anything that arrives, is answered `FENCED`.
//! 2. A handler already running is **not** interrupted. `drain` returns after it
//!    has finished. (A handover that cannot wait — the owner is gone — is not a
//!    drain; the fence at the point where the effect lands is what keeps a stale
//!    host's effect from being authoritative.)
//! 3. The service is dropped, releasing whatever the actor held. The status is
//!    [`Status::Retired`].
//!
//! The mailbox is **kept**. A [`Session`] made before the drain holds it, and with
//! no drain behind it a request it queued would wait for good; so a small task
//! stays on it and answers every request `FENCED` ([`refuse_all`]), which is also
//! what a caller needs to hear: ask where the actor lives now. If the actor comes
//! back to this host, [`Supervisor::spawn`] takes the same mailbox over, and those
//! sessions work again.
//!
//! A request that ran but whose reply was lost is retried at the new owner, so
//! delivery is at-least-once; nothing here prevents that. **Tested, not proved.**
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
//! * **Who calls `drain`.** [`Supervisor::drain`] is the mechanism. Nothing here
//!   decides *when*: a handover that notices the epoch has moved and drains the
//!   actor on its old host is a composition with the ownership layer.
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
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
    },
};

use jetstream::prelude::{
    jetstream_rpc::{client::ClientTransport, context::Context, server::Server},
    *,
};
use tokio::sync::{Notify, watch};

use super::{Capacity, Delivery, Fence, Mailbox, Session, refuse_all, serve_until};
use crate::id::Id;
use crate::scheduling::{
    Resource,
    discovery::{Discovery, DiscoveryError},
};

/// An actor, as a [`Resource`] to ask [`Discovery`] about.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorRef(pub Id);

impl Resource for ActorRef {}

/// Whether an actor is running on this node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// Hosted here, and its drain is running.
    Running,
    /// [`Supervisor::drain`] has been asked for, and a handler that was already
    /// running has not finished. It starts no new request: they are answered
    /// `FENCED`.
    Draining,
    /// Drained. The service has been dropped; the mailbox is kept, and every request
    /// that reaches it is answered `FENCED`. A new [`Supervisor::transport`] is
    /// refused. [`Supervisor::spawn`] hosts the id again, on the same mailbox.
    Retired,
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
    fn status(&self, id: Id) -> Status;

    /// Host `id` here: give it a mailbox of the given capacity, and serve `service`
    /// from the other end of it, one request at a time, each one only if `fence`
    /// still lets this host serve ([`serve_fenced`](super::serve_fenced)).
    ///
    /// `C` is the protocol callers' channels speak (`BChannel`) and `S` the one the
    /// service speaks (`BService<Impl>`): the same requests and responses, as for
    /// [`serve`](super::serve). An error if `id` is [`Status::Running`] or
    /// [`Status::Draining`]. A [`Status::Stopped`] or [`Status::Retired`] one is
    /// replaced: a stopped one is how an actor whose handler panicked is restarted,
    /// and a retired one is how an actor comes back to a host it was drained from.
    /// If it speaks the same protocol the new drain takes over the **same mailbox**
    /// (and `capacity` is ignored), so sessions obtained before, and the requests
    /// queued behind a panic, are served, not stranded. A different protocol gets a
    /// fresh mailbox, and the old one is not served.
    fn spawn<C, S, F>(
        &self,
        id: Id,
        capacity: Capacity,
        service: S,
        fence: F,
    ) -> impl Future<Output = Result<()>> + Send
    where
        C: Protocol<Error = Error> + 'static,
        S: Server<Request = C::Request, Response = C::Response> + 'static,
        F: Fence + 'static;

    /// Stop `id` being served here, cooperatively: close its fence, wait for a
    /// handler that is running to finish, drop the service, and leave a responder on
    /// the mailbox that answers every request `FENCED` ([`Status::Retired`]).
    ///
    /// Returns when the actor is retired, so a caller that goes on to hand the actor
    /// to another host knows nothing is still running here. Draining a retired actor
    /// returns at once. An error if `id` is not hosted, or if its drain ended — the
    /// handler panicked — before it retired: there is nothing left to drain, and
    /// nothing answering `FENCED` either, so the actor is [`Status::Stopped`].
    fn drain(&self, id: Id) -> impl Future<Output = Result<()>> + Send;

    /// A transport to `id` on this node, calling as `from`. Wrap it in the service's
    /// channel: `BChannel::new(64, transport)`.
    ///
    /// An error if `id` is not [`Status::Running`] here, or hosts a service that
    /// does not speak `P`.
    fn transport<P>(
        &self,
        id: Id,
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
    /// Set by [`Supervisor::drain`], and read by the actor's fence: from then on it
    /// starts no request.
    retiring: Arc<AtomicBool>,
    /// Wakes the drain task to retire when it is next idle.
    retire: Arc<Notify>,
    /// `true` once the task has dropped the service. If the task ends without
    /// sending it, the sender is dropped and a waiter sees that.
    released: watch::Receiver<bool>,
}

impl Slot {
    /// Whether the drain task is still running. It ends only if the service's
    /// handler panicked (or the runtime is shutting down): the task loops for as
    /// long as the mailbox is held, and the slot holds it. A retired actor's task
    /// is still running; it is the one answering `FENCED`.
    fn running(&self) -> bool {
        !self.drain.is_finished()
    }

    fn status(&self) -> Status {
        if !self.running() {
            Status::Stopped
        } else if *self.released.borrow() {
            Status::Retired
        } else if self.retiring.load(Ordering::SeqCst) {
            Status::Draining
        } else {
            Status::Running
        }
    }
}

/// The caller's fence, and the supervisor's own: a drained actor serves nothing,
/// whatever the caller's fence says.
struct Retiring<F> {
    inner: F,
    retiring: Arc<AtomicBool>,
}

impl<F: Fence> Fence for Retiring<F> {
    fn may_serve(&self) -> bool {
        !self.retiring.load(Ordering::SeqCst) && self.inner.may_serve()
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
    me: Id,
    slots: Mutex<HashMap<Id, Slot>>,
}

impl LocalSupervisor {
    /// A supervisor for the node `me`, with nothing hosted.
    pub fn new(me: Id) -> Self {
        Self {
            me,
            slots: Mutex::new(HashMap::new()),
        }
    }

    /// The node this supervisor runs on.
    pub fn host(&self) -> Id {
        self.me
    }
}

/// What this supervisor knows about where an actor is: itself, if it is running one.
/// It has no view of any other node, so an actor it does not host is `NotFound`,
/// which is "not here" and not "nowhere".
impl Discovery for LocalSupervisor {
    fn discover<W: Resource>(&self, what: W) -> std::result::Result<Vec<Id>, DiscoveryError> {
        let Some(ActorRef(id)) = (&what as &dyn Any).downcast_ref::<ActorRef>() else {
            return Err(DiscoveryError::NotFound);
        };
        match self.status(*id) {
            Status::Running => Ok(vec![self.me]),
            // A draining actor starts nothing, and a retired one answers `FENCED`:
            // neither is where a caller should go.
            Status::Draining | Status::Retired | Status::Stopped | Status::Absent => {
                Err(DiscoveryError::NotFound)
            }
        }
    }
}

impl Supervisor for LocalSupervisor {
    fn status(&self, id: Id) -> Status {
        match self.slots.lock().expect("supervisor lock").get(&id) {
            Some(slot) => slot.status(),
            None => Status::Absent,
        }
    }

    async fn drain(&self, id: Id) -> Result<()> {
        let (retiring, retire, mut released) = {
            let slots = self.slots.lock().expect("supervisor lock");
            let slot = slots
                .get(&id)
                .ok_or_else(|| Error::new(format!("no actor {id}")))?;
            (
                slot.retiring.clone(),
                slot.retire.clone(),
                slot.released.clone(),
            )
        };
        // The fence first, so that nothing starts from here on; then the signal,
        // which a task that is busy keeps (a stored permit) until it is next idle.
        retiring.store(true, Ordering::SeqCst);
        retire.notify_one();
        match released.wait_for(|released| *released).await {
            Ok(_) => Ok(()),
            // The task ended without releasing the service: its handler panicked.
            Err(_) => Err(Error::new(format!(
                "actor {id} stopped before it could be drained"
            ))),
        }
    }

    async fn spawn<C, S, F>(
        &self,
        id: Id,
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
        // Only an actor that is not being served is replaced: one whose drain has
        // ended (a panic restarts it) or that was drained (it comes back).
        match slots.get(&id).map(Slot::status) {
            Some(Status::Running | Status::Draining) => {
                return Err(Error::new(format!("actor {id} is already hosted")));
            }
            Some(Status::Retired | Status::Stopped) | None => {}
            Some(Status::Absent) => unreachable!("a slot is never absent"),
        }
        // Sessions made before hold this mailbox, `Round::drop` put the requests
        // behind a panic back on it, and a retired actor's callers are still
        // being answered `FENCED` from it. A new mailbox would strand them all.
        let reused = slots
            .get(&id)
            .filter(|old| old.protocol == TypeId::of::<C>())
            .and_then(|old| old.mailbox.downcast_ref::<Mailbox<Delivery<C>>>())
            .cloned();
        let mailbox = reused.unwrap_or_else(|| Mailbox::<Delivery<C>>::new(capacity));
        // The old slot goes first, and with it its task (the `FENCED` responder of a
        // retired actor, or one that has already ended), so that the new drain is not
        // started beside it. The abort lands the next time that task is polled; a
        // request it answers in that instant is refused `FENCED` and retried, which is
        // the safe way to be wrong.
        drop(slots.remove(&id));
        let retiring = Arc::new(AtomicBool::new(false));
        let retire = Arc::new(Notify::new());
        let (released_tx, released) = watch::channel(false);
        let drain = tokio::spawn({
            let mailbox = mailbox.clone();
            let fence = Retiring {
                inner: fence,
                retiring: retiring.clone(),
            };
            let retire = retire.clone();
            async move {
                serve_until(mailbox.clone(), &mut service, &fence, retire.notified()).await;
                // Idle, and told to stop: nothing is running, so the service can go.
                drop(service);
                let _ = released_tx.send(true);
                // What is left of the actor answers anyone who still comes.
                refuse_all(mailbox).await
            }
        });
        slots.insert(
            id,
            Slot {
                protocol: TypeId::of::<C>(),
                mailbox: Box::new(mailbox),
                drain,
                retiring,
                retire,
                released,
            },
        );
        Ok(())
    }

    async fn transport<P>(&self, id: Id, from: Context) -> Result<Box<dyn ClientTransport<P>>>
    where
        P: Protocol<Error = Error> + 'static,
    {
        let slots = self.slots.lock().expect("supervisor lock");
        let slot = slots
            .get(&id)
            .ok_or_else(|| Error::new(format!("no actor {id}")))?;
        match slot.status() {
            Status::Running => {}
            // A new session would only be told `FENCED`: send the caller to ask
            // where the actor lives instead.
            Status::Draining | Status::Retired => {
                return Err(Error::new(format!("actor {id} is not served here")));
            }
            // A new session would queue behind a drain that is gone.
            Status::Stopped => return Err(Error::new(format!("actor {id} has stopped"))),
            Status::Absent => unreachable!("a slot is never absent"),
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
