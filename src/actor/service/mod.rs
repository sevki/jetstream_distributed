//! A distributed actor, as a Jetstream service.
//!
//! The same split the other services make: the *decisions* are the verified
//! functions in [`crate::actor::steps`] — [`accept_step`](crate::actor::steps::accept_step),
//! [`send_step`](crate::actor::steps::send_step) and
//! [`apply_step`](crate::actor::steps::apply_step), which
//! `crate::actor::proofs::refinement` ties to the model — and this file is the
//! part around them: who is calling, what a message carries, and the journal the
//! decisions read.
//!
//! # What the service is
//!
//! A [`Host`] holds an actor's **journal** and a mailbox of what has been sent,
//! and fences every append with the ownership [`Registry`](crate::ownership::service::Registry)
//! it is built around. The registry is the same one the `Ownership` service
//! serves, with the same epoch floor; the actor adds nothing to the ownership
//! protocol, it *uses* it. Four of the trait's methods are the ownership calls,
//! delegated; the other four are the actor's:
//!
//! | model step | method | acts at |
//! | --- | --- | --- |
//! | `Send { from, body }` | [`Actor::send`] | the caller |
//! | `Accept { host, epoch, env }` | [`Actor::accept`] | the caller (`host`) |
//! | — (a read) | [`Actor::state`], [`Actor::journal`] | — |
//!
//! **No method takes the acting node's number.** [`Actor::accept`] does take a
//! `sender`, and that is not the same thing: it names whose message is being
//! processed, and the host checks it against the mailbox, so naming a message
//! that was never sent is refused rather than believed.
//!
//! # Why the registry is inside, and behind a gate
//!
//! An append reads the registry (is this host the owner at this epoch?) and
//! writes the journal. Two locks taken one after the other would leave a gap
//! between the question and the write, and the gap is the race fencing exists to
//! close: the registry answers "yes, you own it", a handover completes, and the
//! append lands in a journal the host no longer has the right to write. So every
//! method takes one **gate** first, and the registry is built inside
//! [`Host::new`] from the one roster and exposed only through read-only views —
//! the same construction, for the same reasons, as `composed::service`.
//!
//! # What goes on the wire, and what does not
//!
//! The behaviour is applied by the service, not by the host: the state is a fold
//! over the journal, so [`Actor::accept`] returns the state it produced and a
//! host never computes it. Forcing a handover (`Host::force`) is the
//! coordinator's own transition and is not on the wire, for the reason `force`
//! is not on the ownership trait.
//!
//! # Liveness, stated
//!
//! This service refines the actor machine's crash-free executions: it has no
//! `Crash` or `Recover`, because liveness is ground truth a process cannot
//! evaluate. See `crate::composed::steps` for the argument.
//!
//! # The assumption this rests on, stated
//!
//! The same one the other services state: a caller is identified by
//! [`Context::remote`] against a roster fixed at construction, and an address is
//! not a credential.

mod host;
mod lane;
mod mailbox;
mod refusal;
mod session;
mod supervisor;
mod transport;

pub use host::{Event, Host};
pub use lane::{bridge, read_attach, write_attach};
pub use mailbox::{Capacity, Mailbox, Permit, Round, Waiter};
pub use session::{Closer, Delivery, Fence, Session, refuse_all, serve, serve_fenced, serve_until};
pub use supervisor::{ActorRef, LocalSupervisor, Status, Supervisor};
pub use transport::Connection;

use crate::actor::model::Envelope;
use crate::id::Id;
use crate::ownership::service::Offer;
use jetstream::prelude::*;

/// What accepting a message produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Receipt {
    /// The message's position in the journal.
    pub index: u64,
    /// The actor's state after applying it.
    pub state: u64,
}

/// The actor, as of the journal's end.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Snapshot {
    /// How many messages the journal holds.
    pub len: u64,
    /// The state those messages fold to.
    pub state: u64,
}

/// One journal entry, on the wire: a message, and who accepted it under which
/// epoch.
#[derive(Debug, Clone, PartialEq, Eq, JetStreamWireFormat)]
pub struct Record {
    pub sender: Id,
    pub seq: u64,
    pub body: Vec<u8>,
    pub host: Id,
    pub epoch: u64,
}

/// What the room says when a subscription ends normally. This is the
/// value a plain `Stream` has nowhere to put.
#[derive(Debug, Clone, JetStreamWireFormat)]
pub struct Closed {
    pub last_seq: u64,
}

/// The most records one `journal` read returns.
pub const MAX_READ: u64 = 1024;

/// The longest message body a host takes: the most a `Vec<u8>` can carry on the
/// wire, whose length is a `u16`. A body any longer could not be sent, nor read
/// back from the journal.
pub const MAX_BODY: u64 = u16::MAX as u64;

/// The node-facing protocol: four ownership calls, and the actor's own.
///
/// None takes the acting node's number — see the module docs.
#[service(uses(super::{Closed, Id, Offer, Receipt, Record, Snapshot}, crate::actor::model::Envelope))]
pub trait Actor {
    // --- ownership, delegated ----------------------------------------------

    /// What is on offer for the caller?
    async fn poll(&self, ctx: Context) -> Result<Offer>;

    /// Take an offered grant: become the actor's host.
    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()>;

    /// The host agrees to hand the actor to `to`. Its epoch is burned from this
    /// moment, so nothing it appends afterwards is accepted.
    async fn begin_transfer(&self, ctx: Context, to: Id) -> Result<()>;

    /// The outgoing host acknowledges the revocation.
    async fn release(&self, ctx: Context, epoch: u64) -> Result<()>;

    // --- the actor -----------------------------------------------------------

    /// `Send`: the caller sends the actor a message, numbered by the host. Returns
    /// its sequence number, which is the caller's own count — the first is 0.
    ///
    /// A reply lost on the way back makes a retry a second message, which is why
    /// [`call`](Actor::call), where the caller does the numbering, exists.
    async fn send(&self, ctx: Context, body: Vec<u8>) -> Result<u64>;

    /// `Accept`: the caller, presenting `epoch`, processes the message `sender`
    /// sent as number `seq`.
    ///
    /// Refused unless the caller is the owner at exactly that epoch, the message
    /// was sent, and it is exactly its turn: a message already accepted and one
    /// not yet due are both refused, which is what makes redelivery harmless.
    async fn accept(&self, ctx: Context, epoch: u64, sender: Id, seq: u64) -> Result<Receipt>;

    /// The actor's state, as of the journal's end. Any member may read.
    async fn state(&self, ctx: Context) -> Result<Snapshot>;

    /// Up to [`MAX_READ`] journal entries starting at index `from`. This is how a
    /// host that has just taken the actor catches up: the journal, not a copy of
    /// the previous host's memory.
    async fn journal(&self, ctx: Context, from: u64, limit: u64) -> Result<Vec<Record>>;

    /// `Send`, numbered by the caller: deliver `envelope` to the actor.
    ///
    /// `envelope.sender` must be the caller, as the connection says; an envelope
    /// naming anyone else is refused. If the host has already recorded this very
    /// message the call succeeds and changes nothing, so a caller whose reply was
    /// lost can send it again. The same number with a different body, or a number
    /// that is neither the caller's next nor one already used, is refused.
    async fn call(&self, ctx: Context, envelope: Envelope) -> Result<()>;

    /// The messages the actor has for the caller, from number `from`; the
    /// subscription ends with a [`Closed`] carrying the last number it sent.
    ///
    /// Nothing is sent yet: the model's actor has no outputs, only a state, so
    /// there is no `Send` from an actor for this to carry. It ends at once.
    #[subscription]
    fn replies(&self, ctx: Context, from: u64) -> Subscription<Envelope, Closed>;
}
