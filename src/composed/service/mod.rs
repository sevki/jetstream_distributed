//! Ownership and Raymond, behind one coordinator, over Jetstream RPC.
//!
//! The composition is not an algorithm of its own — it is two, with the coupling
//! between them made a **guard**. So this service is the two existing ones
//! ([`Registry`](crate::ownership::service::Registry) and
//! [`Router`](crate::raymond::service::Router)) and the guards that tie them together, and
//! almost all of it is delegation. What it adds is small and is the whole point:
//!
//! * **the privilege moves only once the actor has been released.**
//!   [`Composed::assign_privilege`] refuses while the actor is `Owned` or
//!   `Transferring`, however willing the routing layer is
//!   (`cs_pass_token`, [`crate::composed::steps::pass_token_step`]);
//! * **authority is taken only by the node holding the privilege.**
//!   [`Composed::acquire`] refuses a node the routing layer has not elected
//!   (`cs_acquire_under_token`);
//! * **the privilege can be taken from a holder that does not cooperate**
//!   ([`Coordinator::seize_token`], `cs_seize_token`), and the node it was taken
//!   from owes a reconciliation ([`Composed::reconcile`], `cs_reconcile`).
//!
//! Everything else is carried: a routing step is the Raymond layer's own
//! (`cs_ray`) and an ownership step is the ownership layer's own (`cs_own`), and
//! `crate::composed::proofs::refinement` proves that carrying a step the layers
//! have already proved correct needs no second proof.
//!
//! # Why one coordinator, and why a gate
//!
//! The coupling reads **both** layers' state in one decision: `assign_privilege`
//! asks the registry whether the actor is `Unowned` and then moves the
//! privilege. Two locks, taken one after the other, would leave a gap between
//! the question and the move — and the gap is exactly the race the guard
//! exists to close. Say the registry answers "unowned", an `acquire` slips in
//! (the caller still holds the privilege, so the coupling lets it), and then the
//! privilege moves: authority stranded at a node that no longer holds the
//! privilege. So every method takes one **gate** first, and the two layers
//! underneath it are never shared with anything else. That is enforced rather
//! than asked for: [`Coordinator::new`] builds both layers itself, from one
//! identity, and exposes only read-only views of them. Handing in a `Registry` and
//! a `Router` would let a caller keep them, and every method of their service
//! traits takes `&self` — it could pass the privilege while authority sat at the
//! old owner. It would also let the layers disagree about which address is which
//! node.
//!
//! # Liveness, stated
//!
//! The composed *model* guards some steps on `own.live`, which is ground truth.
//! This service has no `Crash` or `Recover`: the steps it calls refine the composed
//! machine's executions in which no node crashes, and the service around them is
//! plain Rust and tested. See [`crate::composed::steps`] for the
//! argument, and for why that still covers the case the machine exists for —
//! taking the privilege from a holder that is merely unreachable.
//!
//! # The assumption this rests on, stated
//!
//! The same one the other services state, and now stated once, in
//! [`crate::identity`]: a caller is identified by asking an
//! [`Identity`](crate::identity::Identity), which for a [`Roster`](crate::identity::Roster)
//! is [`Context::remote`] looked up in a table fixed at construction, and an address
//! is not a credential.

mod command;
mod coordinator;
mod refusal;

pub use command::{apply, Command, Reply};
pub use coordinator::{Coordinator, Event};

use crate::ownership::service::Offer;
use crate::raymond::service::Standing;
use crate::id::Id;
use jetstream::prelude::*;

/// The node-facing protocol: the ownership layer's five calls, the routing
/// layer's six, and the one step that belongs to neither.
///
/// None takes the acting node's number. Seizing the privilege is **not** here:
/// it is the coordinator's own step, and a node-facing service that offered it
/// would let any node take the privilege from the one that holds it.
#[service(uses(super::{Id, Offer, Standing}))]
pub trait Composed {
    // --- ownership, carried ---------------------------------------------

    /// What is on offer for the caller?
    async fn poll(&self, ctx: Context) -> Result<Offer>;

    /// `AcquireUnderToken`: take an offered grant — **only if the caller holds
    /// the privilege.**
    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()>;

    /// Write as the current owner, returning the sequence number.
    async fn write(&self, ctx: Context, epoch: u64) -> Result<u64>;

    /// The owner agrees to hand the actor to `to`.
    async fn begin_transfer(&self, ctx: Context, to: Id) -> Result<()>;

    /// The outgoing owner acknowledges the revocation.
    async fn release(&self, ctx: Context, epoch: u64) -> Result<()>;

    // --- routing, carried -----------------------------------------------

    /// What do my own routing entries say?
    async fn standing(&self, ctx: Context) -> Result<Standing>;

    /// I want the privilege.
    async fn request_cs(&self, ctx: Context) -> Result<()>;

    /// Forward my request one hop towards the privilege.
    async fn make_request(&self, ctx: Context) -> Result<Id>;

    /// A request `from` sent to me arrives.
    async fn receive_request(&self, ctx: Context, from: Id) -> Result<()>;

    /// I enter my critical section.
    async fn enter_cs(&self, ctx: Context) -> Result<()>;

    /// I leave it.
    async fn exit_cs(&self, ctx: Context) -> Result<()>;

    // --- the coupling ---------------------------------------------------

    /// `PassToken`: hand the privilege to the head of my queue — **only once
    /// the actor has been released.** Returns who got it.
    async fn assign_privilege(&self, ctx: Context) -> Result<Id>;

    /// `Reconcile`: the privilege was taken from me. I drop the belief that I
    /// hold it and leave the critical section I thought I was in.
    async fn reconcile(&self, ctx: Context) -> Result<()>;
}
