//! The protocol's transitions, executable and verified.
//!
//! [`crate::exec`] made one decision machine-checked: the fence. Everything
//! else a server does — deciding whether an acquire may be taken, what a
//! handover moves the actor to, where a forced revoke leaves it — was
//! hand-written next to the model and checked by reading. This module is the
//! rest of the decisions, written the way `exec` writes the fence: as small
//! executable functions over `u64` state whose postconditions are stated in
//! terms of [`crate::model`].
//!
//! # What a step is, and what it is not
//!
//! A step here is a **pure function of the actor's record**. It takes the
//! state, the arguments of the request and a small number of facts the caller
//! has already established — whether a grant was issued, whether the named
//! successor is a real node — and returns the new state or a refusal. It does
//! no I/O, takes no lock, knows nothing about who is connected and decides
//! nothing about identity. Those are the server's business and stay there.
//!
//! The division is what makes the verification worth anything. If the step
//! functions also resolved identity, "verified transition" would quietly
//! include a lookup that no theorem covers. What is left outside is therefore
//! named rather than left to be discovered: **the lock, the identity lookup,
//! the durable epoch floor and the audit log are not verified**, and
//! `services/ownership` says so too.
//!
//! # The two places the executable steps are narrower than the model
//!
//! Both are the implementation's, both are refusals rather than divergences,
//! and both are stated in the theorems rather than hidden:
//!
//! * **Epoch exhaustion.** The model counts epochs in `nat` and never runs out.
//!   A step that would advance past `u64::MAX` refuses with
//!   [`Refusal::Exhausted`] instead of wrapping, because wrapping would take
//!   the epoch *backwards* and that is the one ordering every fencing theorem
//!   rests on.
//!
//! * **The request names an epoch.** `tr_acquire` reads the epoch out of the
//!   actor's record and requires a `Grant` for it; a request, by contrast,
//!   arrives carrying an epoch, and a request naming a different one is
//!   refused. So [`acquire_step`] fires exactly when the model's step is
//!   enabled *and* the request named the actor's current epoch — see
//!   `crate::proofs::refinement::theorem_acquire_step_refuses_exactly_when_disabled`,
//!   whose hypothesis is that second conjunct.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;

verus! {

/// Why a step did not fire.
///
/// These are the *protocol's* reasons. A server has others — an unknown
/// caller, a floor it could not write — and they are not in here, because a
/// step function never learns about them.
#[derive(Clone, Copy)]
pub enum Refusal {
    /// No grant was ever issued for this node at this epoch. `tr_acquire`'s
    /// second conjunct: a grant has to have been *issued*, not merely be due.
    NoGrant,
    /// The actor is not on offer to this node at this epoch.
    NotOffered,
    /// The caller does not own the actor.
    NotOwner,
    /// A node cannot hand the actor to itself. `tr_begin_transfer`'s
    /// `from != to`.
    SameNode,
    /// The named successor is not a node. `pre.nodes.contains(..)`.
    NoSuchNode,
    /// No transfer of this caller's is in flight at this epoch.
    NoTransfer,
    /// The `u64` epoch space is exhausted. See the module docs.
    Exhausted,
}

/// The actor's ownership record, at `u64`.
///
/// [`OwnershipState`] narrowed to the machine's integers, with every case
/// present — including the two in which nobody may mutate anything.
/// [`crate::exec::FenceGuard`] narrowed it to the `Owned` case alone, which is
/// why a server using it had to write the other two cases out by hand, in Rust,
/// with nothing checking them.
#[derive(Clone, Copy)]
pub enum ExecState {
    Unowned { epoch: u64, intended: u64 },
    Transferring { from: u64, to: u64, old_epoch: u64, new_epoch: u64 },
    Owned { owner: u64, epoch: u64 },
}

impl ExecState {
    /// The ghost record this stands for.
    pub open spec fn view(self) -> OwnershipState {
        match self {
            ExecState::Unowned { epoch, intended } => OwnershipState::Unowned {
                epoch: epoch as nat,
                intended_owner: intended as nat,
            },
            ExecState::Transferring { from, to, old_epoch, new_epoch } =>
                OwnershipState::Transferring {
                    from: from as nat,
                    to: to as nat,
                    old_epoch: old_epoch as nat,
                    new_epoch: new_epoch as nat,
                },
            ExecState::Owned { owner, epoch } => OwnershipState::Owned {
                owner: owner as nat,
                epoch: epoch as nat,
            },
        }
    }

    /// The actor's one authoritative epoch, executable.
    ///
    /// The `Transferring` case reports `new_epoch`, which is what fences the
    /// outgoing owner from the moment the handover is agreed rather than from
    /// the moment it completes. That is [`current_epoch`]'s choice, and this
    /// function is proved to make the same one.
    pub fn current(&self) -> (r: u64)
        ensures
            r as nat == current_epoch(self.view()),
    {
        match *self {
            ExecState::Unowned { epoch, intended: _ } => epoch,
            ExecState::Transferring { from: _, to: _, old_epoch: _, new_epoch } => new_epoch,
            ExecState::Owned { owner: _, epoch } => epoch,
        }
    }

    /// Which node a forced revoke would offer the actor to. See
    /// [`force_offers_to`].
    pub fn offered_to_on_force(&self, next: u64) -> (r: u64)
        ensures
            r as nat == force_offers_to(self.view(), next as nat),
    {
        match *self {
            ExecState::Transferring { from, to: _, old_epoch: _, new_epoch: _ } => from,
            _ => next,
        }
    }
}

/// What a transition did.
pub enum Outcome {
    /// It fired, and this is the actor's new record.
    Moved(ExecState),
    /// It did not.
    Refused(Refusal),
}

/// What a forced revoke did. It additionally reports **which node the actor is
/// now offered to**, which is not always the one that was asked for: from
/// `Transferring` the model offers it back to the node the transfer came from.
pub enum ForceOutcome {
    Moved(ExecState, u64),
    Refused(Refusal),
}

/// What a poll is answered with.
pub enum ExecOffer {
    Nothing,
    Grant(u64),
    Revoke(u64),
}

// ---------------------------------------------------------------------------
// The guards and the results, at the model's level
// ---------------------------------------------------------------------------
//
// Each transition is split into "does it fire" and "where does it go". Keeping
// them apart is what lets a theorem say *refusing is exactly disablement*
// rather than only *accepting is sound*: a step function that refused
// everything would satisfy the second and nothing else.

/// `tr_acquire`'s guard, as much of it as an actor's record can decide, plus
/// the request-level epoch check. See the module docs.
pub open spec fn acquire_fires(s: OwnershipState, n: NodeId, e: Epoch, granted: bool) -> bool {
    match s {
        OwnershipState::Unowned { epoch, intended_owner } =>
            intended_owner == n && epoch == e && granted,
        _ => false,
    }
}

/// Where `tr_acquire` leaves the actor.
pub open spec fn acquire_next(s: OwnershipState, n: NodeId) -> OwnershipState {
    OwnershipState::Owned { owner: n, epoch: current_epoch(s) }
}

/// `tr_begin_transfer`'s guard, plus exhaustion. See the module docs.
pub open spec fn begin_transfer_fires(
    s: OwnershipState,
    from: NodeId,
    to: NodeId,
    to_is_node: bool,
) -> bool {
    match s {
        OwnershipState::Owned { owner, epoch: _ } => owner == from && from != to && to_is_node,
        _ => false,
    }
}

/// Where `tr_begin_transfer` leaves the actor: mid-handover, with the next
/// epoch already allocated and therefore already fencing `from`.
pub open spec fn begin_transfer_next(s: OwnershipState, to: NodeId) -> OwnershipState {
    match s {
        OwnershipState::Owned { owner, epoch } => OwnershipState::Transferring {
            from: owner,
            to: to,
            old_epoch: epoch,
            new_epoch: epoch + 1,
        },
        _ => s,
    }
}

/// The guard on a release: a transfer of this caller's, at this epoch.
///
/// The epoch is carried by the request rather than read from the record, and
/// that is the point — without it a release delayed on the wire, or replayed,
/// would complete a *later* handover by the same node.
pub open spec fn release_fires(s: OwnershipState, n: NodeId, e: Epoch) -> bool {
    match s {
        OwnershipState::Transferring { from, to: _, old_epoch: _, new_epoch } =>
            from == n && new_epoch == e,
        _ => false,
    }
}

/// Where a completed release leaves the actor.
pub open spec fn release_next(s: OwnershipState) -> OwnershipState {
    match s {
        OwnershipState::Transferring { from: _, to, old_epoch: _, new_epoch } =>
            OwnershipState::Unowned { epoch: new_epoch, intended_owner: to },
        _ => s,
    }
}

/// Which node a forced revoke offers the actor to. Not always `next`: from
/// `Transferring` the model gives the coordinator no way to redirect an
/// interrupted handover, so the actor goes back to the node it came from.
pub open spec fn force_offers_to(s: OwnershipState, next: NodeId) -> NodeId {
    match s {
        OwnershipState::Transferring { from, to: _, old_epoch: _, new_epoch: _ } => from,
        _ => next,
    }
}

/// Where a forced revoke leaves the actor: unowned, one epoch on, offered to
/// [`force_offers_to`].
pub open spec fn force_next(s: OwnershipState, next: NodeId) -> OwnershipState {
    OwnershipState::Unowned {
        epoch: current_epoch(s) + 1,
        intended_owner: force_offers_to(s, next),
    }
}

/// The node an `Unowned` actor is being held for.
///
/// Only meaningful under `is_unowned`; the other cases return a placeholder,
/// exactly as [`transferring_from`] does and for the same reason — an accessor
/// keeps a fact about one field statable without an existential over all of
/// them.
pub open spec fn intended_owner(s: OwnershipState) -> NodeId {
    match s {
        OwnershipState::Unowned { epoch: _, intended_owner } => intended_owner,
        _ => 0,
    }
}

/// What the registry has to say to `n`.
///
/// Written over [`ExecState`] rather than over [`OwnershipState`] so that the
/// epoch it carries is the machine's, with no cast in either direction. What
/// ties it to the model is
/// `crate::proofs::refinement::theorem_poll_step_refines_tr_issue_grant`.
pub open spec fn poll_answer(st: ExecState, n: u64) -> ExecOffer {
    match st {
        ExecState::Unowned { epoch, intended } => if intended == n {
            ExecOffer::Grant(epoch)
        } else {
            ExecOffer::Nothing
        },
        ExecState::Transferring { from, to: _, old_epoch: _, new_epoch } => if from == n {
            ExecOffer::Revoke(new_epoch)
        } else {
            ExecOffer::Nothing
        },
        ExecState::Owned { owner: _, epoch: _ } => ExecOffer::Nothing,
    }
}

// ---------------------------------------------------------------------------
// The executable steps
// ---------------------------------------------------------------------------

/// `tr_acquire`: take an offered grant.
///
/// `granted` is the caller's answer to "was a grant issued to this node at this
/// epoch?". It stands for `pre.network.contains(Grant { .. })`, and a server
/// supplies it from the set of grants it has actually published — which is the
/// coupling the refinement theorem requires and the server maintains.
pub fn acquire_step(st: ExecState, node: u64, epoch: u64, granted: bool) -> (r: Outcome)
    ensures
        match r {
            Outcome::Moved(next) => acquire_fires(st.view(), node as nat, epoch as nat, granted)
                && next.view() == acquire_next(st.view(), node as nat),
            Outcome::Refused(_) => !acquire_fires(st.view(), node as nat, epoch as nat, granted),
        },
{
    match st {
        ExecState::Unowned { epoch: e, intended } => {
            if intended != node || e != epoch {
                Outcome::Refused(Refusal::NotOffered)
            } else if !granted {
                Outcome::Refused(Refusal::NoGrant)
            } else {
                Outcome::Moved(ExecState::Owned { owner: node, epoch: e })
            }
        },
        _ => Outcome::Refused(Refusal::NotOffered),
    }
}

/// `tr_begin_transfer`: the owner agrees to hand the actor to `to`.
///
/// `to_is_node` stands for `pre.nodes.contains(to)`. The model requires the
/// successor to exist, and a precondition enforced only by well-behaved callers
/// is not a precondition at all.
pub fn begin_transfer_step(st: ExecState, from: u64, to: u64, to_is_node: bool) -> (r: Outcome)
    ensures
        match r {
            Outcome::Moved(next) => begin_transfer_fires(
                st.view(),
                from as nat,
                to as nat,
                to_is_node,
            ) && next.view() == begin_transfer_next(st.view(), to as nat),
            // Refusing is exactly disablement, *or* the epoch space ran out —
            // and in that one case the refusal says so, so the two are never
            // confused for one another.
            Outcome::Refused(why) => !begin_transfer_fires(
                st.view(),
                from as nat,
                to as nat,
                to_is_node,
            ) || (why is Exhausted),
        },
{
    // The two conditions that do not depend on the actor's record are answered
    // first, so that a malformed successor is reported as a malformed successor
    // whoever is asking. The alternative — deciding ownership first — answers
    // `NotOwner` to a request that was never well-formed.
    if !to_is_node {
        return Outcome::Refused(Refusal::NoSuchNode);
    }
    if from == to {
        return Outcome::Refused(Refusal::SameNode);
    }
    match st {
        ExecState::Owned { owner, epoch } => {
            if owner != from {
                Outcome::Refused(Refusal::NotOwner)
            } else if epoch == u64::MAX {
                Outcome::Refused(Refusal::Exhausted)
            } else {
                Outcome::Moved(
                    ExecState::Transferring {
                        from: owner,
                        to: to,
                        old_epoch: epoch,
                        new_epoch: epoch + 1,
                    },
                )
            }
        },
        _ => Outcome::Refused(Refusal::NotOwner),
    }
}

/// `tr_handle_revoke` followed by `tr_complete_release`: the outgoing owner
/// acknowledges, and the actor is offered on.
///
/// Two model transitions and one method, because the node's acknowledgement and
/// the coordinator's reaction to it are the same event when the coordinator is
/// the thing being called.
pub fn release_step(st: ExecState, node: u64, epoch: u64) -> (r: Outcome)
    ensures
        match r {
            Outcome::Moved(next) => release_fires(st.view(), node as nat, epoch as nat)
                && next.view() == release_next(st.view()),
            Outcome::Refused(_) => !release_fires(st.view(), node as nat, epoch as nat),
        },
{
    match st {
        ExecState::Transferring { from, to, old_epoch: _, new_epoch } => {
            if from != node || new_epoch != epoch {
                Outcome::Refused(Refusal::NoTransfer)
            } else {
                Outcome::Moved(ExecState::Unowned { epoch: new_epoch, intended: to })
            }
        },
        _ => Outcome::Refused(Refusal::NoTransfer),
    }
}

/// `tr_revoke_owner`, `tr_reassign_unowned` and `tr_abort_transfer`: the
/// coordinator forcing progress on its own.
///
/// One function because the three differ only in which state they fire from and
/// where they send the actor, and a server that had to choose between them
/// would be re-deciding, in Rust, something the actor's record already
/// determines.
pub fn force_step(st: ExecState, next: u64, next_is_node: bool) -> (r: ForceOutcome)
    ensures
        match r {
            ForceOutcome::Moved(moved, offered_to) => next_is_node && moved.view()
                == force_next(st.view(), next as nat) && offered_to as nat == force_offers_to(
                st.view(),
                next as nat,
            ),
            ForceOutcome::Refused(why) => !next_is_node || (why is Exhausted),
        },
{
    if !next_is_node {
        return ForceOutcome::Refused(Refusal::NoSuchNode);
    }
    let from_epoch = st.current();
    if from_epoch == u64::MAX {
        return ForceOutcome::Refused(Refusal::Exhausted);
    }
    let offered_to = st.offered_to_on_force(next);
    ForceOutcome::Moved(
        ExecState::Unowned { epoch: from_epoch + 1, intended: offered_to },
        offered_to,
    )
}

/// What the registry has to say to `node`, and nothing else.
///
/// A query: it moves nothing. The `Grant` arm is `tr_issue_grant`, which is
/// retransmission and is always safe because the grant names only state that is
/// already public; the `Revoke` arm hands the outgoing owner the message
/// `tr_begin_transfer` already put on the network.
pub fn poll_step(st: ExecState, node: u64) -> (r: ExecOffer)
    ensures
        r == poll_answer(st, node),
{
    match st {
        ExecState::Unowned { epoch, intended } => {
            if intended == node {
                ExecOffer::Grant(epoch)
            } else {
                ExecOffer::Nothing
            }
        },
        ExecState::Transferring { from, to: _, old_epoch: _, new_epoch } => {
            if from == node {
                ExecOffer::Revoke(new_epoch)
            } else {
                ExecOffer::Nothing
            }
        },
        ExecState::Owned { owner: _, epoch: _ } => ExecOffer::Nothing,
    }
}

/// The fence, over the whole state space.
///
/// [`crate::exec::FenceGuard::accepts`] answers this for the `Owned` case, and a
/// server holding a record that might be `Unowned` or `Transferring` had to
/// supply the other two answers itself, in unverified Rust, next to a comment
/// asserting they were `false`. Here all three come from one function with one
/// postcondition, so the `Transferring` case — the one the whole protocol turns
/// on, because it is where the outgoing owner is fenced — is checked rather
/// than asserted.
pub fn may_write_step(st: ExecState, node: u64, epoch: u64) -> (r: bool)
    ensures
        r == may_mutate(st.view(), node as nat, epoch as nat),
{
    match st {
        ExecState::Owned { owner, epoch: e } => node == owner && epoch == e,
        _ => false,
    }
}

} // verus!
