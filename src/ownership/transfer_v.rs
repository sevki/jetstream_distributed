//! Ownership handover, modelled as a sequence of protocol transitions rather
//! than an atomic assignment.
//!
//! ```text
//! Owned(A, 41)
//!       |  BeginTransfer
//! Transferring(A, B, 41, 42)
//!       |  CompleteRelease
//! Unowned(42, B)
//!       |  Acquire
//! Owned(B, 42)
//! ```
//!
//! During the two middle stages *nobody* has mutable authority. That is the
//! deliberate trade: the protocol gives up availability during handover in
//! order to make double ownership unrepresentable.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;

verus! {

/// Stage 1 of a handover: `a` owns the actor at `e`.
pub open spec fn stage_owned(a: Id, e: Epoch) -> OwnershipState {
    OwnershipState::Owned { owner: a, epoch: e }
}

/// Stage 2: authority withdrawn from `a`, epoch `e + 1` allocated for `b`.
pub open spec fn stage_transferring(a: Id, b: Id, e: Epoch) -> OwnershipState {
    OwnershipState::Transferring { from: a, to: b, old_epoch: e, new_epoch: e + 1 }
}

/// Stage 3: nobody owns the actor; `b` is the intended owner at `e + 1`.
pub open spec fn stage_unowned(b: Id, e: Epoch) -> OwnershipState {
    OwnershipState::Unowned { epoch: e + 1, intended_owner: b }
}

/// Stage 4: `b` owns the actor at `e + 1`.
pub open spec fn stage_acquired(b: Id, e: Epoch) -> OwnershipState {
    OwnershipState::Owned { owner: b, epoch: e + 1 }
}

/// The epoch never goes backwards along a handover, and it strictly increases
/// exactly once, at `BeginTransfer`.
pub proof fn lemma_handover_epochs(a: Id, b: Id, e: Epoch)
    ensures
        current_epoch(stage_owned(a, e)) == e,
        current_epoch(stage_transferring(a, b, e)) == e + 1,
        current_epoch(stage_unowned(b, e)) == e + 1,
        current_epoch(stage_acquired(b, e)) == e + 1,
{
}

/// Nobody at all may mutate during the two middle stages of a handover.
pub proof fn lemma_handover_middle_has_no_owner(a: Id, b: Id, e: Epoch, n: Id, x: Epoch)
    ensures
        !may_mutate(stage_transferring(a, b, e), n, x),
        !may_mutate(stage_unowned(b, e), n, x),
{
}

/// The outgoing owner is fenced out from the moment the transfer starts, and
/// stays fenced out for the rest of the handover - including after `b` has
/// taken ownership.
pub proof fn lemma_outgoing_owner_fenced(a: Id, b: Id, e: Epoch)
    ensures
        !may_mutate(stage_transferring(a, b, e), a, e),
        !may_mutate(stage_unowned(b, e), a, e),
        !may_mutate(stage_acquired(b, e), a, e),
        !valid_fence(stage_transferring(a, b, e), e),
        !valid_fence(stage_unowned(b, e), e),
        !valid_fence(stage_acquired(b, e), e),
{
}

/// At every stage of a handover at most one node has authority, and at the two
/// middle stages that number is zero.
pub proof fn lemma_handover_never_two_owners(
    a: Id,
    b: Id,
    e: Epoch,
    n1: Id,
    e1: Epoch,
    n2: Id,
    e2: Epoch,
)
    ensures
        may_mutate(stage_owned(a, e), n1, e1) && may_mutate(stage_owned(a, e), n2, e2) ==> n1 == n2,
        may_mutate(stage_acquired(b, e), n1, e1) && may_mutate(stage_acquired(b, e), n2, e2) ==> n1
            == n2,
        !may_mutate(stage_transferring(a, b, e), n1, e1),
        !may_mutate(stage_unowned(b, e), n1, e1),
{
}

/// An interrupted handover burns another epoch, so a `Grant` for the abandoned
/// epoch is stale on arrival.
pub proof fn lemma_aborted_handover_fences_both(a: Id, b: Id, e: Epoch)
    ensures
        current_epoch(OwnershipState::Unowned { epoch: e + 2, intended_owner: a }) > current_epoch(
            stage_transferring(a, b, e),
        ),
        !may_mutate(OwnershipState::Unowned { epoch: e + 2, intended_owner: a }, a, e),
        !may_mutate(OwnershipState::Unowned { epoch: e + 2, intended_owner: a }, b, e + 1),
{
}

/// A single transition never decreases an actor's epoch.
pub proof fn lemma_step_epoch_monotone(pre: OwnershipSystem, post: OwnershipSystem, s: Step, a: Id)
    requires
        step(pre, post, s),
        pre.actors.contains_key(a),
    ensures
        post.actors.contains_key(a),
        current_epoch(post.actors[a]) >= current_epoch(pre.actors[a]),
{
    match s {
        Step::Acquire { actor, node } => {
            if actor == a {
                match pre.actors[a] {
                    OwnershipState::Unowned { epoch, intended_owner } => {},
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        Step::BeginTransfer { actor, from, to } => {
            if actor == a {
                match pre.actors[a] {
                    OwnershipState::Owned { owner, epoch } => {},
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        Step::CompleteRelease { actor } => {
            if actor == a {
                match pre.actors[a] {
                    OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        Step::AbortTransfer { actor } => {
            if actor == a {
                match pre.actors[a] {
                    OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        Step::RevokeOwner { actor, next } => {
            if actor == a {
                match pre.actors[a] {
                    OwnershipState::Owned { owner, epoch } => {},
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        Step::ReassignUnowned { actor, next } => {
            if actor == a {
                match pre.actors[a] {
                    OwnershipState::Unowned { epoch, intended_owner } => {},
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        Step::IssueGrant { actor } => {
            if actor == a {
                match pre.actors[a] {
                    OwnershipState::Unowned { epoch, intended_owner } => {},
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {},
        Step::Crash { node } => {},
        Step::Recover { node } => {},
        Step::Replay { msg } => {},
        Step::Stutter => {},
    }
}

} // verus!
