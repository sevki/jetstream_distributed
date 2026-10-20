//! **Claim 4 - Transfer safety.**
//!
//! Ownership transfer is modelled as several protocol transitions, never as an
//! atomic assignment. Every permitted transition preserves the ownership and
//! fencing invariants, and at no point can both the outgoing and the incoming
//! node have authority.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::ownership::proofs::invariant::*;
use crate::ownership::transfer::*;

verus! {

/// **Every permitted transition preserves the invariants.**
pub proof fn theorem_transition_preserves_invariants(pre: OwnershipSystem, post: OwnershipSystem, s: Step, a: ActorId)
    requires
        inv(pre),
        step(pre, post, s),
        pre.actors.contains_key(a),
    ensures
        inv(post),
        post.actors.contains_key(a),
        current_epoch(post.actors[a]) >= current_epoch(pre.actors[a]),
{
    lemma_step_preserves_inv(pre, post, s);
    lemma_step_epoch_monotone(pre, post, s, a);
}

/// **Transfer safety, stagewise.** Walking the canonical handover
/// `Owned(A,e) -> Transferring(A,B,e,e+1) -> Unowned(e+1,B) -> Owned(B,e+1)`:
///
/// * the epoch never decreases;
/// * during the two middle stages nobody has authority;
/// * `A` is fenced out from the first transition onwards;
/// * at the end exactly one node - `B` - has authority.
pub proof fn theorem_handover_safety(a: Id, b: Id, e: Epoch, n: Id, x: Epoch)
    requires
        a != b,
    ensures
        current_epoch(stage_owned(a, e)) <= current_epoch(stage_transferring(a, b, e)),
        current_epoch(stage_transferring(a, b, e)) <= current_epoch(stage_unowned(b, e)),
        current_epoch(stage_unowned(b, e)) <= current_epoch(stage_acquired(b, e)),
        !may_mutate(stage_transferring(a, b, e), n, x),
        !may_mutate(stage_unowned(b, e), n, x),
        !may_mutate(stage_acquired(b, e), a, e),
        may_mutate(stage_acquired(b, e), n, x) ==> n == b && x == e + 1,
{
    lemma_handover_epochs(a, b, e);
    lemma_handover_middle_has_no_owner(a, b, e, n, x);
    lemma_outgoing_owner_fenced(a, b, e);
}

/// **It is never possible for both nodes to have authority.** For every stage
/// of a handover, `A` and `B` are never simultaneously permitted to mutate.
pub proof fn theorem_handover_never_both(a: Id, b: Id, e: Epoch, ea: Epoch, eb: Epoch)
    requires
        a != b,
    ensures
        !(may_mutate(stage_owned(a, e), a, ea) && may_mutate(stage_owned(a, e), b, eb)),
        !(may_mutate(stage_transferring(a, b, e), a, ea) && may_mutate(
            stage_transferring(a, b, e),
            b,
            eb,
        )),
        !(may_mutate(stage_unowned(b, e), a, ea) && may_mutate(stage_unowned(b, e), b, eb)),
        !(may_mutate(stage_acquired(b, e), a, ea) && may_mutate(stage_acquired(b, e), b, eb)),
{
}

/// **Interrupted transfer.** If a handover is abandoned while `Transferring`,
/// recovery burns another epoch. Neither the outgoing owner's epoch nor the
/// abandoned incoming epoch is usable afterwards.
pub proof fn theorem_interrupted_transfer_fences_both(a: Id, b: Id, e: Epoch)
    ensures
        !may_mutate(OwnershipState::Unowned { epoch: e + 2, intended_owner: a }, a, e),
        !may_mutate(OwnershipState::Unowned { epoch: e + 2, intended_owner: a }, b, e + 1),
        current_epoch(OwnershipState::Unowned { epoch: e + 2, intended_owner: a }) > current_epoch(
            stage_transferring(a, b, e),
        ),
{
    lemma_aborted_handover_fences_both(a, b, e);
}

/// Ownership cannot be manufactured out of nothing: if an actor is `Owned` after
/// a step but was not `Owned` by the same node at the same epoch before it, the
/// step must have been an `Acquire` of that actor, which in turn requires the
/// actor to have been `Unowned` at exactly that epoch with that node as the
/// intended owner.
pub proof fn theorem_ownership_only_via_acquire(
    pre: OwnershipSystem,
    post: OwnershipSystem,
    s: Step,
    a: ActorId,
    n: Id,
    e: Epoch,
)
    requires
        step(pre, post, s),
        pre.actors.contains_key(a),
        !may_mutate(pre.actors[a], n, e),
        may_mutate(post.actors[a], n, e),
    ensures
        s == (Step::Acquire { actor: a, node: n }),
        pre.actors[a] == (OwnershipState::Unowned { epoch: e, intended_owner: n }),
        pre.network.contains(Message::Grant { actor: a, to: n, epoch: e }),
        pre.live.contains(n),
{
    match s {
        Step::Acquire { actor, node } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {
                    assert(actor == a);
                    assert(node == n);
                    assert(epoch == e);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::BeginTransfer { actor, from, to } => {
            assert(false);
        },
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {
            assert(false);
        },
        Step::CompleteRelease { actor } => {
            assert(false);
        },
        Step::AbortTransfer { actor } => {
            assert(false);
        },
        Step::RevokeOwner { actor, next } => {
            assert(false);
        },
        Step::ReassignUnowned { actor, next } => {
            assert(false);
        },
        Step::IssueGrant { actor } => {
            assert(false);
        },
        Step::Crash { node } => {
            assert(false);
        },
        Step::Recover { node } => {
            assert(false);
        },
        Step::Replay { msg } => {
            assert(false);
        },
        Step::Stutter => {
            assert(false);
        },
    }
}

} // verus!
