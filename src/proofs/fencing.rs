//! **Claim 2 - Unique current epoch**, **Claim 3 - Stale-owner fencing**, and
//! **Claim 5 - Epoch monotonicity.**
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::invariant::*;
use crate::transfer::*;

verus! {

/// **Unique current epoch.** An actor has exactly one authoritative fencing
/// epoch.
///
/// Stated unconditionally: existence is asserted outright rather than under the
/// assumption that some authoritative epoch was already supplied, and
/// uniqueness is an implication over *arbitrary* epochs. A version taking two
/// authoritative epochs as hypotheses would establish existence only where a
/// witness already existed, which is not the claim.
pub proof fn theorem_unique_current_epoch(s: OwnershipState)
    ensures
        is_authoritative_epoch(s, current_epoch(s)),
        forall|e: Epoch| #[trigger] is_authoritative_epoch(s, e) ==> e == current_epoch(s),
{
    lemma_authoritative_epoch_exists(s);
    assert forall|e: Epoch| #[trigger] is_authoritative_epoch(s, e) implies e == current_epoch(s)
        by {
        lemma_authoritative_epoch_unique(s, e, current_epoch(s));
    }
}

/// **Stale-owner fencing.**
///
/// ```text
/// current_epoch(actor) > supplied_epoch  ==>  !can_mutate(actor, node, supplied_epoch)
/// ```
pub proof fn theorem_stale_epoch_cannot_mutate(
    sys: System,
    a: ActorId,
    node: NodeId,
    supplied_epoch: Epoch,
)
    requires
        sys.actors.contains_key(a),
        current_epoch(sys.actors[a]) > supplied_epoch,
    ensures
        !can_mutate(sys, a, node, supplied_epoch),
        !valid_fence(sys.actors[a], supplied_epoch),
{
    lemma_stale_epoch_cannot_mutate(sys.actors[a], node, supplied_epoch);
}

/// The state-local phrasing of the same claim: advancing from epoch `n` to
/// `n + 1` strips authority from everyone holding `n`.
pub proof fn theorem_epoch_advance_fences_previous(s_old: OwnershipState, s_new: OwnershipState, n: NodeId, e: Epoch)
    requires
        current_epoch(s_old) == e,
        current_epoch(s_new) == e + 1,
    ensures
        !may_mutate(s_new, n, e),
{
    lemma_stale_epoch_cannot_mutate(s_new, n, e);
}

/// **Epoch monotonicity.** A transition never decreases an actor's epoch.
pub proof fn theorem_epoch_monotone_step(pre: System, post: System, s: Step, a: ActorId)
    requires
        step(pre, post, s),
        pre.actors.contains_key(a),
    ensures
        post.actors.contains_key(a),
        current_epoch(post.actors[a]) >= current_epoch(pre.actors[a]),
{
    lemma_step_epoch_monotone(pre, post, s, a);
}

/// Epoch monotonicity, lifted to `next`.
pub proof fn theorem_epoch_monotone_next(pre: System, post: System, a: ActorId)
    requires
        next(pre, post),
        pre.actors.contains_key(a),
    ensures
        post.actors.contains_key(a),
        current_epoch(post.actors[a]) >= current_epoch(pre.actors[a]),
{
    let s = choose|s: Step| step(pre, post, s);
    lemma_step_epoch_monotone(pre, post, s, a);
}

/// Epoch monotonicity along a whole execution.
pub proof fn theorem_epoch_monotone_execution(tr: Seq<System>, i: int, j: int, a: ActorId)
    requires
        valid_execution(tr),
        0 <= i <= j < tr.len(),
        tr[i].actors.contains_key(a),
    ensures
        tr[j].actors.contains_key(a),
        current_epoch(tr[j].actors[a]) >= current_epoch(tr[i].actors[a]),
    decreases j - i,
{
    if i == j {
    } else {
        assert(next(tr[i], tr[i + 1]));
        theorem_epoch_monotone_next(tr[i], tr[i + 1], a);
        theorem_epoch_monotone_execution(tr, i + 1, j, a);
    }
}

/// Under the system invariant, no *issued* token can carry an epoch ahead of
/// the actor's current epoch, so for issued tokens the fence check degenerates
/// to epoch equality. (Without the invariant, `valid_fence` would also accept
/// an impossibly-far-future epoch.)
pub proof fn theorem_fence_is_exact_for_issued_tokens(sys: System, t: Token)
    requires
        reachable(sys),
        token_held(sys, t),
    ensures
        t.epoch <= current_epoch(sys.actors[t.actor]),
        valid_fence(sys.actors[t.actor], t.epoch) <==> t.epoch == current_epoch(
            sys.actors[t.actor],
        ),
{
    theorem_reachable_inv(sys);
    assert(token_inv(sys, t));
}

} // verus!
