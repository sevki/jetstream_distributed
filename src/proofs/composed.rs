//! The composed machine keeps `couples` as an invariant.
//!
//! This is what makes "token transfer preserves ownership safety" a property of
//! the system rather than a hypothesis. In [`crate::raymond`] alone, `couples`
//! can be stated but nothing enforces it: `ray_assign_privilege` does not see the
//! ownership state, so a token could move out from under a node that still had
//! authority. [`crate::composed`] puts that synchronisation in the guards, and
//! the lemmas below discharge it for every transition.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::composed::*;
use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::invariant::*;
use crate::proofs::raymond::*;
use crate::proofs::transfer::*;
use crate::raymond::*;
use crate::transfer::*;

verus! {

/// A Raymond step that does not move the token - routing or critical-section
/// bookkeeping - leaves the coupling untouched.
pub proof fn lemma_composed_ray_preserves_inv(pre: Composed, post: Composed, s: RayStep)
    requires
        composed_inv(pre),
        cs_ray(pre, post, s),
    ensures
        composed_inv(post),
{
    lemma_ray_step_preserves_inv(pre.ray, post.ray, s);
    lemma_token_preserving_steps_keep_holder(pre.ray, post.ray, s);
    assert forall|nd: NodeId, e: Epoch|
        may_mutate(post.own.actors[post.actor], nd, e) implies has_token(post.ray, nd) by {
        assert(has_token(pre.ray, nd));
    }
}

/// An ownership transition that is not an `Acquire` of this actor cannot create
/// authority over it, so whoever could mutate after the step could already
/// mutate before it - and therefore already held the token.
pub proof fn lemma_composed_own_preserves_inv(pre: Composed, post: Composed, s: Step)
    requires
        composed_inv(pre),
        cs_own(pre, post, s),
    ensures
        composed_inv(post),
{
    lemma_step_preserves_inv(pre.own, post.own, s);
    lemma_step_epoch_monotone(pre.own, post.own, s, pre.actor);
    assert forall|nd: NodeId, e: Epoch|
        may_mutate(post.own.actors[post.actor], nd, e) implies has_token(post.ray, nd) by {
        if !may_mutate(pre.own.actors[pre.actor], nd, e) {
            theorem_ownership_only_via_acquire(pre.own, post.own, s, pre.actor, nd, e);
            assert(is_acquire_of(s, pre.actor));
            assert(false);
        }
        assert(has_token(pre.ray, nd));
    }
}

/// **The guard that matters.** The token may only move once the actor has been
/// released, so at the moment of transfer nobody has authority and the coupling
/// survives vacuously - which is exactly why it cannot be stranded.
pub proof fn lemma_composed_pass_token_preserves_inv(
    pre: Composed,
    post: Composed,
    n: NodeId,
    head: NodeId,
)
    requires
        composed_inv(pre),
        cs_pass_token(pre, post, n, head),
    ensures
        composed_inv(post),
        has_token(post.ray, head),
        forall|m: NodeId| #[trigger] has_token(post.ray, m) ==> m == head,
{
    lemma_assign_privilege_preserves_unique_token(pre.ray, post.ray, n, head);
    assert forall|nd: NodeId, e: Epoch|
        may_mutate(post.own.actors[post.actor], nd, e) implies has_token(post.ray, nd) by {
        assert(!is_owned(pre.own.actors[pre.actor]));
        assert(false);
    }
}

/// Taking ownership requires holding the token, so the node that gains authority
/// is the token holder by construction.
pub proof fn lemma_composed_acquire_preserves_inv(pre: Composed, post: Composed, n: NodeId)
    requires
        composed_inv(pre),
        cs_acquire_under_token(pre, post, n),
    ensures
        composed_inv(post),
{
    let s = Step::Acquire { actor: pre.actor, node: n };
    assert(step(pre.own, post.own, s));
    lemma_step_preserves_inv(pre.own, post.own, s);
    lemma_step_epoch_monotone(pre.own, post.own, s, pre.actor);
    match pre.own.actors[pre.actor] {
        OwnershipState::Unowned { epoch, intended_owner } => {
            assert(post.own.actors[pre.actor] == (OwnershipState::Owned {
                owner: n,
                epoch: epoch,
            }));
            assert forall|nd: NodeId, e: Epoch|
                may_mutate(post.own.actors[post.actor], nd, e) implies has_token(post.ray, nd) by {
                assert(nd == n);
            }
        },
        _ => {
            assert(false);
        },
    }
}

/// **Every composed transition preserves the coupling.**
pub proof fn theorem_composed_step_preserves_inv(pre: Composed, post: Composed, s: ComposedStep)
    requires
        composed_inv(pre),
        composed_step(pre, post, s),
    ensures
        composed_inv(post),
{
    match s {
        ComposedStep::Ray { ray_step } => {
            lemma_composed_ray_preserves_inv(pre, post, ray_step);
        },
        ComposedStep::Own { own_step } => {
            lemma_composed_own_preserves_inv(pre, post, own_step);
        },
        ComposedStep::PassToken { node, head } => {
            lemma_composed_pass_token_preserves_inv(pre, post, node, head);
        },
        ComposedStep::AcquireUnderToken { node } => {
            lemma_composed_acquire_preserves_inv(pre, post, node);
        },
    }
}

pub proof fn lemma_composed_next_preserves_inv(pre: Composed, post: Composed)
    requires
        composed_inv(pre),
        composed_next(pre, post),
    ensures
        composed_inv(post),
{
    let s = choose|s: ComposedStep| composed_step(pre, post, s);
    theorem_composed_step_preserves_inv(pre, post, s);
}

/// Initial composed states satisfy the invariant: nothing is owned yet, so the
/// coupling holds vacuously.
pub proof fn lemma_composed_init_inv(c: Composed)
    requires
        composed_init(c),
    ensures
        composed_inv(c),
{
    lemma_init_inv(c.own);
    let root = choose|root: NodeId| ray_init(c.ray, root);
    theorem_ray_init_inv(c.ray, root);
    assert forall|nd: NodeId, e: Epoch| may_mutate(c.own.actors[c.actor], nd, e)
        implies has_token(c.ray, nd) by {
        assert(starts_unowned(c.own.actors[c.actor]));
        assert(false);
    }
}

pub proof fn lemma_composed_execution_inv(tr: Seq<Composed>, i: int)
    requires
        composed_valid_execution(tr),
        0 <= i < tr.len(),
    ensures
        composed_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_composed_init_inv(tr[0]);
    } else {
        lemma_composed_execution_inv(tr, i - 1);
        assert(composed_next(tr[i - 1], tr[i]));
        lemma_composed_next_preserves_inv(tr[i - 1], tr[i]);
    }
}

/// **Every reachable composed state satisfies the coupling.**
pub proof fn theorem_composed_reachable_inv(c: Composed)
    requires
        composed_reachable(c),
    ensures
        composed_inv(c),
{
    let tr = choose|tr: Seq<Composed>| composed_valid_execution(tr) && tr[tr.len() - 1] == c;
    lemma_composed_execution_inv(tr, tr.len() - 1);
}

/// The composed machine really does admit critical-section entry.
///
/// Without this, `composed_next` could not represent any Raymond execution that
/// enters a critical section, every composed-reachable state would keep `using`
/// uniformly false, and the composed theorems below would only cover a
/// degenerate fragment of the real behaviour.
pub proof fn theorem_composed_admits_critical_section(pre: Composed, post: Composed, n: NodeId)
    requires
        composed_inv(pre),
        ray_enter_cs(pre.ray, post.ray, n),
        post.own == pre.own,
        post.actor == pre.actor,
    ensures
        composed_step(pre, post, ComposedStep::Ray { ray_step: RayStep::EnterCs { node: n } }),
        composed_inv(post),
        post.ray.using[n],
{
    lemma_composed_ray_preserves_inv(pre, post, RayStep::EnterCs { node: n });
}

/// Leaving the critical section is likewise a legal composed step.
pub proof fn theorem_composed_admits_critical_section_exit(
    pre: Composed,
    post: Composed,
    n: NodeId,
)
    requires
        composed_inv(pre),
        ray_exit_cs(pre.ray, post.ray, n),
        post.own == pre.own,
        post.actor == pre.actor,
    ensures
        composed_step(pre, post, ComposedStep::Ray { ray_step: RayStep::ExitCs { node: n } }),
        composed_inv(post),
        !post.ray.using[n],
{
    lemma_composed_ray_preserves_inv(pre, post, RayStep::ExitCs { node: n });
}

/// **The composed safety property.**
///
/// In every reachable state of the composed machine, at most one node may mutate
/// the actor, and that node is the one holding the Raymond token. Neither a
/// routing decision nor a token transfer can strand authority away from the
/// token, because the machine will not let the token move until the actor has
/// been released.
pub proof fn theorem_composed_exclusivity(
    c: Composed,
    n1: NodeId,
    e1: Epoch,
    n2: NodeId,
    e2: Epoch,
)
    requires
        composed_reachable(c),
        may_mutate(c.own.actors[c.actor], n1, e1),
        may_mutate(c.own.actors[c.actor], n2, e2),
    ensures
        n1 == n2,
        e1 == e2,
        has_token(c.ray, n1),
        forall|m: NodeId| #[trigger] has_token(c.ray, m) ==> m == n1,
{
    theorem_composed_reachable_inv(c);
    lemma_exclusive_owner(c.own.actors[c.actor], n1, e1, n2, e2);
    assert(has_token(c.ray, n1));
    assert forall|m: NodeId| #[trigger] has_token(c.ray, m) implies m == n1 by {
        theorem_ray_at_most_one_token(c.ray, m, n1);
    }
}

} // verus!
