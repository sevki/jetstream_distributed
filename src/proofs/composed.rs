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
use crate::proofs::properties::*;
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
    theorem_node_domain_constant(pre.own, post.own, s);
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

/// **Seizing the token preserves the coupling.**
///
/// Same argument as `lemma_composed_pass_token_preserves_inv`, and it is worth
/// noticing that it is the *same* argument: the guard is `is_unowned`, so
/// nobody has authority over the actor, so `couples` holds vacuously however
/// the token moves. Safety here does not come from the holder agreeing to let
/// go - it comes from the epoch having been burned before the token moved,
/// which is what lets a takeover be forcible at all.
pub proof fn lemma_composed_seize_preserves_inv(
    pre: Composed,
    post: Composed,
    from: NodeId,
    to: NodeId,
)
    requires
        composed_inv(pre),
        cs_seize_token(pre, post, from, to),
    ensures
        composed_inv(post),
        has_token(post.ray, to),
        !has_token(post.ray, from),
        forall|m: NodeId| #[trigger] has_token(post.ray, m) ==> m == to,
{
    lemma_seize_preserves_inv(pre.ray, post.ray, from, to);
    assert forall|nd: NodeId, e: Epoch|
        may_mutate(post.own.actors[post.actor], nd, e) implies has_token(post.ray, nd) by {
        assert(is_unowned(pre.own.actors[pre.actor]));
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
        ComposedStep::SeizeToken { from, to } => {
            lemma_composed_seize_preserves_inv(pre, post, from, to);
        },
        ComposedStep::Reconcile { node } => {
            lemma_composed_reconcile_preserves_inv(pre, post, node);
        },
        ComposedStep::AcquireUnderToken { node } => {
            lemma_composed_acquire_preserves_inv(pre, post, node);
        },
    }
}

/// Reconciliation touches only the seizure marker, so every part of the
/// invariant rides through untouched.
pub proof fn lemma_composed_reconcile_preserves_inv(pre: Composed, post: Composed, n: NodeId)
    requires
        composed_inv(pre),
        cs_reconcile(pre, post, n),
    ensures
        composed_inv(post),
{
}

/// **A seized node cannot rejoin `live` while it is still seized.**
///
/// `cs_own` refuses `Step::Recover` for such a node, so the only way back is
/// through [`cs_reconcile`] first. This is what stops recovery from silently
/// inheriting the routing rewrite that happened while the node was down.
pub proof fn theorem_seized_node_cannot_recover(
    pre: Composed,
    post: Composed,
    s: ComposedStep,
    n: NodeId,
)
    requires
        composed_step(pre, post, s),
        pre.seized.contains(n),
        !pre.own.live.contains(n),
    ensures
        !post.own.live.contains(n),
{
    match s {
        ComposedStep::Own { own_step } => {
            assert(!recovers_a_seized_node(pre, own_step));
            match own_step {
                Step::Recover { node } => {
                    assert(node != n);
                    assert(post.own.live == pre.own.live.insert(node));
                },
                Step::Crash { node } => {
                    assert(post.own.live == pre.own.live.remove(node));
                },
                _ => {
                    assert(post.own.live == pre.own.live);
                },
            }
        },
        _ => {
            assert(post.own.live == pre.own.live);
        },
    }
}

/// **Only two composed steps move the token, and the holder's liveness decides
/// which.**
///
/// A live holder passes it on ([`cs_pass_token`]); a fail-stopped one has it
/// taken ([`cs_seize_token`]); nothing else touches it. The `false` arms are the
/// content: routing, ownership transitions and acquisition all leave token
/// possession exactly as they found it, so there is no third way for the token
/// to move and in particular no step in which a crashed node hands it over as
/// though it were acting.
pub proof fn theorem_token_movement_is_partitioned(
    pre: Composed,
    post: Composed,
    s: ComposedStep,
    m: NodeId,
)
    requires
        composed_inv(pre),
        composed_step(pre, post, s),
        has_token(pre.ray, m),
        !has_token(post.ray, m),
    ensures
        match s {
            ComposedStep::PassToken { node, head } => node == m && pre.own.live.contains(m),
            ComposedStep::SeizeToken { from, to } => from == m && !pre.own.live.contains(m),
            ComposedStep::Ray { ray_step } => false,
            ComposedStep::Own { own_step } => false,
            ComposedStep::Reconcile { node } => false,
            ComposedStep::AcquireUnderToken { node } => false,
        },
{
    match s {
        ComposedStep::Ray { ray_step } => {
            lemma_token_preserving_steps_keep_holder(pre.ray, post.ray, ray_step);
            assert(has_token(post.ray, m));
            assert(false);
        },
        ComposedStep::Own { own_step } => {
            assert(post.ray == pre.ray);
            assert(has_token(post.ray, m));
            assert(false);
        },
        ComposedStep::AcquireUnderToken { node } => {
            assert(post.ray == pre.ray);
            assert(has_token(post.ray, m));
            assert(false);
        },
        ComposedStep::Reconcile { node } => {
            assert(post.ray == pre.ray);
            assert(has_token(post.ray, m));
            assert(false);
        },
        ComposedStep::PassToken { node, head } => {
            // `ray_assign_privilege` needs the *holder* to act, and the token is
            // unique, so that holder is `m`.
            assert(has_token(pre.ray, node));
            theorem_ray_at_most_one_token(pre.ray, m, node);
            assert(node == m);
            assert(pre.own.live.contains(node));
        },
        ComposedStep::SeizeToken { from, to } => {
            assert(has_token(pre.ray, from));
            theorem_ray_at_most_one_token(pre.ray, m, from);
            assert(from == m);
            assert(!pre.own.live.contains(from));
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

/// An initial composed state is reachable.
pub proof fn lemma_composed_reachable_init(c: Composed)
    requires
        composed_init(c),
    ensures
        composed_reachable(c),
{
    let tr = Seq::<Composed>::empty().push(c);
    assert(tr.len() == 1);
    assert(tr[0] == c);
    assert(composed_valid_execution(tr));
    assert(tr[tr.len() - 1] == c);
}

/// Composed reachability is closed under taking a step.
/// Every state reaches itself.
pub proof fn lemma_composed_reachable_from_refl(c: Composed)
    ensures
        composed_reachable_from(c, c),
{
    let tr = seq![c];
    assert(tr.len() == 1);
    assert(tr[0] == c);
    assert(tr[tr.len() - 1] == c);
    assert(composed_segment(tr));
}

/// Reachability-from extends by one step, exactly as reachability does.
pub proof fn lemma_composed_reachable_from_step(
    c: Composed,
    d: Composed,
    e: Composed,
    s: ComposedStep,
)
    requires
        composed_reachable_from(c, d),
        composed_step(d, e, s),
    ensures
        composed_reachable_from(c, e),
{
    let tr = choose|tr: Seq<Composed>|
        composed_segment(tr) && tr[0] == c && tr[tr.len() - 1] == d;
    let tr2 = tr.push(e);
    assert(tr2.len() == tr.len() + 1);
    assert(tr2[0] == tr[0]);
    assert forall|i: int|
        #![trigger tr2[i], tr2[i + 1]]
        0 <= i < tr2.len() - 1 implies composed_next(tr2[i], tr2[i + 1]) by {
        if i < tr.len() - 1 {
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == tr[i + 1]);
            assert(composed_next(tr[i], tr[i + 1]));
        } else {
            assert(i == tr.len() - 1);
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == e);
            assert(composed_step(d, e, s));
        }
    }
    assert(composed_segment(tr2));
    assert(tr2[tr2.len() - 1] == e);
}

pub proof fn lemma_composed_reachable_step(pre: Composed, post: Composed, s: ComposedStep)
    requires
        composed_reachable(pre),
        composed_step(pre, post, s),
    ensures
        composed_reachable(post),
{
    let tr = choose|tr: Seq<Composed>| composed_valid_execution(tr) && tr[tr.len() - 1] == pre;
    let tr2 = tr.push(post);
    assert(tr2.len() == tr.len() + 1);
    assert(tr2[0] == tr[0]);
    // Same multi-trigger as `composed_valid_execution` itself; see
    // `crate::proofs::invariant::lemma_reachable_step`.
    assert forall|i: int|
        #![trigger tr2[i], tr2[i + 1]]
        0 <= i < tr2.len() - 1 implies composed_next(tr2[i], tr2[i + 1]) by {
        if i < tr.len() - 1 {
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == tr[i + 1]);
            assert(composed_next(tr[i], tr[i + 1]));
        } else {
            assert(i == tr.len() - 1);
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == post);
            assert(composed_step(pre, post, s));
        }
    }
    assert(composed_valid_execution(tr2));
    assert(tr2[tr2.len() - 1] == post);
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
        let j = i - 1;
        lemma_composed_execution_inv(tr, j);
        // Phrased as `tr[j], tr[j + 1]` rather than `tr[i - 1], tr[i]` so that
        // both halves of `composed_valid_execution`'s multi-trigger are present
        // as terms; `tr[i]` alone does not match `tr[j + 1]` syntactically.
        assert(composed_next(tr[j], tr[j + 1]));
        assert(tr[j + 1] == tr[i]);
        lemma_composed_next_preserves_inv(tr[j], tr[i]);
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
        post.seized == pre.seized,
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
        post.seized == pre.seized,
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
