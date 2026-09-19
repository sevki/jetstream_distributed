//! Additional verified properties of the ownership model.
//!
//! These fall into three groups:
//!
//! * **Structural facts the documentation asserts but nothing proved** — that
//!   `issued` and `network` never shrink, and that the actor domain is constant.
//!   Those are load-bearing for the failure model, so they should be theorems
//!   rather than comments.
//! * **Temporal properties**, quantified over whole executions rather than
//!   single states: ownership at a given epoch never changes hands, a stale
//!   epoch stays stale forever, and an epoch advances by at most one per step.
//! * **Authority is always backed by a capability** — a node that may mutate
//!   provably holds an issued token for exactly that `(actor, epoch)`.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::composed::*;
use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::fencing::*;
use crate::proofs::invariant::*;
use crate::proofs::transfer::*;
use crate::raymond::*;
use crate::transfer::*;

verus! {

// ---------------------------------------------------------------------------
// Structural monotonicity
// ---------------------------------------------------------------------------

/// **Issued tokens never disappear.** A crash, a partition or a recovery cannot
/// retract a capability that was handed out - which is exactly why stale tokens
/// have to be fenced rather than revoked.
pub proof fn theorem_issued_monotone(pre: System, post: System, s: Step)
    requires
        step(pre, post, s),
    ensures
        forall|t: Token| #[trigger] pre.issued.contains(t) ==> post.issued.contains(t),
{
    match s {
        Step::Acquire { actor, node } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::BeginTransfer { actor, from, to } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::CompleteRelease { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::AbortTransfer { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::RevokeOwner { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::ReassignUnowned { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::IssueGrant { actor } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {},
        Step::Crash { node } => {},
        Step::Recover { node } => {},
        Step::Replay { msg } => {},
        Step::Stutter => {},
    }
}

/// **Sent messages never disappear.** This is what makes duplication,
/// reordering and unbounded delay free in the model: nothing ever removes a
/// message, so anything sent stays deliverable forever.
pub proof fn theorem_network_monotone(pre: System, post: System, s: Step)
    requires
        step(pre, post, s),
    ensures
        forall|m: Message| #[trigger] pre.network.contains(m) ==> post.network.contains(m),
{
    match s {
        Step::Acquire { actor, node } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::BeginTransfer { actor, from, to } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::CompleteRelease { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::AbortTransfer { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::RevokeOwner { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::ReassignUnowned { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::IssueGrant { actor } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {},
        Step::Crash { node } => {},
        Step::Recover { node } => {},
        Step::Replay { msg } => {},
        Step::Stutter => {},
    }
}

/// **The set of actors is constant.** No transition creates or destroys an
/// actor, so every claim quantified over actors covers the same population at
/// every point in an execution.
pub proof fn theorem_actor_domain_constant(pre: System, post: System, s: Step)
    requires
        step(pre, post, s),
    ensures
        forall|a: ActorId| #[trigger] post.actors.contains_key(a) <==> pre.actors.contains_key(a),
{
    match s {
        Step::Acquire { actor, node } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::BeginTransfer { actor, from, to } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::CompleteRelease { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::AbortTransfer { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::RevokeOwner { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::ReassignUnowned { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::IssueGrant { actor } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {},
        Step::Crash { node } => {},
        Step::Recover { node } => {},
        Step::Replay { msg } => {},
        Step::Stutter => {},
    }
}

// ---------------------------------------------------------------------------
// Epoch behaviour
// ---------------------------------------------------------------------------

/// **An epoch advances by at most one per transition.** Combined with
/// monotonicity this pins the epoch sequence down completely: it is
/// non-decreasing and never skips a generation.
/// **The node population is constant.** No transition creates or destroys a
/// node; `Crash` and `Recover` move nodes in and out of `live`, never out of
/// `nodes`.
pub proof fn theorem_node_domain_constant(pre: System, post: System, s: Step)
    requires
        step(pre, post, s),
    ensures
        post.nodes == pre.nodes,
{
    match s {
        Step::Acquire { actor, node } => {},
        Step::BeginTransfer { actor, from, to } => {},
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {},
        Step::CompleteRelease { actor } => {},
        Step::AbortTransfer { actor } => {},
        Step::RevokeOwner { actor, next } => {},
        Step::ReassignUnowned { actor, next } => {},
        Step::IssueGrant { actor } => {},
        Step::Crash { node } => {},
        Step::Recover { node } => {},
        Step::Replay { msg } => {},
        Step::Stutter => {},
    }
}

pub proof fn theorem_epoch_increases_by_at_most_one(
    pre: System,
    post: System,
    s: Step,
    a: ActorId,
)
    requires
        step(pre, post, s),
        pre.actors.contains_key(a),
    ensures
        post.actors.contains_key(a),
        current_epoch(post.actors[a]) <= current_epoch(pre.actors[a]) + 1,
{
    lemma_step_epoch_monotone(pre, post, s, a);
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

/// Leaving an `Owned` state always burns the epoch: if the actor is still at
/// the same epoch after a step, it is still in exactly the same `Owned` state.
pub proof fn lemma_owned_epoch_frozen(
    pre: System,
    post: System,
    s: Step,
    a: ActorId,
    n: NodeId,
    e: Epoch,
)
    requires
        step(pre, post, s),
        pre.actors.contains_key(a),
        pre.actors[a] == (OwnershipState::Owned { owner: n, epoch: e }),
        current_epoch(post.actors[a]) == e,
    ensures
        post.actors[a] == pre.actors[a],
{
    match s {
        Step::Acquire { actor, node } => {
            if actor == a {
                assert(false);
            }
        },
        Step::BeginTransfer { actor, from, to } => {
            if actor == a {
                assert(current_epoch(post.actors[a]) == e + 1);
                assert(false);
            }
        },
        Step::CompleteRelease { actor } => {
            if actor == a {
                assert(false);
            }
        },
        Step::AbortTransfer { actor } => {
            if actor == a {
                assert(false);
            }
        },
        Step::RevokeOwner { actor, next } => {
            if actor == a {
                assert(current_epoch(post.actors[a]) == e + 1);
                assert(false);
            }
        },
        Step::ReassignUnowned { actor, next } => {
            if actor == a {
                assert(false);
            }
        },
        Step::IssueGrant { actor } => {
            if actor == a {
                assert(false);
            }
        },
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {},
        Step::Crash { node } => {},
        Step::Recover { node } => {},
        Step::Replay { msg } => {},
        Step::Stutter => {},
    }
}

/// **Ownership at a given epoch is final.** Once an actor is owned by `n` at
/// epoch `e`, every later state of the execution that is still at epoch `e` is
/// still owned by `n` at `e`. Ownership of a generation never changes hands -
/// a handover *must* burn the epoch.
pub proof fn theorem_ownership_at_an_epoch_is_final(
    tr: Seq<System>,
    i: int,
    j: int,
    a: ActorId,
    n: NodeId,
    e: Epoch,
)
    requires
        valid_execution(tr),
        0 <= i <= j < tr.len(),
        tr[i].actors.contains_key(a),
        tr[i].actors[a] == (OwnershipState::Owned { owner: n, epoch: e }),
        current_epoch(tr[j].actors[a]) == e,
    ensures
        tr[j].actors.contains_key(a),
        tr[j].actors[a] == (OwnershipState::Owned { owner: n, epoch: e }),
    decreases j - i,
{
    if i == j {
    } else {
        let cur = tr[i];
        let nxt = tr[i + 1];
        assert(next(cur, nxt));
        let s = choose|s: Step| step(cur, nxt, s);
        lemma_step_epoch_monotone(cur, nxt, s, a);
        theorem_epoch_monotone_execution(tr, i + 1, j, a);
        assert(current_epoch(tr[i + 1].actors[a]) == e);
        lemma_owned_epoch_frozen(cur, nxt, s, a, n, e);
        theorem_ownership_at_an_epoch_is_final(tr, i + 1, j, a, n, e);
    }
}

/// **An epoch determines its owner.** Any two points of an execution at which
/// the actor is owned at the same epoch have the same owner.
pub proof fn theorem_epoch_determines_owner(
    tr: Seq<System>,
    i: int,
    j: int,
    a: ActorId,
    n1: NodeId,
    n2: NodeId,
    e: Epoch,
)
    requires
        valid_execution(tr),
        0 <= i <= j < tr.len(),
        tr[i].actors.contains_key(a),
        tr[i].actors[a] == (OwnershipState::Owned { owner: n1, epoch: e }),
        tr[j].actors[a] == (OwnershipState::Owned { owner: n2, epoch: e }),
    ensures
        n1 == n2,
{
    assert(current_epoch(tr[j].actors[a]) == e);
    theorem_ownership_at_an_epoch_is_final(tr, i, j, a, n1, e);
}

/// **A stale epoch stays stale.** Once an actor has advanced past `e`, no later
/// point of the execution ever accepts `e` again - staleness is permanent, so a
/// node that was fenced out can never be fenced back in by waiting.
pub proof fn theorem_stale_stays_stale(tr: Seq<System>, i: int, j: int, a: ActorId, e: Epoch)
    requires
        valid_execution(tr),
        0 <= i <= j < tr.len(),
        tr[i].actors.contains_key(a),
        is_stale(tr[i].actors[a], e),
    ensures
        tr[j].actors.contains_key(a),
        is_stale(tr[j].actors[a], e),
        !valid_fence(tr[j].actors[a], e),
        forall|n: NodeId| !may_mutate(tr[j].actors[a], n, e),
{
    theorem_epoch_monotone_execution(tr, i, j, a);
    assert forall|n: NodeId| !may_mutate(tr[j].actors[a], n, e) by {
        lemma_stale_epoch_cannot_mutate(tr[j].actors[a], n, e);
    }
}

// ---------------------------------------------------------------------------
// Authority is always backed by a capability
// ---------------------------------------------------------------------------

/// Every node that may mutate an actor holds an issued token for exactly that
/// `(actor, epoch)`.
pub open spec fn inv_authority_backed(sys: System) -> bool {
    forall|a: ActorId, n: NodeId, e: Epoch|
        #[trigger] can_mutate(sys, a, n, e) ==> sys.issued.contains(
            Token { actor: a, epoch: e, holder: n },
        )
}

/// Initial states satisfy it vacuously - nothing is owned.
pub proof fn lemma_authority_backed_init(sys: System)
    requires
        init(sys),
    ensures
        inv_authority_backed(sys),
{
    assert forall|a: ActorId, n: NodeId, e: Epoch| can_mutate(sys, a, n, e) implies sys.issued.contains(
        Token { actor: a, epoch: e, holder: n },
    ) by {
        assert(starts_unowned(sys.actors[a]));
        assert(false);
    }
}

/// Every transition preserves it: the only step that creates authority is
/// `Acquire`, and `Acquire` mints the matching token in the same step.
pub proof fn lemma_authority_backed_step(pre: System, post: System, s: Step)
    requires
        inv_authority_backed(pre),
        step(pre, post, s),
    ensures
        inv_authority_backed(post),
{
    theorem_issued_monotone(pre, post, s);
    theorem_actor_domain_constant(pre, post, s);
    assert forall|a: ActorId, n: NodeId, e: Epoch| can_mutate(post, a, n, e) implies post.issued.contains(
        Token { actor: a, epoch: e, holder: n },
    ) by {
        assert(pre.actors.contains_key(a));
        if !may_mutate(pre.actors[a], n, e) {
            theorem_ownership_only_via_acquire(pre, post, s, a, n, e);
            assert(s == (Step::Acquire { actor: a, node: n }));
            assert(pre.actors[a] == (OwnershipState::Unowned { epoch: e, intended_owner: n }));
            assert(post.issued == pre.issued.insert(Token { actor: a, epoch: e, holder: n }));
        } else {
            assert(can_mutate(pre, a, n, e));
            assert(pre.issued.contains(Token { actor: a, epoch: e, holder: n }));
        }
    }
}

/// Lifted along an execution.
pub proof fn lemma_authority_backed_execution(tr: Seq<System>, i: int)
    requires
        valid_execution(tr),
        0 <= i < tr.len(),
    ensures
        inv_authority_backed(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_authority_backed_init(tr[0]);
    } else {
        let j = i - 1;
        lemma_authority_backed_execution(tr, j);
        // `tr[j + 1]`, not `tr[i]`: `valid_execution`'s multi-trigger needs both
        // adjacent terms in the shape it names.
        assert(next(tr[j], tr[j + 1]));
        let prev = tr[j];
        let cur = tr[i];
        assert(tr[j + 1] == cur);
        assert(next(prev, cur));
        let s = choose|s: Step| step(prev, cur, s);
        lemma_authority_backed_step(prev, cur, s);
    }
}

/// **No authority without a capability.** In every reachable state, a node that
/// may mutate an actor demonstrably holds an issued token for that exact
/// `(actor, epoch)`. Authority cannot exist without the capability that
/// conferred it.
pub proof fn theorem_no_authority_without_token(sys: System, a: ActorId, n: NodeId, e: Epoch)
    requires
        reachable(sys),
        can_mutate(sys, a, n, e),
    ensures
        sys.issued.contains(Token { actor: a, epoch: e, holder: n }),
        token_authorized(sys, Token { actor: a, epoch: e, holder: n }),
{
    let tr = choose|tr: Seq<System>| valid_execution(tr) && tr[tr.len() - 1] == sys;
    lemma_authority_backed_execution(tr, tr.len() - 1);
}

// ---------------------------------------------------------------------------
// Composed machine
// ---------------------------------------------------------------------------

/// **Epoch monotonicity survives composition.** No composed transition - not
/// routing, not a token transfer, not an acquisition - decreases the actor's
/// epoch.
pub proof fn theorem_composed_epoch_monotone(pre: Composed, post: Composed, s: ComposedStep)
    requires
        composed_step(pre, post, s),
        pre.own.actors.contains_key(pre.actor),
    ensures
        post.own.actors.contains_key(post.actor),
        current_epoch(post.own.actors[post.actor]) >= current_epoch(pre.own.actors[pre.actor]),
{
    match s {
        ComposedStep::Ray { ray_step } => {},
        ComposedStep::PassToken { node, head } => {},
        // A seizure rewrites routing state only; `own` is untouched.
        ComposedStep::SeizeToken { from, to } => {},
        ComposedStep::Own { own_step } => {
            lemma_step_epoch_monotone(pre.own, post.own, own_step, pre.actor);
        },
        ComposedStep::AcquireUnderToken { node } => {
            let acq = Step::Acquire { actor: pre.actor, node: node };
            assert(step(pre.own, post.own, acq));
            lemma_step_epoch_monotone(pre.own, post.own, acq, pre.actor);
        },
    }
}

} // verus!
