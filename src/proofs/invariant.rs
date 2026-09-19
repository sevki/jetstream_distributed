//! Inductive invariant: `init ==> inv`, `inv /\ next ==> inv`, and therefore
//! `reachable ==> inv`.
//!
//! The individual cases are factored into three small, reusable lemmas:
//!
//! * [`lemma_inv_frame`]           - steps that touch neither actors nor tokens;
//! * [`lemma_inv_epoch_bump`]      - steps that strictly advance an epoch;
//! * [`lemma_inv_same_epoch_unowned`] - steps that keep the epoch but stay out
//!                                   of `Owned`;
//! * [`lemma_inv_acquire`]         - the only step that issues a token.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;

verus! {

/// Steps that change neither the ownership states nor the issued tokens cannot
/// break an invariant that only talks about those two things.
pub proof fn lemma_inv_frame(pre: System, post: System)
    requires
        inv(pre),
        post.actors == pre.actors,
        post.issued == pre.issued,
    ensures
        inv(post),
{
}

/// A step that replaces one actor's state with a state at a *strictly greater*
/// epoch preserves the invariant: every previously issued token is now strictly
/// stale for that actor, so the "current epoch" clause becomes vacuous.
pub proof fn lemma_inv_epoch_bump(
    pre: System,
    post: System,
    a: ActorId,
    s_new: OwnershipState,
)
    requires
        inv(pre),
        pre.actors.contains_key(a),
        post.actors == pre.actors.insert(a, s_new),
        post.issued == pre.issued,
        current_epoch(s_new) > current_epoch(pre.actors[a]),
    ensures
        inv(post),
{
    assert forall|t: Token| post.issued.contains(t) implies token_inv(post, t) by {
        assert(pre.issued.contains(t));
        assert(token_inv(pre, t));
        if t.actor == a {
            assert(post.actors[t.actor] == s_new);
            assert(t.epoch <= current_epoch(pre.actors[a]));
        } else {
            assert(post.actors[t.actor] == pre.actors[t.actor]);
        }
    }
}

/// A step that keeps an actor's epoch but leaves it in a non-`Owned` state,
/// starting from a non-`Owned` state, preserves the invariant: no issued token
/// could have been sitting at the current epoch in the first place.
pub proof fn lemma_inv_same_epoch_unowned(
    pre: System,
    post: System,
    a: ActorId,
    s_new: OwnershipState,
)
    requires
        inv(pre),
        pre.actors.contains_key(a),
        post.actors == pre.actors.insert(a, s_new),
        post.issued == pre.issued,
        current_epoch(s_new) == current_epoch(pre.actors[a]),
        !is_owned(pre.actors[a]),
        !is_owned(s_new),
    ensures
        inv(post),
{
    assert forall|t: Token| post.issued.contains(t) implies token_inv(post, t) by {
        assert(pre.issued.contains(t));
        assert(token_inv(pre, t));
        if t.actor == a {
            assert(post.actors[t.actor] == s_new);
            assert(t.epoch <= current_epoch(pre.actors[a]));
            if t.epoch == current_epoch(s_new) {
                assert(is_owned_by(pre.actors[a], t.holder));
                assert(false);
            }
        } else {
            assert(post.actors[t.actor] == pre.actors[t.actor]);
        }
    }
}

/// No token can already exist at the current epoch of an unowned actor.
///
/// This is the fact that makes token issuance unique: `Acquire` is the only
/// transition that mints a token, and it mints it exactly at the epoch of an
/// `Unowned` actor.
pub proof fn lemma_no_token_at_unowned_epoch(sys: System, a: ActorId, e: Epoch, n: NodeId)
    requires
        inv(sys),
        sys.actors.contains_key(a),
        sys.actors[a] == (OwnershipState::Unowned { epoch: e, intended_owner: n }),
    ensures
        forall|t: Token| sys.issued.contains(t) && t.actor == a ==> t.epoch < e,
{
    assert forall|t: Token| sys.issued.contains(t) && t.actor == a implies t.epoch < e by {
        assert(token_inv(sys, t));
        assert(current_epoch(sys.actors[a]) == e);
        if t.epoch == e {
            assert(is_owned_by(sys.actors[a], t.holder));
            assert(false);
        }
    }
}

/// `Acquire` is the only token-minting step; it preserves the invariant and
/// cannot mint a second token for an `(actor, epoch)` pair.
pub proof fn lemma_inv_acquire(
    pre: System,
    post: System,
    a: ActorId,
    n: NodeId,
    e: Epoch,
)
    requires
        inv(pre),
        pre.actors.contains_key(a),
        pre.actors[a] == (OwnershipState::Unowned { epoch: e, intended_owner: n }),
        post.actors == pre.actors.insert(a, OwnershipState::Owned { owner: n, epoch: e }),
        post.issued == pre.issued.insert(Token { actor: a, epoch: e, holder: n }),
    ensures
        inv(post),
{
    let fresh = Token { actor: a, epoch: e, holder: n };
    lemma_no_token_at_unowned_epoch(pre, a, e, n);

    assert(post.actors[a] == (OwnershipState::Owned { owner: n, epoch: e }));
    assert(current_epoch(post.actors[a]) == e);

    assert forall|t: Token| post.issued.contains(t) implies token_inv(post, t) by {
        if t == fresh {
            assert(is_owned_by(post.actors[a], n));
        } else {
            assert(pre.issued.contains(t));
            assert(token_inv(pre, t));
            if t.actor == a {
                assert(t.epoch < e);
            } else {
                assert(post.actors[t.actor] == pre.actors[t.actor]);
            }
        }
    }

    assert forall|t1: Token, t2: Token|
        post.issued.contains(t1) && post.issued.contains(t2) && t1.actor == t2.actor && t1.epoch
            == t2.epoch implies t1 == t2 by {
        if t1 == fresh && t2 == fresh {
        } else if t1 == fresh {
            assert(pre.issued.contains(t2));
            assert(t2.actor == a);
            assert(t2.epoch < e);
            assert(false);
        } else if t2 == fresh {
            assert(pre.issued.contains(t1));
            assert(t1.actor == a);
            assert(t1.epoch < e);
            assert(false);
        } else {
            assert(pre.issued.contains(t1));
            assert(pre.issued.contains(t2));
        }
    }
}

/// Every transition preserves the system invariant.
pub proof fn lemma_step_preserves_inv(pre: System, post: System, s: Step)
    requires
        inv(pre),
        step(pre, post, s),
    ensures
        inv(post),
{
    match s {
        Step::Acquire { actor, node } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {
                    lemma_inv_acquire(pre, post, actor, node, epoch);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::BeginTransfer { actor, from, to } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {
                    let s_new = OwnershipState::Transferring {
                        from: from,
                        to: to,
                        old_epoch: epoch,
                        new_epoch: epoch + 1,
                    };
                    assert(current_epoch(s_new) == epoch + 1);
                    assert(current_epoch(pre.actors[actor]) == epoch);
                    lemma_inv_epoch_bump(pre, post, actor, s_new);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {
            lemma_inv_frame(pre, post);
        },
        Step::CompleteRelease { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {
                    let s_new = OwnershipState::Unowned { epoch: new_epoch, intended_owner: to };
                    assert(current_epoch(s_new) == new_epoch);
                    assert(current_epoch(pre.actors[actor]) == new_epoch);
                    assert(!is_owned(pre.actors[actor]));
                    assert(!is_owned(s_new));
                    lemma_inv_same_epoch_unowned(pre, post, actor, s_new);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::AbortTransfer { actor } => {
            match pre.actors[actor] {
                OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {
                    let s_new = OwnershipState::Unowned {
                        epoch: new_epoch + 1,
                        intended_owner: from,
                    };
                    assert(current_epoch(s_new) == new_epoch + 1);
                    assert(current_epoch(pre.actors[actor]) == new_epoch);
                    lemma_inv_epoch_bump(pre, post, actor, s_new);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::RevokeOwner { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Owned { owner, epoch } => {
                    let s_new = OwnershipState::Unowned { epoch: epoch + 1, intended_owner: next };
                    assert(current_epoch(s_new) == epoch + 1);
                    assert(current_epoch(pre.actors[actor]) == epoch);
                    lemma_inv_epoch_bump(pre, post, actor, s_new);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::ReassignUnowned { actor, next } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {
                    let s_new = OwnershipState::Unowned { epoch: epoch + 1, intended_owner: next };
                    assert(current_epoch(s_new) == epoch + 1);
                    assert(current_epoch(pre.actors[actor]) == epoch);
                    lemma_inv_epoch_bump(pre, post, actor, s_new);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::IssueGrant { actor } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {
                    lemma_inv_frame(pre, post);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Step::Crash { node } => {
            lemma_inv_frame(pre, post);
        },
        Step::Recover { node } => {
            lemma_inv_frame(pre, post);
        },
        Step::Replay { msg } => {
            lemma_inv_frame(pre, post);
        },
        Step::Stutter => {
            lemma_inv_frame(pre, post);
        },
    }
}

/// `next` preserves the invariant.
pub proof fn lemma_next_preserves_inv(pre: System, post: System)
    requires
        inv(pre),
        next(pre, post),
    ensures
        inv(post),
{
    let s = choose|s: Step| step(pre, post, s);
    lemma_step_preserves_inv(pre, post, s);
}

/// Initial states satisfy the invariant (vacuously: nothing has been issued).
pub proof fn lemma_init_inv(sys: System)
    requires
        init(sys),
    ensures
        inv(sys),
{
}

/// An initial state is reachable.
pub proof fn lemma_reachable_init(sys: System)
    requires
        init(sys),
    ensures
        reachable(sys),
{
    let tr = Seq::<System>::empty().push(sys);
    assert(tr.len() == 1);
    assert(tr[0] == sys);
    assert(valid_execution(tr));
    assert(tr[tr.len() - 1] == sys);
}

/// Reachability is closed under taking a step.
pub proof fn lemma_reachable_step(pre: System, post: System, s: Step)
    requires
        reachable(pre),
        step(pre, post, s),
    ensures
        reachable(post),
{
    let tr = choose|tr: Seq<System>| valid_execution(tr) && tr[tr.len() - 1] == pre;
    let tr2 = tr.push(post);
    assert(tr2.len() == tr.len() + 1);
    assert(tr2[0] == tr[0]);
    assert forall|i: int| 0 <= i < tr2.len() - 1 implies next(#[trigger] tr2[i], tr2[i + 1]) by {
        if i < tr.len() - 1 {
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == tr[i + 1]);
            assert(next(tr[i], tr[i + 1]));
        } else {
            assert(i == tr.len() - 1);
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == post);
            assert(step(pre, post, s));
        }
    }
    assert(valid_execution(tr2));
    assert(tr2[tr2.len() - 1] == post);
}

/// Every state of a valid execution satisfies the invariant.
pub proof fn lemma_execution_inv(tr: Seq<System>, i: int)
    requires
        valid_execution(tr),
        0 <= i < tr.len(),
    ensures
        inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_init_inv(tr[0]);
    } else {
        lemma_execution_inv(tr, i - 1);
        assert(next(tr[i - 1], tr[i]));
        lemma_next_preserves_inv(tr[i - 1], tr[i]);
    }
}

/// **Every reachable system state satisfies the invariant.**
pub proof fn theorem_reachable_inv(sys: System)
    requires
        reachable(sys),
    ensures
        inv(sys),
{
    let tr = choose|tr: Seq<System>| valid_execution(tr) && tr[tr.len() - 1] == sys;
    lemma_execution_inv(tr, tr.len() - 1);
}

} // verus!
