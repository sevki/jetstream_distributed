//! Adversarial scenarios.
//!
//! These are machine-checked *executions*, not tests: each one constructs a
//! concrete sequence of system states, proves that every step is a legal
//! protocol transition, and then proves the safety property of interest at the
//! end.
//!
//! Covered here:
//!
//! * a returning stale owner (the headline scenario);
//! * duplicated / replayed messages;
//! * a stale `Grant` arriving after the epoch moved on;
//! * an ownership transfer interrupted midway;
//! * crash and stale-node recovery.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::invariant::*;
use crate::transfer::*;

verus! {

/// **The headline scenario.**
///
/// ```text
/// A owns X @ epoch 41
/// transfer / recovery occurs
/// B owns X @ epoch 42
/// A returns believing it owns X @ epoch 41
/// ```
///
/// The execution built below is:
///
/// ```text
/// init                    X: Unowned(41, A)
/// IssueGrant(X)           network += Grant(X, A, 41)
/// Acquire(X, A)           X: Owned(A, 41)            issued += Token(X, 41, A)
/// BeginTransfer(X, A, B)  X: Transferring(A, B, 41, 42)
/// HandleRevoke(X, A)      network += Released(X, A, 42)
/// CompleteRelease(X)      X: Unowned(42, B)          network += Grant(X, B, 42)
/// Crash(A)                A goes away, still holding Token(X, 41, A)
/// Acquire(X, B)           X: Owned(B, 42)            issued += Token(X, 42, B)
/// Recover(A)              A comes back, still holding Token(X, 41, A)
/// Replay(Grant(X, A, 41)) A's stale grant is redelivered
/// ```
///
/// and in the final state A still physically holds its epoch-41 token, yet has
/// no authority whatsoever.
pub proof fn scenario_stale_owner_returns(x: ActorId, a: NodeId, b: NodeId)
    requires
        a != b,
    ensures
        exists|sys: System|
            {
                &&& reachable(sys)
                &&& #[trigger] sys.issued.contains(Token { actor: x, epoch: 41, holder: a })
                &&& !token_authorized(sys, Token { actor: x, epoch: 41, holder: a })
                &&& !can_mutate(sys, x, a, 41)
                &&& can_mutate(sys, x, b, 42)
            },
{
    let nodes = Set::<NodeId>::empty().insert(a).insert(b);
    let stale = Token { actor: x, epoch: 41, holder: a };
    let grant_41 = Message::Grant { actor: x, to: a, epoch: 41 };

    // --- initial state -----------------------------------------------------
    let s0 = System {
        actors: Map::<ActorId, OwnershipState>::empty().insert(
            x,
            OwnershipState::Unowned { epoch: 41, intended_owner: a },
        ),
        nodes: nodes,
        live: nodes,
        issued: Set::<Token>::empty(),
        network: Set::<Message>::empty(),
    };
    assert(s0.actors.contains_key(x));
    assert(s0.actors[x] == (OwnershipState::Unowned { epoch: 41, intended_owner: a }));
    assert(s0.nodes.contains(a));
    assert(s0.nodes.contains(b));
    assert(init(s0));
    lemma_reachable_init(s0);

    // --- the coordinator publishes the grant for epoch 41 ------------------
    let s1 = System {
        actors: s0.actors,
        nodes: s0.nodes,
        live: s0.live,
        issued: s0.issued,
        network: s0.network.insert(grant_41),
    };
    assert(step(s0, s1, Step::IssueGrant { actor: x }));
    lemma_reachable_step(s0, s1, Step::IssueGrant { actor: x });

    // --- A takes ownership at epoch 41 -------------------------------------
    let s2 = System {
        actors: s1.actors.insert(x, OwnershipState::Owned { owner: a, epoch: 41 }),
        nodes: s1.nodes,
        live: s1.live,
        issued: s1.issued.insert(stale),
        network: s1.network,
    };
    assert(s1.live.contains(a));
    assert(s1.network.contains(grant_41));
    assert(step(s1, s2, Step::Acquire { actor: x, node: a }));
    lemma_reachable_step(s1, s2, Step::Acquire { actor: x, node: a });

    // --- handover to B begins; A is fenced out immediately -----------------
    let revoke = Message::Revoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 };
    let s3 = System {
        actors: s2.actors.insert(
            x,
            OwnershipState::Transferring { from: a, to: b, old_epoch: 41, new_epoch: 42 },
        ),
        nodes: s2.nodes,
        live: s2.live,
        issued: s2.issued,
        network: s2.network.insert(revoke),
    };
    assert(s2.actors[x] == (OwnershipState::Owned { owner: a, epoch: 41 }));
    assert(s2.nodes.contains(b));
    assert(step(s2, s3, Step::BeginTransfer { actor: x, from: a, to: b }));
    lemma_reachable_step(s2, s3, Step::BeginTransfer { actor: x, from: a, to: b });
    assert(!may_mutate(s3.actors[x], a, 41));

    // --- A acknowledges the revocation -------------------------------------
    let released = Message::Released { actor: x, from: a, new_epoch: 42 };
    let s4 = System {
        actors: s3.actors,
        nodes: s3.nodes,
        live: s3.live,
        issued: s3.issued,
        network: s3.network.insert(released),
    };
    assert(s3.live.contains(a));
    assert(s3.network.contains(revoke));
    assert(step(
        s3,
        s4,
        Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
    ));
    lemma_reachable_step(
        s3,
        s4,
        Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
    );

    // --- the actor becomes unowned at epoch 42, B is granted it ------------
    let grant_42 = Message::Grant { actor: x, to: b, epoch: 42 };
    let s5 = System {
        actors: s4.actors.insert(x, OwnershipState::Unowned { epoch: 42, intended_owner: b }),
        nodes: s4.nodes,
        live: s4.live,
        issued: s4.issued,
        network: s4.network.insert(grant_42),
    };
    assert(s4.actors[x] == (OwnershipState::Transferring {
        from: a,
        to: b,
        old_epoch: 41,
        new_epoch: 42,
    }));
    assert(s4.network.contains(released));
    assert(step(s4, s5, Step::CompleteRelease { actor: x }));
    lemma_reachable_step(s4, s5, Step::CompleteRelease { actor: x });

    // --- A crashes, still physically holding Token(X, 41, A) ---------------
    let s6 = System {
        actors: s5.actors,
        nodes: s5.nodes,
        live: s5.live.remove(a),
        issued: s5.issued,
        network: s5.network,
    };
    assert(s5.live.contains(a));
    assert(step(s5, s6, Step::Crash { node: a }));
    lemma_reachable_step(s5, s6, Step::Crash { node: a });
    assert(s6.issued.contains(stale));

    // --- B takes ownership at epoch 42 -------------------------------------
    let s7 = System {
        actors: s6.actors.insert(x, OwnershipState::Owned { owner: b, epoch: 42 }),
        nodes: s6.nodes,
        live: s6.live,
        issued: s6.issued.insert(Token { actor: x, epoch: 42, holder: b }),
        network: s6.network,
    };
    assert(s6.live.contains(b));
    assert(s6.actors[x] == (OwnershipState::Unowned { epoch: 42, intended_owner: b }));
    assert(s6.network.contains(grant_42));
    assert(step(s6, s7, Step::Acquire { actor: x, node: b }));
    lemma_reachable_step(s6, s7, Step::Acquire { actor: x, node: b });

    // --- A comes back, still believing it owns X at epoch 41 ---------------
    let s8 = System {
        actors: s7.actors,
        nodes: s7.nodes,
        live: s7.live.insert(a),
        issued: s7.issued,
        network: s7.network,
    };
    assert(s7.nodes.contains(a));
    assert(!s7.live.contains(a));
    assert(step(s7, s8, Step::Recover { node: a }));
    lemma_reachable_step(s7, s8, Step::Recover { node: a });

    // --- and its stale grant is redelivered for good measure ---------------
    let s9 = System {
        actors: s8.actors,
        nodes: s8.nodes,
        live: s8.live,
        issued: s8.issued,
        network: s8.network.insert(grant_41),
    };
    assert(s8.network.contains(grant_41));
    assert(step(s8, s9, Step::Replay { msg: grant_41 }));
    lemma_reachable_step(s8, s9, Step::Replay { msg: grant_41 });

    // --- the payoff --------------------------------------------------------
    assert(s9.actors[x] == (OwnershipState::Owned { owner: b, epoch: 42 }));
    assert(current_epoch(s9.actors[x]) == 42);
    assert(s9.issued.contains(stale));
    assert(!may_mutate(s9.actors[x], a, 41));
    assert(!token_authorized(s9, stale));
    assert(!can_mutate(s9, x, a, 41));
    assert(can_mutate(s9, x, b, 42));
    assert(reachable(s9));
}

/// A stale `Grant` cannot resurrect a superseded epoch: if the actor has moved
/// past `e`, no `Acquire` can hand out authority at `e`, no matter how many
/// copies of the old grant are floating around.
pub proof fn theorem_stale_grant_cannot_be_used(
    pre: System,
    post: System,
    a: ActorId,
    n: NodeId,
    e: Epoch,
)
    requires
        pre.actors.contains_key(a),
        current_epoch(pre.actors[a]) > e,
        tr_acquire(pre, post, a, n),
    ensures
        !may_mutate(post.actors[a], n, e),
        !token_authorized(post, Token { actor: a, epoch: e, holder: n }),
{
    match pre.actors[a] {
        OwnershipState::Unowned { epoch, intended_owner } => {
            assert(epoch > e);
            assert(post.actors[a] == (OwnershipState::Owned { owner: n, epoch: epoch }));
        },
        _ => {
            assert(false);
        },
    }
}

/// Message duplication, reordering and delay cannot change ownership on their
/// own: every purely network-level step leaves `actors` and `issued` untouched.
pub proof fn theorem_network_steps_cannot_change_ownership(pre: System, post: System, s: Step)
    requires
        step(pre, post, s),
        s is Replay || s is HandleRevoke || s is IssueGrant || s is Stutter,
    ensures
        post.actors == pre.actors,
        post.issued == pre.issued,
{
    match s {
        Step::Replay { msg } => {},
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } => {},
        Step::IssueGrant { actor } => {
            match pre.actors[actor] {
                OwnershipState::Unowned { epoch, intended_owner } => {},
                _ => {
                    assert(false);
                },
            }
        },
        Step::Stutter => {},
        _ => {
            assert(false);
        },
    }
}

/// Crash and recovery cannot change ownership either: a node that crashes keeps
/// its tokens, and a node that comes back gets no new authority from the fact
/// of coming back.
pub proof fn theorem_crash_recovery_cannot_change_ownership(pre: System, post: System, s: Step)
    requires
        step(pre, post, s),
        s is Crash || s is Recover,
    ensures
        post.actors == pre.actors,
        post.issued == pre.issued,
{
    match s {
        Step::Crash { node } => {},
        Step::Recover { node } => {},
        _ => {
            assert(false);
        },
    }
}

/// An interrupted transfer leaves nobody with authority, and burns the epoch
/// that the interrupted handover had allocated.
pub proof fn scenario_interrupted_transfer(
    pre: System,
    post: System,
    x: ActorId,
    a: NodeId,
    b: NodeId,
    e: Epoch,
)
    requires
        inv(pre),
        pre.actors.contains_key(x),
        pre.actors[x] == (OwnershipState::Transferring {
            from: a,
            to: b,
            old_epoch: e,
            new_epoch: e + 1,
        }),
        step(pre, post, Step::AbortTransfer { actor: x }),
    ensures
        inv(post),
        post.actors[x] == (OwnershipState::Unowned { epoch: e + 2, intended_owner: a }),
        !can_mutate(post, x, a, e),
        !can_mutate(post, x, b, e + 1),
        current_epoch(post.actors[x]) > current_epoch(pre.actors[x]),
{
    lemma_step_preserves_inv(pre, post, Step::AbortTransfer { actor: x });
}

// ---------------------------------------------------------------------------
// Fabricated `Released` messages
// ---------------------------------------------------------------------------

/// **`CompleteRelease` needs the `Released` that matches the live handover.**
///
/// `tr_handle_revoke` is deliberately permissive: it requires only that *some*
/// `Revoke` for the actor is on the never-shrinking network and that the target
/// is live. It does not check that the actor is currently `Transferring`, nor
/// that `target` is its owner, so any live node can manufacture a `Released`
/// for any `Revoke` ever sent, however ancient.
///
/// This theorem is the first half of why that is harmless. The only transition
/// that consumes a `Released` is `CompleteRelease`, and it re-reads the actor's
/// *current* state: so if it fires at all, the actor is `Transferring` right
/// now, and the message that enabled it names exactly that handover's `from`
/// and `new_epoch`. A `Released` naming anything else is inert.
pub proof fn theorem_complete_release_needs_the_matching_released(
    pre: System,
    post: System,
    a: ActorId,
)
    requires
        step(pre, post, Step::CompleteRelease { actor: a }),
    ensures
        pre.actors.contains_key(a),
        is_transferring(pre.actors[a]),
        exists|from: NodeId, to: NodeId, old_epoch: Epoch, new_epoch: Epoch|
            {
                &&& pre.actors[a] == (OwnershipState::Transferring {
                    from: from,
                    to: to,
                    old_epoch: old_epoch,
                    new_epoch: new_epoch,
                })
                &&& #[trigger] pre.network.contains(
                    Message::Released { actor: a, from: from, new_epoch: new_epoch },
                )
            },
{
    assert(tr_complete_release(pre, post, a));
    match pre.actors[a] {
        OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {
            assert(pre.network.contains(
                Message::Released { actor: a, from: from, new_epoch: new_epoch },
            ));
        },
        _ => {
            assert(false);
        },
    }
}

/// **The outcome of `CompleteRelease` is fixed by the actor's state, not by the
/// message.**
///
/// The second half. Even granting that some matching `Released` exists, the
/// epoch the actor lands on is read from the live `Transferring` record, not
/// taken from the message. So a fabricated `Released` cannot steer the handover
/// anywhere: at most it can let a handover that was already in progress finish
/// slightly earlier than the real acknowledgement would have.
///
/// Together with the freshness of `new_epoch` — no epoch is ever revisited, by
/// `proofs::properties::theorem_stale_stays_stale` — this is the whole reason
/// `tr_handle_revoke` can afford to be as permissive as it is.
pub proof fn theorem_complete_release_outcome_is_fixed_by_state(
    pre: System,
    post: System,
    a: ActorId,
    from: NodeId,
    to: NodeId,
    old_epoch: Epoch,
    new_epoch: Epoch,
)
    requires
        step(pre, post, Step::CompleteRelease { actor: a }),
        pre.actors.contains_key(a),
        pre.actors[a] == (OwnershipState::Transferring {
            from: from,
            to: to,
            old_epoch: old_epoch,
            new_epoch: new_epoch,
        }),
    ensures
        post.actors[a] == (OwnershipState::Unowned { epoch: new_epoch, intended_owner: to }),
        current_epoch(post.actors[a]) == new_epoch,
        forall|n: NodeId| !(#[trigger] may_mutate(post.actors[a], n, new_epoch)),
{
    assert(tr_complete_release(pre, post, a));
}

} // verus!
