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

use crate::host::HostId;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::ownership::proofs::invariant::*;
use crate::ownership::transfer::*;

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
pub proof fn scenario_stale_owner_returns(x: ActorId, a: HostId, b: HostId)
    requires
        a != b,
    ensures
        // The whole run, with every step named.
        //
        // Exporting the crash, the recovery and the endpoint as three separate
        // existentials was not enough: nothing made them the *same* execution,
        // so an ordinary live handover could supply the endpoint while some
        // other run supplied the crash. The nine labels below are one run, and
        // they are the failure story - `Crash(A)` at index 5 between the
        // release and `B`'s acquisition, `Recover(A)` at 7, and the replay of
        // `A`'s epoch-41 grant at 8.
        exists|tr: Seq<OwnershipSystem>, labels: Seq<Step>|
            {
                &&& #[trigger] labelled_execution(tr, labels)
                &&& labels.len() == 9
                &&& labels[0] == (Step::IssueGrant { actor: x })
                &&& labels[1] == (Step::Acquire { actor: x, node: a })
                &&& labels[2] == (Step::BeginTransfer { actor: x, from: a, to: b })
                &&& labels[3] == (Step::HandleRevoke {
                    actor: x,
                    target: a,
                    old_epoch: 41,
                    new_epoch: 42,
                })
                &&& labels[4] == (Step::CompleteRelease { actor: x })
                &&& labels[5] == (Step::Crash { node: a })
                &&& labels[6] == (Step::Acquire { actor: x, node: b })
                &&& labels[7] == (Step::Recover { node: a })
                &&& labels[8] == (Step::Replay {
                    msg: Message::Grant { actor: x, to: a, epoch: 41 },
                })
                // The epochs, which the labels do not carry.
                &&& tr[2].actors[x] == (OwnershipState::Owned { owner: a, epoch: 41 })
                &&& tr[3].actors[x] == (OwnershipState::Transferring {
                    from: a,
                    to: b,
                    old_epoch: 41,
                    new_epoch: 42,
                })
                // `A` is live up to the crash and gone after it, and keeps its
                // epoch-41 token throughout.
                &&& tr[5].live.contains(a)
                &&& !tr[6].live.contains(a)
                &&& !tr[7].live.contains(a)
                &&& tr[8].live.contains(a)
                &&& tr[6].issued.contains(Token { actor: x, epoch: 41, holder: a })
                // And the headline: `A` is back, still physically holding its
                // epoch-41 token, with no authority at all, while `B` owns at
                // 42 - after `A`'s original grant has been redelivered to it.
                &&& tr[9].live.contains(a)
                &&& tr[9].issued.contains(Token { actor: x, epoch: 41, holder: a })
                &&& !token_authorized(tr[9], Token { actor: x, epoch: 41, holder: a })
                &&& !can_mutate(tr[9], x, a, 41)
                &&& can_mutate(tr[9], x, b, 42)
                &&& tr[9].network.contains(Message::Grant { actor: x, to: a, epoch: 41 })
            },
{
    let nodes = Set::<HostId>::empty().insert(a).insert(b);
    let stale = Token { actor: x, epoch: 41, holder: a };
    let grant_41 = Message::Grant { actor: x, to: a, epoch: 41 };

    // --- initial state -----------------------------------------------------
    let s0 = OwnershipSystem {
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
    let s1 = OwnershipSystem {
        actors: s0.actors,
        nodes: s0.nodes,
        live: s0.live,
        issued: s0.issued,
        network: s0.network.insert(grant_41),
    };
    assert(step(s0, s1, Step::IssueGrant { actor: x }));
    lemma_reachable_step(s0, s1, Step::IssueGrant { actor: x });

    // --- A takes ownership at epoch 41 -------------------------------------
    let s2 = OwnershipSystem {
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
    let s3 = OwnershipSystem {
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
    let s4 = OwnershipSystem {
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
    let s5 = OwnershipSystem {
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
    let s6 = OwnershipSystem {
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
    let s7 = OwnershipSystem {
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
    let s8 = OwnershipSystem {
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
    let s9 = OwnershipSystem {
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
    assert(s9.live.contains(a));

    // The run: nine states and the nine labels between them. Each `step` was
    // proved above; collecting them makes the scenario's evidence the run
    // rather than three endpoints that three different runs could supply.
    let tr = seq![s0, s1, s2, s3, s4, s5, s6, s7, s8, s9];
    let labels = seq![
        Step::IssueGrant { actor: x },
        Step::Acquire { actor: x, node: a },
        Step::BeginTransfer { actor: x, from: a, to: b },
        Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
        Step::CompleteRelease { actor: x },
        Step::Crash { node: a },
        Step::Acquire { actor: x, node: b },
        Step::Recover { node: a },
        Step::Replay { msg: grant_41 },
    ];
    assert(tr.len() == 10);
    assert(labels.len() == 9);
    assert(tr[0] == s0);
    assert(tr[1] == s1);
    assert(tr[2] == s2);
    assert(tr[3] == s3);
    assert(tr[4] == s4);
    assert(tr[5] == s5);
    assert(tr[6] == s6);
    assert(tr[7] == s7);
    assert(tr[8] == s8);
    assert(tr[9] == s9);
    assert(labels[0] == (Step::IssueGrant { actor: x }));
    assert(labels[1] == (Step::Acquire { actor: x, node: a }));
    assert(labels[2] == (Step::BeginTransfer { actor: x, from: a, to: b }));
    assert(labels[3] == (Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 }));
    assert(labels[4] == (Step::CompleteRelease { actor: x }));
    assert(labels[5] == (Step::Crash { node: a }));
    assert(labels[6] == (Step::Acquire { actor: x, node: b }));
    assert(labels[7] == (Step::Recover { node: a }));
    assert(labels[8] == (Step::Replay { msg: grant_41 }));
    assert forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() implies step(tr[i], tr[i + 1], labels[i]) by {
        if i == 0 {
            assert(step(s0, s1, Step::IssueGrant { actor: x }));
        } else if i == 1 {
            assert(step(s1, s2, Step::Acquire { actor: x, node: a }));
        } else if i == 2 {
            assert(step(s2, s3, Step::BeginTransfer { actor: x, from: a, to: b }));
        } else if i == 3 {
            assert(step(
                s3,
                s4,
                Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
            ));
        } else if i == 4 {
            assert(step(s4, s5, Step::CompleteRelease { actor: x }));
        } else if i == 5 {
            assert(step(s5, s6, Step::Crash { node: a }));
        } else if i == 6 {
            assert(step(s6, s7, Step::Acquire { actor: x, node: b }));
        } else if i == 7 {
            assert(step(s7, s8, Step::Recover { node: a }));
        } else {
            assert(i == 8);
            assert(step(s8, s9, Step::Replay { msg: grant_41 }));
        }
    }
    assert(run(tr, labels));
    assert(init(tr[0]));
    assert(labelled_execution(tr, labels));
}

/// A stale `Grant` cannot resurrect a superseded epoch: if the actor has moved
/// past `e`, no `Acquire` can hand out authority at `e`, no matter how many
/// copies of the old grant are floating around.
pub proof fn theorem_stale_grant_cannot_be_used(
    pre: OwnershipSystem,
    post: OwnershipSystem,
    a: ActorId,
    n: HostId,
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
pub proof fn theorem_network_steps_cannot_change_ownership(pre: OwnershipSystem, post: OwnershipSystem, s: Step)
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
pub proof fn theorem_crash_recovery_cannot_change_ownership(pre: OwnershipSystem, post: OwnershipSystem, s: Step)
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

/// **An interrupted transfer really happens.**
///
/// The step property below says what an `AbortTransfer` does *if* one occurs.
/// This says one occurs: it builds the execution
///
/// ```text
/// init                    X: Unowned(41, A)
/// IssueGrant(X)           network += Grant(X, A, 41)
/// Acquire(X, A)           X: Owned(A, 41)              issued += Token(X, 41, A)
/// BeginTransfer(X, A, B)  X: Transferring(A, B, 41, 42)
/// AbortTransfer(X)        X: Unowned(43, A)            network += Grant(X, A, 43)
/// ```
///
/// and exports the abort as a named step between reachable states. Without it,
/// the step property remains provable even if `AbortTransfer` were changed to
/// be always false - a conditional lemma about an unreachable transition.
pub proof fn scenario_interrupted_transfer(x: ActorId, a: HostId, b: HostId)
    requires
        a != b,
    ensures
        // The run, with every step named: the abort at index 3 follows the
        // `BeginTransfer` at index 2 that opened the very transfer it
        // interrupts.
        exists|tr: Seq<OwnershipSystem>, labels: Seq<Step>|
            {
                &&& #[trigger] labelled_execution(tr, labels)
                &&& labels.len() == 4
                &&& labels[0] == (Step::IssueGrant { actor: x })
                &&& labels[1] == (Step::Acquire { actor: x, node: a })
                &&& labels[2] == (Step::BeginTransfer { actor: x, from: a, to: b })
                &&& labels[3] == (Step::AbortTransfer { actor: x })
                &&& tr[3].actors[x] == (OwnershipState::Transferring {
                    from: a,
                    to: b,
                    old_epoch: 41,
                    new_epoch: 42,
                })
                &&& tr[4].actors[x] == (OwnershipState::Unowned {
                    epoch: 43,
                    intended_owner: a,
                })
                &&& !can_mutate(tr[4], x, a, 41)
                &&& !can_mutate(tr[4], x, b, 42)
                &&& tr[4].issued.contains(Token { actor: x, epoch: 41, holder: a })
            },
{
    let nodes = Set::<HostId>::empty().insert(a).insert(b);
    let stale = Token { actor: x, epoch: 41, holder: a };
    let grant_41 = Message::Grant { actor: x, to: a, epoch: 41 };

    let s0 = OwnershipSystem {
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
    assert(init(s0));
    lemma_reachable_init(s0);

    // 1. The coordinator offers X to A at epoch 41.
    let s1 = OwnershipSystem {
        actors: s0.actors,
        nodes: s0.nodes,
        live: s0.live,
        issued: s0.issued,
        network: s0.network.insert(grant_41),
    };
    assert(step(s0, s1, Step::IssueGrant { actor: x }));
    lemma_reachable_step(s0, s1, Step::IssueGrant { actor: x });

    // 2. A takes ownership at 41.
    let s2 = OwnershipSystem {
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

    // 3. A begins handing X to B. The epoch is burned immediately.
    let revoke = Message::Revoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 };
    let s3 = OwnershipSystem {
        actors: s2.actors.insert(
            x,
            OwnershipState::Transferring { from: a, to: b, old_epoch: 41, new_epoch: 42 },
        ),
        nodes: s2.nodes,
        live: s2.live,
        issued: s2.issued,
        network: s2.network.insert(revoke),
    };
    assert(s2.nodes.contains(b));
    assert(s2.actors[x] == (OwnershipState::Owned { owner: a, epoch: 41 }));
    assert(step(s2, s3, Step::BeginTransfer { actor: x, from: a, to: b }));
    lemma_reachable_step(s2, s3, Step::BeginTransfer { actor: x, from: a, to: b });

    // 4. The handover is interrupted. Recovery burns *another* epoch, so the
    //    epoch-42 grant that may still be in flight is stale on arrival.
    let s4 = OwnershipSystem {
        actors: s3.actors.insert(x, OwnershipState::Unowned { epoch: 43, intended_owner: a }),
        nodes: s3.nodes,
        live: s3.live,
        issued: s3.issued,
        network: s3.network.insert(Message::Grant { actor: x, to: a, epoch: 43 }),
    };
    assert(s3.actors[x] == (OwnershipState::Transferring {
        from: a,
        to: b,
        old_epoch: 41,
        new_epoch: 42,
    }));
    assert(step(s3, s4, Step::AbortTransfer { actor: x }));
    lemma_reachable_step(s3, s4, Step::AbortTransfer { actor: x });

    assert(s4.actors[x] == (OwnershipState::Unowned { epoch: 43, intended_owner: a }));
    assert(!may_mutate(s4.actors[x], a, 41));
    assert(!may_mutate(s4.actors[x], b, 42));
    assert(!can_mutate(s4, x, a, 41));
    assert(!can_mutate(s4, x, b, 42));
    assert(s4.issued.contains(stale));

    let tr = seq![s0, s1, s2, s3, s4];
    let labels = seq![
        Step::IssueGrant { actor: x },
        Step::Acquire { actor: x, node: a },
        Step::BeginTransfer { actor: x, from: a, to: b },
        Step::AbortTransfer { actor: x },
    ];
    assert(tr.len() == 5);
    assert(labels.len() == 4);
    assert(tr[0] == s0);
    assert(tr[1] == s1);
    assert(tr[2] == s2);
    assert(tr[3] == s3);
    assert(tr[4] == s4);
    assert(labels[0] == (Step::IssueGrant { actor: x }));
    assert(labels[1] == (Step::Acquire { actor: x, node: a }));
    assert(labels[2] == (Step::BeginTransfer { actor: x, from: a, to: b }));
    assert(labels[3] == (Step::AbortTransfer { actor: x }));
    assert forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() implies step(tr[i], tr[i + 1], labels[i]) by {
        if i == 0 {
            assert(step(s0, s1, Step::IssueGrant { actor: x }));
        } else if i == 1 {
            assert(step(s1, s2, Step::Acquire { actor: x, node: a }));
        } else if i == 2 {
            assert(step(s2, s3, Step::BeginTransfer { actor: x, from: a, to: b }));
        } else {
            assert(i == 3);
            assert(step(s3, s4, Step::AbortTransfer { actor: x }));
        }
    }
    assert(run(tr, labels));
    assert(init(tr[0]));
    assert(labelled_execution(tr, labels));
}

/// An interrupted transfer leaves nobody with authority, and burns the epoch
/// that the interrupted handover had allocated.
///
/// Named a theorem rather than a scenario, because it is one: it takes the
/// `Transferring` state and the `AbortTransfer` step as hypotheses rather than
/// constructing a reachable execution that contains them. Every other
/// `scenario_*` in this crate builds a run from `init`, so calling this one a
/// scenario claimed more than it delivers. It is not weaker for being a step
/// property - `theorem_reachable_inv` gives `inv` for every reachable state, so
/// it applies to all of them - but the name should say which it is.
pub proof fn theorem_interrupted_transfer_burns_the_epoch(
    pre: OwnershipSystem,
    post: OwnershipSystem,
    x: ActorId,
    a: HostId,
    b: HostId,
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
    pre: OwnershipSystem,
    post: OwnershipSystem,
    a: ActorId,
)
    requires
        step(pre, post, Step::CompleteRelease { actor: a }),
    ensures
        pre.actors.contains_key(a),
        is_transferring(pre.actors[a]),
        pre.network.contains(
            Message::Released {
                actor: a,
                from: transferring_from(pre.actors[a]),
                new_epoch: transferring_new_epoch(pre.actors[a]),
            },
        ),
{
    assert(tr_complete_release(pre, post, a));
    match pre.actors[a] {
        OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {
            assert(transferring_from(pre.actors[a]) == from);
            assert(transferring_new_epoch(pre.actors[a]) == new_epoch);
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
    pre: OwnershipSystem,
    post: OwnershipSystem,
    a: ActorId,
    from: HostId,
    to: HostId,
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
        forall|n: HostId| !(#[trigger] may_mutate(post.actors[a], n, new_epoch)),
{
    assert(tr_complete_release(pre, post, a));
}

} // verus!
