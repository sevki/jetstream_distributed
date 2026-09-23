//! The executable steps agree with the model.
//!
//! [`crate::ownership::steps`] holds small `u64`-valued functions that decide what a
//! server does with a request. This module is what makes them more than a
//! careful transcription: for each one, a theorem saying that when it fires the
//! model takes the corresponding step, that the state it computes is the state
//! the model moves to, and — where the notion makes sense — that when it
//! refuses the model's step is not enabled at all.
//!
//! The last of those is the half that is easy to leave out and carries most of
//! the weight. A step function that accepted nothing would satisfy "whenever it
//! fires, the model steps" perfectly.
//!
//! # The couplings
//!
//! The model's state is a whole `System`; a step function sees one actor's
//! record and a couple of booleans. The theorems below name the correspondence
//! as hypotheses rather than assuming it silently:
//!
//! | Hypothesis | What supplies it |
//! | --- | --- |
//! | `sys.actors[a] == st.view()` | the server's record *is* the actor's record |
//! | `granted == sys.network.contains(Grant { .. })` | the server's set of issued grants |
//! | `to_is_node == sys.nodes.contains(to)` | the server's roster |
//! | `sys.live.contains(n)` | `n` is connected and asking |
//! | `sys.network.contains(Revoke { .. })` | `begin_transfer` put it there |
//!
//! The first four are discharged by construction in `services/ownership`. Two
//! of them are worth reading twice, because they are discharged in quite
//! different ways.
//!
//! The **grant** coupling is an *equality*, and it is maintained by the server
//! doing work: `granted` is an input to `acquire_step`, so the server's set has
//! to hold every grant the model's network would. Four transitions publish one
//! — `tr_issue_grant`, `tr_complete_release`, `tr_revoke_owner`,
//! `tr_reassign_unowned` and `tr_abort_transfer` — and a server that recorded
//! only the first would be applying the refusal theorem under a hypothesis that
//! does not hold, which is worth nothing at all. That is a coupling a server can
//! *break*, and one did.
//!
//! The **revoke** coupling is structural and cannot be broken the same way:
//! nothing reads it, and the registry can only be in a `Transferring` record
//! because its own `begin_transfer` put it there, which is the transition that
//! puts that exact message on the network. It is a hypothesis about how the
//! state was reached rather than about a second set kept in step with the
//! first.
//!
//! What no theorem here covers is equally worth naming: the lock, the identity
//! lookup, the durable epoch floor and the audit log. Those are the server's,
//! and `services/ownership` says so in the same words.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::ownership::steps::*;

verus! {

// ---------------------------------------------------------------------------
// The post-states, built explicitly
// ---------------------------------------------------------------------------
//
// One per transition. Writing them out rather than existentially quantifying
// over "some post state" is deliberate: an existential would let a theorem be
// satisfied by a step the server did not take.

/// Where `tr_acquire` sends the system.
pub open spec fn acquire_post(sys: System, a: ActorId, n: NodeId) -> System {
    System {
        actors: sys.actors.insert(a, acquire_next(sys.actors[a], n)),
        nodes: sys.nodes,
        live: sys.live,
        issued: sys.issued.insert(
            Token { actor: a, epoch: current_epoch(sys.actors[a]), holder: n },
        ),
        network: sys.network,
    }
}

/// Where `tr_begin_transfer` sends the system.
pub open spec fn begin_transfer_post(sys: System, a: ActorId, from: NodeId, to: NodeId) -> System {
    System {
        actors: sys.actors.insert(a, begin_transfer_next(sys.actors[a], to)),
        nodes: sys.nodes,
        live: sys.live,
        issued: sys.issued,
        network: sys.network.insert(
            Message::Revoke {
                actor: a,
                target: from,
                old_epoch: current_epoch(sys.actors[a]),
                new_epoch: current_epoch(sys.actors[a]) + 1,
            },
        ),
    }
}

/// Where `tr_handle_revoke` sends the system: the outgoing owner's
/// acknowledgement, and nothing else.
pub open spec fn released_post(sys: System, a: ActorId, from: NodeId, new_epoch: Epoch) -> System {
    System {
        actors: sys.actors,
        nodes: sys.nodes,
        live: sys.live,
        issued: sys.issued,
        network: sys.network.insert(
            Message::Released { actor: a, from: from, new_epoch: new_epoch },
        ),
    }
}

/// Where `tr_complete_release` sends it from there.
pub open spec fn release_post(
    sys: System,
    a: ActorId,
    from: NodeId,
    to: NodeId,
    new_epoch: Epoch,
) -> System {
    System {
        actors: sys.actors.insert(
            a,
            OwnershipState::Unowned { epoch: new_epoch, intended_owner: to },
        ),
        nodes: sys.nodes,
        live: sys.live,
        issued: sys.issued,
        network: released_post(sys, a, from, new_epoch).network.insert(
            Message::Grant { actor: a, to: to, epoch: new_epoch },
        ),
    }
}

/// Where a forced revoke sends the system, whichever of the three transitions
/// it turns out to be.
pub open spec fn force_post(sys: System, a: ActorId, next: NodeId) -> System {
    System {
        actors: sys.actors.insert(a, force_next(sys.actors[a], next)),
        nodes: sys.nodes,
        live: sys.live,
        issued: sys.issued,
        network: sys.network.insert(
            Message::Grant {
                actor: a,
                to: force_offers_to(sys.actors[a], next),
                epoch: current_epoch(sys.actors[a]) + 1,
            },
        ),
    }
}

/// Where `tr_issue_grant` sends the system: one more copy of a grant that names
/// only state which is already public.
pub open spec fn issue_grant_post(sys: System, a: ActorId, to: NodeId, epoch: Epoch) -> System {
    System {
        actors: sys.actors,
        nodes: sys.nodes,
        live: sys.live,
        issued: sys.issued,
        network: sys.network.insert(Message::Grant { actor: a, to: to, epoch: epoch }),
    }
}

// ---------------------------------------------------------------------------
// Acquire
// ---------------------------------------------------------------------------

/// When [`acquire_step`] fires, `tr_acquire` fires, to exactly the state it
/// computed.
pub proof fn theorem_acquire_step_refines_tr_acquire(
    sys: System,
    a: ActorId,
    n: NodeId,
    e: Epoch,
    granted: bool,
)
    requires
        sys.actors.contains_key(a),
        sys.live.contains(n),
        granted == sys.network.contains(Message::Grant { actor: a, to: n, epoch: e }),
        acquire_fires(sys.actors[a], n, e, granted),
    ensures
        tr_acquire(sys, acquire_post(sys, a, n), a, n),
        acquire_post(sys, a, n).actors[a] == acquire_next(sys.actors[a], n),
{
}

/// When [`acquire_step`] refuses a request naming the actor's current epoch,
/// **no** post state satisfies `tr_acquire`.
///
/// The hypothesis `e == current_epoch(..)` is the one place the executable step
/// is narrower than the model, and it is narrower in the safe direction: the
/// model reads the epoch out of its own record, a request carries one, and a
/// request naming any other epoch is refused. See `crate::ownership::steps`.
pub proof fn theorem_acquire_step_refuses_exactly_when_disabled(
    sys: System,
    post: System,
    a: ActorId,
    n: NodeId,
    e: Epoch,
    granted: bool,
)
    requires
        granted == sys.network.contains(Message::Grant { actor: a, to: n, epoch: e }),
        e == current_epoch(sys.actors[a]),
        !acquire_fires(sys.actors[a], n, e, granted),
    ensures
        !tr_acquire(sys, post, a, n),
{
}

/// However the model acquires, the actor ends up where the step says.
pub proof fn theorem_acquire_outcome_is_the_step(
    sys: System,
    post: System,
    a: ActorId,
    n: NodeId,
)
    requires
        tr_acquire(sys, post, a, n),
    ensures
        post.actors[a] == acquire_next(sys.actors[a], n),
{
}

// ---------------------------------------------------------------------------
// Begin transfer
// ---------------------------------------------------------------------------

/// When [`begin_transfer_step`] fires, `tr_begin_transfer` fires, to exactly
/// the state it computed — with the next epoch already allocated, which is what
/// fences the outgoing owner from this moment rather than from the
/// acknowledgement.
pub proof fn theorem_begin_transfer_step_refines_tr_begin_transfer(
    sys: System,
    a: ActorId,
    from: NodeId,
    to: NodeId,
)
    requires
        sys.actors.contains_key(a),
        sys.live.contains(from),
        sys.nodes.contains(to),
        begin_transfer_fires(sys.actors[a], from, to, true),
    ensures
        tr_begin_transfer(sys, begin_transfer_post(sys, a, from, to), a, from, to),
        begin_transfer_post(sys, a, from, to).actors[a] == begin_transfer_next(sys.actors[a], to),
{
}

/// When [`begin_transfer_step`] refuses for a reason other than exhaustion, no
/// post state satisfies `tr_begin_transfer`.
pub proof fn theorem_begin_transfer_step_refuses_exactly_when_disabled(
    sys: System,
    post: System,
    a: ActorId,
    from: NodeId,
    to: NodeId,
    to_is_node: bool,
)
    requires
        to_is_node == sys.nodes.contains(to),
        !begin_transfer_fires(sys.actors[a], from, to, to_is_node),
    ensures
        !tr_begin_transfer(sys, post, a, from, to),
{
}

/// However the model begins a transfer, the actor ends up where the step says.
pub proof fn theorem_begin_transfer_outcome_is_the_step(
    sys: System,
    post: System,
    a: ActorId,
    from: NodeId,
    to: NodeId,
)
    requires
        tr_begin_transfer(sys, post, a, from, to),
    ensures
        post.actors[a] == begin_transfer_next(sys.actors[a], to),
{
}

// ---------------------------------------------------------------------------
// Release
// ---------------------------------------------------------------------------

/// [`release_step`] is two model transitions: the outgoing owner's
/// acknowledgement and the coordinator's reaction to it.
///
/// They are one method because the coordinator is the thing being called, and
/// they are two theorems' worth of obligation because the model keeps them
/// apart — `tr_handle_revoke` is a node acting, `tr_complete_release` is the
/// coordinator acting, and the middle state is exhibited rather than assumed to
/// exist.
pub proof fn theorem_release_step_refines_handle_revoke_then_complete_release(
    sys: System,
    a: ActorId,
    from: NodeId,
    to: NodeId,
    old_epoch: Epoch,
    new_epoch: Epoch,
)
    requires
        sys.actors.contains_key(a),
        sys.actors[a] == (OwnershipState::Transferring {
            from: from,
            to: to,
            old_epoch: old_epoch,
            new_epoch: new_epoch,
        }),
        sys.live.contains(from),
        sys.network.contains(
            Message::Revoke {
                actor: a,
                target: from,
                old_epoch: old_epoch,
                new_epoch: new_epoch,
            },
        ),
    ensures
        tr_handle_revoke(
            sys,
            released_post(sys, a, from, new_epoch),
            a,
            from,
            old_epoch,
            new_epoch,
        ),
        tr_complete_release(
            released_post(sys, a, from, new_epoch),
            release_post(sys, a, from, to, new_epoch),
            a,
        ),
        release_post(sys, a, from, to, new_epoch).actors[a] == release_next(sys.actors[a]),
{
}

/// A release [`release_step`] refuses is not the handover the model would
/// complete.
///
/// "Exactly when disabled" is the wrong shape here, and saying why is the
/// point: `tr_complete_release` takes no node and no epoch — it reads both out
/// of the actor's record. So a refusal cannot mean the model is stuck; it means
/// the model's release, if it happens, is somebody else's, or the same node's
/// at a different epoch. Which is precisely what a replayed or delayed release
/// must not be able to complete.
pub proof fn theorem_refused_release_is_not_the_models_release(
    sys: System,
    post: System,
    a: ActorId,
    n: NodeId,
    e: Epoch,
)
    requires
        !release_fires(sys.actors[a], n, e),
        tr_complete_release(sys, post, a),
    ensures
        !(transferring_from(sys.actors[a]) == n && transferring_new_epoch(sys.actors[a]) == e),
{
}

// ---------------------------------------------------------------------------
// Forced revocation
// ---------------------------------------------------------------------------
//
// Three model transitions, one step function, and three theorems rather than a
// disjunction: which transition it is depends on the state, and the point of
// the step function is that a server does not have to choose between them.

/// From `Owned`, a forced revoke is `tr_revoke_owner`.
pub proof fn theorem_force_step_refines_tr_revoke_owner(sys: System, a: ActorId, next: NodeId)
    requires
        sys.actors.contains_key(a),
        sys.nodes.contains(next),
        is_owned(sys.actors[a]),
    ensures
        tr_revoke_owner(sys, force_post(sys, a, next), a, next),
        force_post(sys, a, next).actors[a] == force_next(sys.actors[a], next),
{
}

/// From `Unowned`, it is `tr_reassign_unowned`: the intended owner never picked
/// the actor up, so burn the epoch and offer it to somebody else.
pub proof fn theorem_force_step_refines_tr_reassign_unowned(sys: System, a: ActorId, next: NodeId)
    requires
        sys.actors.contains_key(a),
        sys.nodes.contains(next),
        is_unowned(sys.actors[a]),
    ensures
        tr_reassign_unowned(sys, force_post(sys, a, next), a, next),
        force_post(sys, a, next).actors[a] == force_next(sys.actors[a], next),
{
}

/// From `Transferring`, it is `tr_abort_transfer` — and `next` is ignored.
///
/// This is where [`force_offers_to`] earns its existence. The model burns
/// *another* epoch, so a `Grant` for the abandoned one is stale on arrival, and
/// offers the actor back to the node it was being taken from. A coordinator
/// that asked for some other successor did not get it, and the step function
/// returns the node that was actually offered rather than reporting success.
pub proof fn theorem_force_step_refines_tr_abort_transfer(sys: System, a: ActorId, next: NodeId)
    requires
        sys.actors.contains_key(a),
        is_transferring(sys.actors[a]),
    ensures
        tr_abort_transfer(sys, force_post(sys, a, next), a),
        force_post(sys, a, next).actors[a] == force_next(sys.actors[a], next),
        force_offers_to(sys.actors[a], next) == transferring_from(sys.actors[a]),
{
}

// ---------------------------------------------------------------------------
// Poll
// ---------------------------------------------------------------------------

/// An offered grant is `tr_issue_grant`, and it names the actor's current
/// epoch.
///
/// The second half is what stops a poll being a way to collect a superseded
/// generation: the registry cannot offer an epoch it has already left, because
/// the epoch in the answer is read from the same record the fence is read from.
pub proof fn theorem_poll_step_refines_tr_issue_grant(
    sys: System,
    a: ActorId,
    st: ExecState,
    n: u64,
    epoch: u64,
)
    requires
        sys.actors.contains_key(a),
        sys.actors[a] == st.view(),
        poll_answer(st, n) == ExecOffer::Grant(epoch),
    ensures
        tr_issue_grant(sys, issue_grant_post(sys, a, n as nat, epoch as nat), a),
        epoch as nat == current_epoch(sys.actors[a]),
{
}

/// Telling an outgoing owner to stand down hands it the `Revoke` that
/// `tr_begin_transfer` already put on the network, and so enables exactly the
/// node's own `tr_handle_revoke`.
pub proof fn theorem_poll_step_refines_tr_handle_revoke(
    sys: System,
    a: ActorId,
    st: ExecState,
    n: u64,
    epoch: u64,
    old_epoch: Epoch,
)
    requires
        sys.actors.contains_key(a),
        sys.actors[a] == st.view(),
        sys.live.contains(n as nat),
        poll_answer(st, n) == ExecOffer::Revoke(epoch),
        sys.network.contains(
            Message::Revoke {
                actor: a,
                target: n as nat,
                old_epoch: old_epoch,
                new_epoch: epoch as nat,
            },
        ),
    ensures
        tr_handle_revoke(
            sys,
            released_post(sys, a, n as nat, epoch as nat),
            a,
            n as nat,
            old_epoch,
            epoch as nat,
        ),
        epoch as nat == current_epoch(sys.actors[a]),
{
}

/// A poll answered with `Nothing` is not an offer withheld from somebody who
/// had one coming: nobody is owed anything in that state.
pub proof fn theorem_poll_step_offers_nothing_only_when_nothing_is_owed(
    sys: System,
    a: ActorId,
    st: ExecState,
    n: u64,
)
    requires
        sys.actors[a] == st.view(),
        poll_answer(st, n) == ExecOffer::Nothing,
    ensures
        // `n` is neither the node the actor is being held for, nor the node
        // being told to stand down.
        !(is_unowned(sys.actors[a]) && intended_owner(sys.actors[a]) == n as nat),
        !(is_transferring(sys.actors[a]) && transferring_from(sys.actors[a]) == n as nat),
{
}

// ---------------------------------------------------------------------------
// Are any of these vacuous?
// ---------------------------------------------------------------------------
//
// Every theorem above is an implication under hypotheses, and an implication
// whose hypotheses cannot all hold at once is true and says nothing. That is
// the failure mode a reader cannot see and the verifier will not report: a
// refinement suite can be green and empty.
//
// So the hypotheses are exhibited rather than argued about. The scenario below
// builds one concrete system and walks a handover through the step functions,
// invoking each theorem at the point its hypotheses hold and asserting what
// came out. If any of those hypotheses were unsatisfiable the scenario would
// stop verifying, which is the check the theorems cannot perform on themselves.

/// A whole handover, through the verified steps, on a system written out in
/// full.
///
/// `A` is offered actor 0 at epoch 41 and takes it; `A` agrees to hand it to
/// `B`, which allocates 42 and fences `A` from that moment; `A` acknowledges
/// and the actor is offered to `B` at 42. Each arrow is a theorem from this
/// module applied to the state the previous one produced, so the run is one
/// execution rather than three unrelated claims.
pub proof fn scenario_a_handover_through_the_verified_steps() {
    let actor: ActorId = 0;
    let a: NodeId = 1;
    let b: NodeId = 2;

    let sys0 = System {
        actors: Map::empty().insert(
            actor,
            OwnershipState::Unowned { epoch: 41, intended_owner: a },
        ),
        nodes: Set::empty().insert(a).insert(b),
        live: Set::empty().insert(a).insert(b),
        issued: Set::empty(),
        network: Set::empty().insert(Message::Grant { actor: actor, to: a, epoch: 41 }),
    };

    assert(sys0.actors.contains_key(actor));
    assert(sys0.actors[actor] == (OwnershipState::Unowned { epoch: 41, intended_owner: a }));
    assert(sys0.live.contains(a));
    assert(sys0.nodes.contains(b));
    assert(sys0.network.contains(Message::Grant { actor: actor, to: a, epoch: 41 }));

    // A poll would offer exactly this grant, at exactly this epoch.
    let record = ExecState::Unowned { epoch: 41, intended: 1 };
    assert(record.view() == sys0.actors[actor]);
    assert(poll_answer(record, 1) == ExecOffer::Grant(41));
    theorem_poll_step_refines_tr_issue_grant(sys0, actor, record, 1, 41);

    // `A` takes it.
    assert(acquire_fires(sys0.actors[actor], a, 41, true));
    theorem_acquire_step_refines_tr_acquire(sys0, actor, a, 41, true);
    let sys1 = acquire_post(sys0, actor, a);
    assert(tr_acquire(sys0, sys1, actor, a));
    assert(sys1.actors[actor] == (OwnershipState::Owned { owner: a, epoch: 41 }));

    // Nobody else may write, and `A` may — the fence, on the system's record.
    assert(may_mutate(sys1.actors[actor], a, 41));
    assert(!may_mutate(sys1.actors[actor], b, 41));

    // `A` agrees to hand the actor to `B`, which allocates 42.
    assert(sys1.live.contains(a));
    assert(sys1.nodes.contains(b));
    assert(begin_transfer_fires(sys1.actors[actor], a, b, true));
    theorem_begin_transfer_step_refines_tr_begin_transfer(sys1, actor, a, b);
    let sys2 = begin_transfer_post(sys1, actor, a, b);
    assert(tr_begin_transfer(sys1, sys2, actor, a, b));
    assert(sys2.actors[actor] == (OwnershipState::Transferring {
        from: a,
        to: b,
        old_epoch: 41,
        new_epoch: 42,
    }));

    // And `A` is fenced from this moment, not from the acknowledgement.
    assert(!may_mutate(sys2.actors[actor], a, 41));
    assert(current_epoch(sys2.actors[actor]) == 42);

    // `A` acknowledges. Two model transitions, one call.
    assert(sys2.network.contains(Message::Revoke {
        actor: actor,
        target: a,
        old_epoch: 41,
        new_epoch: 42,
    }));
    theorem_release_step_refines_handle_revoke_then_complete_release(sys2, actor, a, b, 41, 42);
    let mid = released_post(sys2, actor, a, 42);
    let sys3 = release_post(sys2, actor, a, b, 42);
    assert(tr_handle_revoke(sys2, mid, actor, a, 41, 42));
    assert(tr_complete_release(mid, sys3, actor));
    assert(sys3.actors[actor] == (OwnershipState::Unowned { epoch: 42, intended_owner: b }));

    // The actor is now offered to `B` at 42, and to nobody at 41.
    let after = ExecState::Unowned { epoch: 42, intended: 2 };
    assert(after.view() == sys3.actors[actor]);
    assert(poll_answer(after, 2) == ExecOffer::Grant(42));
    assert(poll_answer(after, 1) == ExecOffer::Nothing);
    theorem_poll_step_offers_nothing_only_when_nothing_is_owed(sys3, actor, after, 1);
}

/// The refusal theorems are not vacuous either.
///
/// Their hypotheses are the *negation* of a guard, so a run in which the guard
/// holds says nothing about them. This is a system in which each one applies:
/// no grant has been published, so an acquire is refused and provably not
/// something the model could have done; and node `B`, which does not own the
/// actor, cannot begin a transfer of it.
pub proof fn scenario_the_refusals_are_refusals_of_something_real() {
    let actor: ActorId = 0;
    let a: NodeId = 1;
    let b: NodeId = 2;

    // The actor is held for `A` at 41 and no grant has been sent.
    let ungranted = System {
        actors: Map::empty().insert(
            actor,
            OwnershipState::Unowned { epoch: 41, intended_owner: a },
        ),
        nodes: Set::empty().insert(a).insert(b),
        live: Set::empty().insert(a).insert(b),
        issued: Set::empty(),
        network: Set::empty(),
    };
    assert(!ungranted.network.contains(Message::Grant { actor: actor, to: a, epoch: 41 }));
    assert(current_epoch(ungranted.actors[actor]) == 41);
    assert(!acquire_fires(ungranted.actors[actor], a, 41, false));

    // For *every* post state, not merely for one the server had in mind.
    assert forall|post: System| !tr_acquire(ungranted, post, actor, a) by {
        theorem_acquire_step_refuses_exactly_when_disabled(ungranted, post, actor, a, 41, false);
    }

    // And a node that does not own the actor cannot hand it on.
    let held = System {
        actors: Map::empty().insert(actor, OwnershipState::Owned { owner: a, epoch: 41 }),
        nodes: Set::empty().insert(a).insert(b),
        live: Set::empty().insert(a).insert(b),
        issued: Set::empty(),
        network: Set::empty(),
    };
    assert(held.nodes.contains(a));
    assert(!begin_transfer_fires(held.actors[actor], b, a, true));
    assert forall|post: System| !tr_begin_transfer(held, post, actor, b, a) by {
        theorem_begin_transfer_step_refuses_exactly_when_disabled(held, post, actor, b, a, true);
    }
}

// ---------------------------------------------------------------------------
// The fence
// ---------------------------------------------------------------------------

/// [`may_write_step`] is the *system's* fence, not a node's belief about it.
///
/// `exec::FenceGuard` answers `may_mutate` for the one generation the guard
/// records, which is why its own docs say a node cannot fence itself. This
/// function is handed the registry's current record, so the same postcondition
/// becomes a statement about `can_mutate` — authority as the system sees it.
/// That is the difference between node-local staleness rejection and fencing,
/// and it is bought entirely by *where the function is called*.
pub proof fn theorem_may_write_step_is_the_system_fence(
    sys: System,
    a: ActorId,
    st: ExecState,
    n: NodeId,
    e: Epoch,
)
    requires
        sys.actors.contains_key(a),
        sys.actors[a] == st.view(),
    ensures
        may_mutate(st.view(), n, e) == can_mutate(sys, a, n, e),
{
}

} // verus!
