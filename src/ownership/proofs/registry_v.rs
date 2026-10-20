//! The registry's record is the model.
//!
//! [`crate::ownership::registry::RegistryCore`] keeps the actor's record, the
//! grants published and a count of writes. These theorems say what its contracts
//! come to against [`crate::ownership::model`]: given a system the core stands
//! for, a core that takes a step stands for the system the model's transition
//! leads to — **including the grants**.
//!
//! # The relation
//!
//! [`stands_for`] has two parts. The actor's record is the core's state. And the
//! core's published grants are the network's `Grant` messages *for that actor*,
//! exactly — an equality, not an inclusion, because
//! `acquire_step` reads it as `granted` and its refusal theorem is worth nothing
//! under a set that has forgotten a grant the model's network holds. It is the
//! coupling [`crate::ownership::proofs::refinement`] names as the one a server
//! can break, and these theorems are where a registry that publishes the wrong
//! grant stops type-checking.
//!
//! The model's `Revoke` and `Released` messages are not tracked by the core. The
//! `Revoke` coupling is structural — the record can be `Transferring` only
//! because a `begin_transfer` put it there, and that puts the message on the
//! network — and the theorem for `release` takes it as a hypothesis, as the
//! existing refinement does.
//!
//! # What is not here
//!
//! The lock, the identity lookup, the audit log and the durable floor. The
//! theorems are about one step at a time; that `persist` is called before the
//! state moves is the code's order, not a proved property.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::proofs::refinement::*;
use crate::ownership::registry::*;
use crate::ownership::spec::*;
use crate::ownership::steps::*;

verus! {

/// The core stands for the system, as far as it keeps anything: the actor's
/// record is its state, and its published grants are the network's.
pub open spec fn stands_for(c: RegistryCore, sys: OwnershipSystem, a: ActorId) -> bool {
    &&& sys.actors.contains_key(a)
    &&& sys.actors[a] == c.state.view()
    &&& forall|n: Id, e: nat|
        #[trigger] c.has_grant(n, e) == sys.network.contains(
            Message::Grant { actor: a, to: n, epoch: e },
        )
}

/// **A poll that answers with a grant is `tr_issue_grant`**, and publishes it:
/// the core's set and the network gain the same grant.
pub proof fn theorem_poll_is_issue_grant(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    node: Id,
    epoch: u64,
)
    requires
        stands_for(c, sys, a),
        poll_answer(c.state, node) == ExecOffer::Grant(epoch),
        c2.state.view() == c.state.view(),
        grants_plus(c, c2, node, epoch as nat),
    ensures
        tr_issue_grant(sys, issue_grant_post(sys, a, node, epoch as nat), a),
        stands_for(c2, issue_grant_post(sys, a, node, epoch as nat), a),
{
    theorem_poll_step_refines_tr_issue_grant(sys, a, c.state, node, epoch);
    let sys2 = issue_grant_post(sys, a, node, epoch as nat);
    assert forall|n: Id, e: nat|
        #[trigger] c2.has_grant(n, e) == sys2.network.contains(
            Message::Grant { actor: a, to: n, epoch: e },
        ) by {
        assert(c2.has_grant(n, e) == (c.has_grant(n, e) || (n == node && e == epoch as nat)));
    }
}

/// **A poll that answers with anything else publishes nothing** — and the model
/// takes no step, so the core and the system are as they were.
pub proof fn theorem_poll_without_a_grant_changes_nothing(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    node: Id,
)
    requires
        stands_for(c, sys, a),
        !(poll_answer(c.state, node) is Grant),
        c2.state.view() == c.state.view(),
        grants_same(c, c2),
    ensures
        stands_for(c2, sys, a),
{
    assert forall|n: Id, e: nat|
        #[trigger] c2.has_grant(n, e) == sys.network.contains(
            Message::Grant { actor: a, to: n, epoch: e },
        ) by {
        assert(c2.has_grant(n, e) == c.has_grant(n, e));
    }
}

/// **`acquire` is `tr_acquire`.** The grant it required is the network's.
pub proof fn theorem_acquire_is_tr_acquire(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    node: Id,
    epoch: u64,
)
    requires
        stands_for(c, sys, a),
        sys.live.contains(node),
        acquire_fires(c.state.view(), node, epoch as nat, c.has_grant(node, epoch as nat)),
        c2.state.view() == acquire_next(c.state.view(), node),
        grants_same(c, c2),
    ensures
        tr_acquire(sys, acquire_post(sys, a, node), a, node),
        stands_for(c2, acquire_post(sys, a, node), a),
{
    let granted = c.has_grant(node, epoch as nat);
    assert(granted == sys.network.contains(
        Message::Grant { actor: a, to: node, epoch: epoch as nat },
    ));
    theorem_acquire_step_refines_tr_acquire(sys, a, node, epoch as nat, granted);
    let sys2 = acquire_post(sys, a, node);
    assert forall|n: Id, e: nat|
        #[trigger] c2.has_grant(n, e) == sys2.network.contains(
            Message::Grant { actor: a, to: n, epoch: e },
        ) by {
        assert(c2.has_grant(n, e) == c.has_grant(n, e));
    }
}

/// **A refused `acquire` is a step the model could not take**, whatever state it
/// was sent to — for a request that names the actor's current epoch, which is
/// the only kind the model has an acquire for.
pub proof fn theorem_refused_acquire_is_disabled(
    c: RegistryCore,
    sys: OwnershipSystem,
    post: OwnershipSystem,
    a: ActorId,
    node: Id,
    epoch: u64,
)
    requires
        stands_for(c, sys, a),
        epoch as nat == current_epoch(sys.actors[a]),
        !acquire_fires(c.state.view(), node, epoch as nat, c.has_grant(node, epoch as nat)),
    ensures
        !tr_acquire(sys, post, a, node),
{
    let granted = c.has_grant(node, epoch as nat);
    theorem_acquire_step_refuses_exactly_when_disabled(
        sys,
        post,
        a,
        node,
        epoch as nat,
        granted,
    );
}

/// **`begin_transfer` is `tr_begin_transfer`**; it publishes no grant, and the
/// model's `Revoke` goes on the network.
pub proof fn theorem_begin_transfer_is_tr_begin_transfer(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    from: Id,
    to: Id,
)
    requires
        stands_for(c, sys, a),
        sys.live.contains(from),
        sys.nodes.contains(to),
        begin_transfer_fires(c.state.view(), from, to, true),
        c2.state.view() == begin_transfer_next(c.state.view(), to),
        grants_same(c, c2),
    ensures
        tr_begin_transfer(sys, begin_transfer_post(sys, a, from, to), a, from, to),
        stands_for(c2, begin_transfer_post(sys, a, from, to), a),
{
    theorem_begin_transfer_step_refines_tr_begin_transfer(sys, a, from, to);
    let sys2 = begin_transfer_post(sys, a, from, to);
    assert forall|n: Id, e: nat|
        #[trigger] c2.has_grant(n, e) == sys2.network.contains(
            Message::Grant { actor: a, to: n, epoch: e },
        ) by {
        assert(c2.has_grant(n, e) == c.has_grant(n, e));
    }
}

/// **A refused `begin_transfer` is a step the model could not take** — unless the
/// refusal was the `u64` epoch running out, which the model's `nat` does not.
pub proof fn theorem_refused_begin_transfer_is_disabled(
    c: RegistryCore,
    sys: OwnershipSystem,
    post: OwnershipSystem,
    a: ActorId,
    from: Id,
    to: Id,
    to_is_node: bool,
)
    requires
        stands_for(c, sys, a),
        to_is_node == sys.nodes.contains(to),
        !begin_transfer_fires(c.state.view(), from, to, to_is_node),
    ensures
        !tr_begin_transfer(sys, post, a, from, to),
{
    theorem_begin_transfer_step_refuses_exactly_when_disabled(
        sys,
        post,
        a,
        from,
        to,
        to_is_node,
    );
}

/// **`release` is `tr_handle_revoke` then `tr_complete_release`**, and the grant
/// that completes the handover is the one published.
pub proof fn theorem_release_is_handle_revoke_then_complete_release(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    node: Id,
    epoch: u64,
    to: Id,
    old_epoch: Epoch,
)
    requires
        stands_for(c, sys, a),
        sys.live.contains(node),
        release_fires(c.state.view(), node, epoch as nat),
        c2.state.view() == release_next(c.state.view()),
        to == intended_owner(c2.state.view()),
        grants_plus(c, c2, to, epoch as nat),
        sys.network.contains(
            Message::Revoke {
                actor: a,
                target: node,
                old_epoch: old_epoch,
                new_epoch: epoch as nat,
            },
        ),
        c.state.view() == (OwnershipState::Transferring {
            from: node,
            to: to,
            old_epoch: old_epoch,
            new_epoch: epoch as nat,
        }),
    ensures
        tr_handle_revoke(
            sys,
            released_post(sys, a, node, epoch as nat),
            a,
            node,
            old_epoch,
            epoch as nat,
        ),
        tr_complete_release(
            released_post(sys, a, node, epoch as nat),
            release_post(sys, a, node, to, epoch as nat),
            a,
        ),
        stands_for(c2, release_post(sys, a, node, to, epoch as nat), a),
{
    theorem_release_step_refines_handle_revoke_then_complete_release(
        sys,
        a,
        node,
        to,
        old_epoch,
        epoch as nat,
    );
    let sys2 = release_post(sys, a, node, to, epoch as nat);
    assert forall|n: Id, e: nat|
        #[trigger] c2.has_grant(n, e) == sys2.network.contains(
            Message::Grant { actor: a, to: n, epoch: e },
        ) by {
        assert(c2.has_grant(n, e) == (c.has_grant(n, e) || (n == to && e == epoch as nat)));
    }
}

/// **`force` from `Owned` is `tr_revoke_owner`**, and publishes the grant it
/// offers the actor on with.
pub proof fn theorem_force_from_owned_is_tr_revoke_owner(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    next: Id,
    offered: Id,
)
    requires
        stands_for(c, sys, a),
        sys.nodes.contains(next),
        is_owned(c.state.view()),
        c2.state.view() == force_next(c.state.view(), next),
        offered == force_offers_to(c.state.view(), next),
        grants_plus(c, c2, offered, current_epoch(c2.state.view())),
    ensures
        tr_revoke_owner(sys, force_post(sys, a, next), a, next),
        stands_for(c2, force_post(sys, a, next), a),
{
    theorem_force_step_refines_tr_revoke_owner(sys, a, next);
    lemma_force_publishes(c, c2, sys, a, next, offered);
}

/// **`force` from `Unowned` is `tr_reassign_unowned`.**
pub proof fn theorem_force_from_unowned_is_tr_reassign_unowned(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    next: Id,
    offered: Id,
)
    requires
        stands_for(c, sys, a),
        sys.nodes.contains(next),
        is_unowned(c.state.view()),
        c2.state.view() == force_next(c.state.view(), next),
        offered == force_offers_to(c.state.view(), next),
        grants_plus(c, c2, offered, current_epoch(c2.state.view())),
    ensures
        tr_reassign_unowned(sys, force_post(sys, a, next), a, next),
        stands_for(c2, force_post(sys, a, next), a),
{
    theorem_force_step_refines_tr_reassign_unowned(sys, a, next);
    lemma_force_publishes(c, c2, sys, a, next, offered);
}

/// **`force` from `Transferring` is `tr_abort_transfer`**, which offers the actor
/// back to the node the transfer came from whatever `next` says.
pub proof fn theorem_force_from_transferring_is_tr_abort_transfer(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    next: Id,
    offered: Id,
)
    requires
        stands_for(c, sys, a),
        is_transferring(c.state.view()),
        c2.state.view() == force_next(c.state.view(), next),
        offered == force_offers_to(c.state.view(), next),
        grants_plus(c, c2, offered, current_epoch(c2.state.view())),
    ensures
        tr_abort_transfer(sys, force_post(sys, a, next), a),
        stands_for(c2, force_post(sys, a, next), a),
{
    theorem_force_step_refines_tr_abort_transfer(sys, a, next);
    lemma_force_publishes(c, c2, sys, a, next, offered);
}

/// The grant a forced move publishes is the one `force_post` puts on the network.
proof fn lemma_force_publishes(
    c: RegistryCore,
    c2: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    next: Id,
    offered: Id,
)
    requires
        stands_for(c, sys, a),
        c2.state.view() == force_next(c.state.view(), next),
        offered == force_offers_to(c.state.view(), next),
        grants_plus(c, c2, offered, current_epoch(c2.state.view())),
    ensures
        stands_for(c2, force_post(sys, a, next), a),
{
    let sys2 = force_post(sys, a, next);
    assert(current_epoch(c2.state.view()) == current_epoch(c.state.view()) + 1);
    assert(sys2.actors[a] == c2.state.view());
    assert forall|n: Id, e: nat|
        #[trigger] c2.has_grant(n, e) == sys2.network.contains(
            Message::Grant { actor: a, to: n, epoch: e },
        ) by {
        assert(c2.has_grant(n, e) == (c.has_grant(n, e) || (n == offered && e
            == current_epoch(c2.state.view()))));
    }
}

/// **A write that lands is the model's `can_mutate`** — authority as the system
/// sees it — and changes nothing the model tracks.
pub proof fn theorem_a_landed_write_is_can_mutate(
    c: RegistryCore,
    sys: OwnershipSystem,
    a: ActorId,
    node: Id,
    epoch: u64,
)
    requires
        stands_for(c, sys, a),
        may_mutate(c.state.view(), node, epoch as nat),
    ensures
        can_mutate(sys, a, node, epoch as nat),
{
    theorem_may_write_step_is_the_system_fence(sys, a, c.state, node, epoch as nat);
}

} // verus!
