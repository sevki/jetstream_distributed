//! Ownership specification: who may mutate, which tokens carry authority, and
//! the system invariant that the protocol maintains.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;

use crate::ownership::fencing::*;
use crate::ownership::model::*;

verus! {

/// `node` may perform an authoritative mutation of an actor in state `s`,
/// presenting `epoch` as its fencing token.
///
/// This is the single definition of mutable authority in the whole system.
/// Note that authority is granted in *exactly one* shape: the actor is `Owned`,
/// the caller is the owner, and the caller's epoch is exactly the current one.
/// During `Transferring` and `Unowned` nobody has authority at all.
pub open spec fn may_mutate(s: OwnershipState, node: HostId, epoch: Epoch) -> bool {
    match s {
        OwnershipState::Owned { owner, epoch: e } => node == owner && epoch == e,
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch: _ } => false,
        OwnershipState::Unowned { epoch: _, intended_owner: _ } => false,
    }
}

/// `s` is owned by `n` (at whatever epoch).
pub open spec fn is_owned_by(s: OwnershipState, n: HostId) -> bool {
    match s {
        OwnershipState::Owned { owner, epoch: _ } => owner == n,
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch: _ } => false,
        OwnershipState::Unowned { epoch: _, intended_owner: _ } => false,
    }
}

/// Somebody owns `s`.
pub open spec fn is_owned(s: OwnershipState) -> bool {
    match s {
        OwnershipState::Owned { owner: _, epoch: _ } => true,
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch: _ } => false,
        OwnershipState::Unowned { epoch: _, intended_owner: _ } => false,
    }
}

/// `s` is mid-transfer.
pub open spec fn is_transferring(s: OwnershipState) -> bool {
    match s {
        OwnershipState::Owned { owner: _, epoch: _ } => false,
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch: _ } => true,
        OwnershipState::Unowned { epoch: _, intended_owner: _ } => false,
    }
}

/// The node a `Transferring` actor is moving away from.
///
/// Only meaningful under `is_transferring(s)`; the other cases return a
/// placeholder. These accessors exist so that facts about the live handover can
/// be stated without an existential over all four `Transferring` fields — a
/// four-variable `exists` needs a trigger covering all four, and the natural
/// trigger (the `Released` message) mentions only two.
pub open spec fn transferring_from(s: OwnershipState) -> HostId {
    match s {
        OwnershipState::Transferring { from, to: _, old_epoch: _, new_epoch: _ } => from,
        _ => 0,
    }
}

/// The epoch a `Transferring` actor is moving to. See [`transferring_from`].
pub open spec fn transferring_new_epoch(s: OwnershipState) -> Epoch {
    match s {
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch } => new_epoch,
        _ => 0,
    }
}

/// `s` is unowned.
pub open spec fn is_unowned(s: OwnershipState) -> bool {
    match s {
        OwnershipState::Owned { owner: _, epoch: _ } => false,
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch: _ } => false,
        OwnershipState::Unowned { epoch: _, intended_owner: _ } => true,
    }
}

/// Convenience: `node` may mutate `actor` in system `sys` presenting `epoch`.
pub open spec fn can_mutate(sys: OwnershipSystem, actor: ActorId, node: HostId, epoch: Epoch) -> bool {
    sys.actors.contains_key(actor) && may_mutate(sys.actors[actor], node, epoch)
}

/// A *physically held* token, which may be arbitrarily stale.
pub open spec fn token_held(sys: OwnershipSystem, t: Token) -> bool {
    sys.issued.contains(t)
}

/// A token that actually confers authority right now.
///
/// Holding a token is not enough: the actor's state has to still agree.
pub open spec fn token_authorized(sys: OwnershipSystem, t: Token) -> bool {
    &&& sys.actors.contains_key(t.actor)
    &&& sys.issued.contains(t)
    &&& may_mutate(sys.actors[t.actor], t.holder, t.epoch)
}

// ---------------------------------------------------------------------------
// The system invariant
// ---------------------------------------------------------------------------

/// What must hold of every issued token.
///
/// * the token names a real actor;
/// * the token's epoch never runs ahead of the actor's current epoch (tokens
///   cannot be minted for the future);
/// * a token at the actor's *current* epoch can only be held by the actor's
///   current owner (tokens cannot be minted for somebody else).
pub open spec fn token_inv(sys: OwnershipSystem, t: Token) -> bool {
    &&& sys.actors.contains_key(t.actor)
    &&& t.epoch <= current_epoch(sys.actors[t.actor])
    &&& (t.epoch == current_epoch(sys.actors[t.actor]) ==> is_owned_by(sys.actors[t.actor], t.holder))
}

/// Every issued token is well formed.
pub open spec fn inv_tokens_bounded(sys: OwnershipSystem) -> bool {
    forall|t: Token| #[trigger] sys.issued.contains(t) ==> token_inv(sys, t)
}

/// At most one token was ever physically issued per `(actor, epoch)`.
pub open spec fn inv_tokens_unique(sys: OwnershipSystem) -> bool {
    forall|t1: Token, t2: Token|
        #![trigger sys.issued.contains(t1), sys.issued.contains(t2)]
        sys.issued.contains(t1) && sys.issued.contains(t2) && t1.actor == t2.actor && t1.epoch
            == t2.epoch ==> t1 == t2
}

/// The system invariant maintained by every transition.
pub open spec fn inv(sys: OwnershipSystem) -> bool {
    &&& inv_tokens_bounded(sys)
    &&& inv_tokens_unique(sys)
}

// ---------------------------------------------------------------------------
// Basic (state-local) lemmas
// ---------------------------------------------------------------------------

/// **Exclusive mutable ownership, state-local form.** At most one node may
/// mutate an actor, and it may do so at exactly one epoch.
pub proof fn lemma_exclusive_owner(s: OwnershipState, a: HostId, ea: Epoch, b: HostId, eb: Epoch)
    requires
        may_mutate(s, a, ea),
        may_mutate(s, b, eb),
    ensures
        a == b,
        ea == eb,
{
}

/// Authority implies the actor is owned by that node at the current epoch.
pub proof fn lemma_may_mutate_implies_current(s: OwnershipState, n: HostId, e: Epoch)
    requires
        may_mutate(s, n, e),
    ensures
        is_owned_by(s, n),
        e == current_epoch(s),
        valid_fence(s, e),
{
}

/// **Stale-owner fencing.** If the actor has advanced past `e`, nothing
/// presenting `e` can mutate it.
pub proof fn lemma_stale_epoch_cannot_mutate(s: OwnershipState, n: HostId, e: Epoch)
    requires
        current_epoch(s) > e,
    ensures
        !may_mutate(s, n, e),
{
}

/// Nobody has authority while a transfer is in flight.
pub proof fn lemma_no_authority_while_transferring(s: OwnershipState, n: HostId, e: Epoch)
    requires
        is_transferring(s),
    ensures
        !may_mutate(s, n, e),
{
}

/// Nobody has authority while the actor is unowned.
pub proof fn lemma_no_authority_while_unowned(s: OwnershipState, n: HostId, e: Epoch)
    requires
        is_unowned(s),
    ensures
        !may_mutate(s, n, e),
{
}

} // verus!
