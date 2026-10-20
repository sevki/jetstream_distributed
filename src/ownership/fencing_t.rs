//! Fencing epochs.
//!
//! Every ownership generation carries a monotonically increasing epoch. An
//! operation is accepted only if the epoch it carries is not behind the actor's
//! current authoritative epoch, which is what makes a returning stale owner
//! harmless.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::model::*;

verus! {

/// The one authoritative fencing epoch of an actor.
///
/// `Transferring { old_epoch, new_epoch }` already reports `new_epoch`: the
/// moment a transfer starts, the new epoch has been allocated and the outgoing
/// owner is fenced out, even though nobody has taken ownership yet.
pub open spec fn current_epoch(s: OwnershipState) -> Epoch {
    match s {
        OwnershipState::Owned { owner: _, epoch } => epoch,
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch } => new_epoch,
        OwnershipState::Unowned { epoch, intended_owner: _ } => epoch,
    }
}

/// `e` is *an* authoritative epoch for `s`. Proving that this predicate is
/// functional is `crate::ownership::proofs::fencing::theorem_unique_current_epoch`.
pub open spec fn is_authoritative_epoch(s: OwnershipState, e: Epoch) -> bool {
    match s {
        OwnershipState::Owned { owner: _, epoch } => e == epoch,
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch } => e == new_epoch,
        OwnershipState::Unowned { epoch, intended_owner: _ } => e == epoch,
    }
}

/// The fence check a server performs on an incoming request: reject anything
/// carrying an epoch that is behind the actor's current epoch.
pub open spec fn valid_fence(s: OwnershipState, e: Epoch) -> bool {
    e >= current_epoch(s)
}

/// `e` is strictly behind the actor's current epoch.
pub open spec fn is_stale(s: OwnershipState, e: Epoch) -> bool {
    e < current_epoch(s)
}

/// The authoritative epoch exists.
pub proof fn lemma_authoritative_epoch_exists(s: OwnershipState)
    ensures
        is_authoritative_epoch(s, current_epoch(s)),
{
    match s {
        OwnershipState::Owned { owner: _, epoch: _ } => {},
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch: _ } => {},
        OwnershipState::Unowned { epoch: _, intended_owner: _ } => {},
    }
}

/// The authoritative epoch is unique.
pub proof fn lemma_authoritative_epoch_unique(s: OwnershipState, e1: Epoch, e2: Epoch)
    requires
        is_authoritative_epoch(s, e1),
        is_authoritative_epoch(s, e2),
    ensures
        e1 == e2,
{
    match s {
        OwnershipState::Owned { owner: _, epoch: _ } => {},
        OwnershipState::Transferring { from: _, to: _, old_epoch: _, new_epoch: _ } => {},
        OwnershipState::Unowned { epoch: _, intended_owner: _ } => {},
    }
}

/// A stale epoch never passes the fence check.
pub proof fn lemma_stale_fails_fence(s: OwnershipState, e: Epoch)
    requires
        is_stale(s, e),
    ensures
        !valid_fence(s, e),
{
}

/// Beginning a transfer strictly advances the epoch, which is what fences the
/// outgoing owner.
pub proof fn lemma_begin_transfer_advances_epoch(
    from: Id,
    to: Id,
    old_epoch: Epoch,
)
    ensures
        current_epoch(
            OwnershipState::Transferring {
                from: from,
                to: to,
                old_epoch: old_epoch,
                new_epoch: old_epoch + 1,
            },
        ) > current_epoch(OwnershipState::Owned { owner: from, epoch: old_epoch }),
{
}

} // verus!
