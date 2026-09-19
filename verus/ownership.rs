// Formal Verus Specification for Exclusive Mutable Ownership
//
// This file formalizes the exclusive mutable ownership claim:
// "For every actor and reachable system state, if nodes A and B are both
//  permitted to mutate the actor, then A == B."
//
// This specification is meant to be verified with the Verus prover.
// Verification command: verus verus/ownership.rs

use vstd::prelude::*;

verus! {

pub type NodeId = u64;
pub type Epoch = u64;
pub type ActorId = u64;

/// The three possible ownership states for an actor
pub enum OwnershipState {
    /// Owned: Single node has exclusive authority at a specific epoch
    Owned {
        owner: NodeId,
        epoch: Epoch,
    },
    /// Transferring: Ownership in flight; neither node has authority
    Transferring {
        from: NodeId,
        to: NodeId,
        old_epoch: Epoch,
        new_epoch: Epoch,
    },
    /// Unowned: Transient state where no node has authority
    Unowned {
        epoch: Epoch,
        intended_owner: NodeId,
    },
}

// ============================================================================
// SPECIFICATION: may_mutate predicate
// ============================================================================

/// Specification of which node(s) can mutate an actor given its ownership state
pub open spec fn may_mutate_spec(state: OwnershipState, node: NodeId, epoch: Epoch) -> bool {
    match state {
        OwnershipState::Owned { owner, epoch: e } => owner == node && e == epoch,
        OwnershipState::Transferring { .. } => false,
        OwnershipState::Unowned { .. } => false,
    }
}

// ============================================================================
// LEMMA 1: Owned State - Only Owner Can Mutate
// ============================================================================

pub proof fn lemma_owned_only_owner_mutates(owner: NodeId, epoch: Epoch, node: NodeId, e: Epoch)
    ensures may_mutate_spec(OwnershipState::Owned { owner, epoch }, node, e) ==> (node == owner && e == epoch)
{
}

// ============================================================================
// LEMMA 2: Transferring State - No Mutation Allowed
// ============================================================================

pub proof fn lemma_transferring_no_mutate(
    from: NodeId,
    to: NodeId,
    old_epoch: Epoch,
    new_epoch: Epoch,
    node: NodeId,
    epoch: Epoch,
)
    ensures !may_mutate_spec(OwnershipState::Transferring { from, to, old_epoch, new_epoch }, node, epoch)
{
}

// ============================================================================
// LEMMA 3: Unowned State - No Mutation Allowed
// ============================================================================

pub proof fn lemma_unowned_no_mutate(
    epoch: Epoch,
    intended_owner: NodeId,
    node: NodeId,
    supplied_epoch: Epoch,
)
    ensures !may_mutate_spec(OwnershipState::Unowned { epoch, intended_owner }, node, supplied_epoch)
{
}

// ============================================================================
// THEOREM: Exclusive Mutable Ownership
// ============================================================================

/// Main safety property: For any state, at most one node can mutate at a time
pub proof fn theorem_exclusive_mutable_ownership(
    state: OwnershipState,
    node_a: NodeId,
    node_b: NodeId,
    epoch_a: Epoch,
    epoch_b: Epoch,
)
    requires
        may_mutate_spec(state, node_a, epoch_a) &&
        may_mutate_spec(state, node_b, epoch_b)
    ensures
        node_a == node_b && epoch_a == epoch_b
{
    match state {
        OwnershipState::Owned { owner, epoch } => {
            lemma_owned_only_owner_mutates(owner, epoch, node_a, epoch_a);
            lemma_owned_only_owner_mutates(owner, epoch, node_b, epoch_b);
            assert!(node_a == owner && epoch_a == epoch);
            assert!(node_b == owner && epoch_b == epoch);
        }
        OwnershipState::Transferring { from, to, old_epoch, new_epoch } => {
            lemma_transferring_no_mutate(from, to, old_epoch, new_epoch, node_a, epoch_a);
            assert!(false);
        }
        OwnershipState::Unowned { epoch, intended_owner } => {
            lemma_unowned_no_mutate(epoch, intended_owner, node_a, epoch_a);
            assert!(false);
        }
    }
}

} // verus!
