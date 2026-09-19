use crate::model::{ActorId, Epoch, NodeId, OwnershipState};

pub fn may_mutate(state: &OwnershipState, node: NodeId, epoch: Epoch) -> bool {
    match state {
        OwnershipState::Owned { owner, epoch: e } => *owner == node && *e == epoch,
        OwnershipState::Transferring { .. } => false,
        OwnershipState::Unowned { .. } => false,
    }
}

pub fn can_mutate_at_epoch(state: &OwnershipState, node: NodeId) -> bool {
    match state {
        OwnershipState::Owned { owner, .. } => *owner == node,
        OwnershipState::Transferring { .. } => false,
        OwnershipState::Unowned { .. } => false,
    }
}

#[cfg(test)]
mod exclusivity_tests {
    use super::*;

    #[test]
    fn test_only_owner_can_mutate() {
        let state = OwnershipState::Owned {
            owner: 1,
            epoch: 42,
        };

        assert!(may_mutate(&state, 1, 42));
        assert!(!may_mutate(&state, 2, 42));
        assert!(!may_mutate(&state, 1, 43));
    }

    #[test]
    fn test_no_mutation_during_transfer() {
        let state = OwnershipState::Transferring {
            from: 1,
            to: 2,
            old_epoch: 41,
            new_epoch: 42,
        };

        assert!(!may_mutate(&state, 1, 41));
        assert!(!may_mutate(&state, 2, 42));
        assert!(!may_mutate(&state, 1, 42));
        assert!(!may_mutate(&state, 2, 41));
    }

    #[test]
    fn test_no_mutation_when_unowned() {
        let state = OwnershipState::Unowned {
            epoch: 43,
            intended_owner: 2,
        };

        assert!(!may_mutate(&state, 1, 42));
        assert!(!may_mutate(&state, 2, 43));
        assert!(!may_mutate(&state, 2, 42));
    }

    #[test]
    fn test_mutually_exclusive_owners() {
        let state = OwnershipState::Owned {
            owner: 1,
            epoch: 42,
        };

        let node_1_can_mutate = may_mutate(&state, 1, 42);
        let node_2_can_mutate = may_mutate(&state, 2, 42);

        assert!(node_1_can_mutate);
        assert!(!node_2_can_mutate);
        assert!(!(node_1_can_mutate && node_2_can_mutate));
    }
}
