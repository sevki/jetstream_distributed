use crate::model::{Epoch, NodeId, OwnershipState};
use crate::ownership::may_mutate;

pub fn valid_fence(state: &OwnershipState, node: NodeId, epoch: Epoch) -> bool {
    epoch == state.current_epoch() && may_mutate(state, node, epoch)
}

pub fn current_epoch(state: &OwnershipState) -> Epoch {
    state.current_epoch()
}

pub fn is_stale_epoch(state: &OwnershipState, supplied_epoch: Epoch) -> bool {
    let curr_epoch = current_epoch(state);
    supplied_epoch < curr_epoch
}

pub fn stale_epoch_prevents_mutation(
    state: &OwnershipState,
    node: NodeId,
    supplied_epoch: Epoch,
) -> bool {
    is_stale_epoch(state, supplied_epoch) && !may_mutate(state, node, supplied_epoch)
}

#[cfg(test)]
mod fencing_tests {
    use super::*;

    #[test]
    fn test_current_epoch_extraction() {
        let owned_state = OwnershipState::Owned {
            owner: 1,
            epoch: 42,
        };
        assert_eq!(current_epoch(&owned_state), 42);

        let transferring_state = OwnershipState::Transferring {
            from: 1,
            to: 2,
            old_epoch: 41,
            new_epoch: 42,
        };
        assert_eq!(current_epoch(&transferring_state), 42);

        let unowned_state = OwnershipState::Unowned {
            epoch: 43,
            intended_owner: 2,
        };
        assert_eq!(current_epoch(&unowned_state), 43);
    }

    #[test]
    fn test_valid_fence_owned() {
        let state = OwnershipState::Owned {
            owner: 1,
            epoch: 42,
        };

        assert!(!valid_fence(&state, 1, 0));
        assert!(!valid_fence(&state, 1, 21));
        assert!(valid_fence(&state, 1, 42));
        assert!(!valid_fence(&state, 1, 43));
        assert!(!valid_fence(&state, 2, 42)); // node 2 cannot mutate even at current epoch
    }

    #[test]
    fn test_valid_fence_transferring() {
        let state = OwnershipState::Transferring {
            from: 1,
            to: 2,
            old_epoch: 41,
            new_epoch: 42,
        };

        assert!(!valid_fence(&state, 1, 0));
        assert!(!valid_fence(&state, 1, 40));
        assert!(!valid_fence(&state, 1, 41));
        assert!(!valid_fence(&state, 1, 42)); // neither party can mutate during transfer
        assert!(!valid_fence(&state, 2, 42)); // transfer destination cannot mutate either
        assert!(!valid_fence(&state, 1, 43));
    }

    #[test]
    fn test_stale_epoch_detection() {
        let state = OwnershipState::Owned {
            owner: 1,
            epoch: 42,
        };

        assert!(!is_stale_epoch(&state, 42)); // current epoch, not stale
        assert!(is_stale_epoch(&state, 41)); // past epoch, is stale
        assert!(!is_stale_epoch(&state, 43)); // future epoch, not stale
    }

    #[test]
    fn test_stale_owner_cannot_mutate() {
        let state = OwnershipState::Owned {
            owner: 1,
            epoch: 42,
        };

        let node_a = 1;

        assert!(may_mutate(&state, node_a, 42));
        assert!(!may_mutate(&state, node_a, 41));

        assert!(stale_epoch_prevents_mutation(&state, node_a, 41));

        let new_owner_state = OwnershipState::Owned {
            owner: 2,
            epoch: 43,
        };

        assert!(is_stale_epoch(&new_owner_state, 42));
        assert!(!may_mutate(&new_owner_state, 1, 42));
        assert!(stale_epoch_prevents_mutation(&new_owner_state, 1, 42));
    }

    #[test]
    fn test_transfer_with_epoch_advance() {
        let owned_state = OwnershipState::Owned {
            owner: 1,
            epoch: 41,
        };

        assert!(may_mutate(&owned_state, 1, 41));

        let transferring_state = OwnershipState::Transferring {
            from: 1,
            to: 2,
            old_epoch: 41,
            new_epoch: 42,
        };

        assert!(is_stale_epoch(&transferring_state, 41));
        assert!(!may_mutate(&transferring_state, 1, 41));

        let final_state = OwnershipState::Owned {
            owner: 2,
            epoch: 42,
        };

        assert!(may_mutate(&final_state, 2, 42));
        assert!(!may_mutate(&final_state, 1, 41));
    }

    #[test]
    fn test_epoch_monotonicity_in_transition() {
        let state1 = OwnershipState::Owned {
            owner: 1,
            epoch: 10,
        };
        let epoch1 = current_epoch(&state1);

        let state2 = OwnershipState::Transferring {
            from: 1,
            to: 2,
            old_epoch: 10,
            new_epoch: 11,
        };
        let epoch2 = current_epoch(&state2);

        assert!(epoch2 > epoch1);

        let state3 = OwnershipState::Owned {
            owner: 2,
            epoch: 11,
        };
        let epoch3 = current_epoch(&state3);

        assert!(epoch3 >= epoch2);
    }
}
