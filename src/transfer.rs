use crate::fencing::{current_epoch, is_stale_epoch};
use crate::model::{ActorId, ActorSystem, Epoch, NodeId, OwnershipState};
use crate::ownership::may_mutate;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransitionError {
    InvalidSourceState,
    EpochNotIncreasing,
    InvalidNodeIds,
}

pub fn transition_owned_to_transferring(
    from: NodeId,
    to: NodeId,
    old_epoch: Epoch,
    new_epoch: Epoch,
) -> Result<OwnershipState, TransitionError> {
    if from == 0 || to == 0 || from == to {
        return Err(TransitionError::InvalidNodeIds);
    }
    if new_epoch <= old_epoch {
        return Err(TransitionError::EpochNotIncreasing);
    }
    Ok(OwnershipState::Transferring {
        from,
        to,
        old_epoch,
        new_epoch,
    })
}

pub fn transition_transferring_to_unowned(
    from: NodeId,
    to: NodeId,
    old_epoch: Epoch,
    new_epoch: Epoch,
) -> Result<OwnershipState, TransitionError> {
    if from == 0 || to == 0 || from == to {
        return Err(TransitionError::InvalidNodeIds);
    }
    if new_epoch <= old_epoch {
        return Err(TransitionError::EpochNotIncreasing);
    }
    Ok(OwnershipState::Unowned {
        epoch: new_epoch,
        intended_owner: to,
    })
}

pub fn transition_unowned_to_owned(
    to: NodeId,
    new_epoch: Epoch,
    old_epoch: Epoch,
) -> Result<OwnershipState, TransitionError> {
    if to == 0 {
        return Err(TransitionError::InvalidNodeIds);
    }
    if new_epoch <= old_epoch {
        return Err(TransitionError::EpochNotIncreasing);
    }
    Ok(OwnershipState::Owned {
        owner: to,
        epoch: new_epoch,
    })
}

pub fn transfer_preserves_mutual_exclusion(
    initial_state: &OwnershipState,
    intermediate_state: &OwnershipState,
    final_state: &OwnershipState,
    source_node: NodeId,
    dest_node: NodeId,
    epoch_a: Epoch,
    epoch_b: Epoch,
) -> bool {
    if source_node == dest_node || source_node == 0 || dest_node == 0 || epoch_b <= epoch_a {
        return false;
    }

    let initial_valid = matches!(initial_state, OwnershipState::Owned { owner, epoch } if *owner == source_node && *epoch == epoch_a);

    let intermediate_valid = matches!(
        intermediate_state,
        OwnershipState::Transferring {
            from,
            to,
            old_epoch,
            new_epoch
        } if *from == source_node && *to == dest_node && *old_epoch == epoch_a && *new_epoch == epoch_b
    );

    let final_valid = matches!(final_state, OwnershipState::Owned { owner, epoch } if *owner == dest_node && *epoch == epoch_b);

    let no_concurrent_mutators = {
        !may_mutate(intermediate_state, source_node, epoch_a)
            && !may_mutate(intermediate_state, dest_node, epoch_b)
    };

    initial_valid && intermediate_valid && final_valid && no_concurrent_mutators
}

pub fn stale_token_cannot_authorize_mutation(
    state_before: &OwnershipState,
    state_after: &OwnershipState,
    stale_owner: NodeId,
    stale_epoch: Epoch,
) -> bool {
    let valid_transfer = {
        match (state_before, state_after) {
            (
                OwnershipState::Owned {
                    owner: o1,
                    epoch: e1,
                },
                OwnershipState::Owned {
                    owner: o2,
                    epoch: e2,
                },
            ) => o1 != o2 && e1 < e2 && *o1 == stale_owner && stale_epoch == *e1,
            _ => false,
        }
    };

    let stale_cannot_mutate = !may_mutate(state_after, stale_owner, stale_epoch);

    valid_transfer && stale_cannot_mutate
}

pub fn apply_transition(
    system: &mut ActorSystem,
    actor_id: ActorId,
    new_state: OwnershipState,
) -> Result<(), TransitionError> {
    if !new_state.is_valid() {
        return Err(TransitionError::InvalidSourceState);
    }

    if let Some(current_state) = system.get_actor_state(actor_id) {
        let curr_epoch = current_epoch(current_state);
        let new_epoch = new_state.current_epoch();

        if new_epoch < curr_epoch {
            return Err(TransitionError::EpochNotIncreasing);
        }

        let is_legal_transition = match (current_state, &new_state) {
            (
                OwnershipState::Owned {
                    owner: from,
                    epoch: _,
                },
                OwnershipState::Transferring {
                    from: tf,
                    old_epoch,
                    new_epoch: ne,
                    ..
                },
            ) => *from == *tf && curr_epoch == *old_epoch && *ne > *old_epoch,
            (
                OwnershipState::Transferring {
                    from: _,
                    to,
                    old_epoch: _,
                    new_epoch: ne,
                },
                OwnershipState::Unowned {
                    epoch: ue,
                    intended_owner,
                },
            ) => *ue == *ne && *intended_owner == *to,
            (
                OwnershipState::Unowned {
                    epoch: ue,
                    intended_owner,
                },
                OwnershipState::Owned { owner, epoch: oe },
            ) => *owner == *intended_owner && *oe == *ue,
            _ => false,
        };

        if !is_legal_transition {
            return Err(TransitionError::InvalidSourceState);
        }

        system
            .update_actor_state(actor_id, new_state)
            .map_err(|_| TransitionError::InvalidSourceState)
    } else {
        Err(TransitionError::InvalidSourceState)
    }
}

#[cfg(test)]
mod transfer_tests {
    use super::*;

    #[test]
    fn test_transition_owned_to_transferring() {
        let result = transition_owned_to_transferring(1, 2, 41, 42);
        assert!(result.is_ok());

        let state = result.unwrap();
        assert!(matches!(
            state,
            OwnershipState::Transferring {
                from: 1,
                to: 2,
                old_epoch: 41,
                new_epoch: 42
            }
        ));
    }

    #[test]
    fn test_transition_rejects_non_increasing_epoch() {
        let result = transition_owned_to_transferring(1, 2, 42, 41);
        assert_eq!(result, Err(TransitionError::EpochNotIncreasing));

        let result = transition_owned_to_transferring(1, 2, 42, 42);
        assert_eq!(result, Err(TransitionError::EpochNotIncreasing));
    }

    #[test]
    fn test_transition_rejects_same_node() {
        let result = transition_owned_to_transferring(1, 1, 41, 42);
        assert_eq!(result, Err(TransitionError::InvalidNodeIds));
    }

    #[test]
    fn test_transition_rejects_zero_node() {
        let result = transition_owned_to_transferring(0, 2, 41, 42);
        assert_eq!(result, Err(TransitionError::InvalidNodeIds));

        let result = transition_owned_to_transferring(1, 0, 41, 42);
        assert_eq!(result, Err(TransitionError::InvalidNodeIds));
    }

    #[test]
    fn test_full_transfer_sequence() {
        let state_owned = OwnershipState::Owned {
            owner: 1,
            epoch: 41,
        };

        let state_transferring = transition_owned_to_transferring(1, 2, 41, 42).unwrap();

        let _state_unowned = transition_transferring_to_unowned(1, 2, 41, 42).unwrap();

        let state_final = transition_unowned_to_owned(2, 42, 41).unwrap();

        assert!(transfer_preserves_mutual_exclusion(
            &state_owned,
            &state_transferring,
            &state_final,
            1,
            2,
            41,
            42
        ));
    }

    #[test]
    fn test_no_concurrent_mutation_during_transfer() {
        let state_transferring = OwnershipState::Transferring {
            from: 1,
            to: 2,
            old_epoch: 41,
            new_epoch: 42,
        };

        assert!(!may_mutate(&state_transferring, 1, 41));
        assert!(!may_mutate(&state_transferring, 2, 42));
        assert!(!may_mutate(&state_transferring, 1, 42));
        assert!(!may_mutate(&state_transferring, 2, 41));
    }

    #[test]
    fn test_stale_token_fencing() {
        let state_before = OwnershipState::Owned {
            owner: 1,
            epoch: 41,
        };

        let state_after = OwnershipState::Owned {
            owner: 2,
            epoch: 42,
        };

        assert!(stale_token_cannot_authorize_mutation(
            &state_before,
            &state_after,
            1,
            41
        ));
    }

    #[test]
    fn test_system_transitions() {
        let mut system = ActorSystem::new();
        let actor = 100u64;

        system.create_actor(actor, 1, 1).unwrap();
        let initial_state = OwnershipState::Owned { owner: 1, epoch: 1 };
        assert!(matches!(system.get_actor_state(actor), Some(state) if state == &initial_state));

        let transferring_state = transition_owned_to_transferring(1, 2, 1, 2).unwrap();
        assert!(apply_transition(&mut system, actor, transferring_state.clone()).is_ok());

        let unowned_state = transition_transferring_to_unowned(1, 2, 1, 2).unwrap();
        assert!(apply_transition(&mut system, actor, unowned_state.clone()).is_ok());

        let final_state = transition_unowned_to_owned(2, 2, 1).unwrap();
        assert!(apply_transition(&mut system, actor, final_state.clone()).is_ok());

        let final_stored = system.get_actor_state(actor).unwrap();
        assert_eq!(final_stored, &final_state);
    }

    #[test]
    fn test_transition_rejects_epoch_decrease() {
        let mut system = ActorSystem::new();
        let actor = 100u64;

        system.create_actor(actor, 1, 10).unwrap();

        let bad_state = OwnershipState::Owned { owner: 2, epoch: 5 };
        let result = apply_transition(&mut system, actor, bad_state);
        assert_eq!(result, Err(TransitionError::EpochNotIncreasing));
    }

    #[test]
    fn test_interrupted_transfer_scenario() {
        let state_a_owns = OwnershipState::Owned {
            owner: 1,
            epoch: 41,
        };

        let state_transferring_to_b = OwnershipState::Transferring {
            from: 1,
            to: 2,
            old_epoch: 41,
            new_epoch: 42,
        };

        let state_b_owns = OwnershipState::Owned {
            owner: 2,
            epoch: 42,
        };

        assert!(may_mutate(&state_a_owns, 1, 41));
        assert!(!may_mutate(&state_transferring_to_b, 1, 41));
        assert!(!may_mutate(&state_transferring_to_b, 2, 42));
        assert!(may_mutate(&state_b_owns, 2, 42));
        assert!(!may_mutate(&state_b_owns, 1, 41));

        assert!(transfer_preserves_mutual_exclusion(
            &state_a_owns,
            &state_transferring_to_b,
            &state_b_owns,
            1,
            2,
            41,
            42
        ));
    }
}
