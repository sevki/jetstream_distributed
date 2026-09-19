use std::collections::HashMap;

pub type ActorId = u64;
pub type NodeId = u64;
pub type Epoch = u64;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OwnershipState {
    Owned {
        owner: NodeId,
        epoch: Epoch,
    },
    Transferring {
        from: NodeId,
        to: NodeId,
        old_epoch: Epoch,
        new_epoch: Epoch,
    },
    Unowned {
        epoch: Epoch,
        intended_owner: NodeId,
    },
}

impl OwnershipState {
    pub fn current_epoch(&self) -> Epoch {
        match self {
            OwnershipState::Owned { epoch, .. } => *epoch,
            OwnershipState::Transferring { new_epoch, .. } => *new_epoch,
            OwnershipState::Unowned { epoch, .. } => *epoch,
        }
    }

    pub fn is_valid(&self) -> bool {
        match self {
            OwnershipState::Owned { owner, epoch } => *owner != 0 && *epoch > 0,
            OwnershipState::Transferring {
                from,
                to,
                old_epoch,
                new_epoch,
            } => {
                *from != 0
                    && *to != 0
                    && *from != *to
                    && *old_epoch > 0
                    && *old_epoch < *new_epoch
                    && *new_epoch > 0
            }
            OwnershipState::Unowned {
                epoch,
                intended_owner,
            } => *epoch > 0 && *intended_owner != 0,
        }
    }
}

pub struct ActorSystem {
    actors: HashMap<ActorId, OwnershipState>,
}

impl ActorSystem {
    pub fn new() -> Self {
        ActorSystem {
            actors: HashMap::new(),
        }
    }

    pub fn create_actor(
        &mut self,
        actor_id: ActorId,
        initial_owner: NodeId,
        epoch: Epoch,
    ) -> Result<(), &'static str> {
        if initial_owner == 0 || epoch == 0 {
            return Err("invalid initial owner or epoch");
        }
        if self.actors.contains_key(&actor_id) {
            return Err("actor already exists");
        }
        let state = OwnershipState::Owned {
            owner: initial_owner,
            epoch,
        };
        self.actors.insert(actor_id, state);
        Ok(())
    }

    pub fn get_actor_state(&self, actor_id: ActorId) -> Option<&OwnershipState> {
        self.actors.get(&actor_id)
    }

    pub(crate) fn update_actor_state(
        &mut self,
        actor_id: ActorId,
        new_state: OwnershipState,
    ) -> Result<(), &'static str> {
        if !new_state.is_valid() {
            return Err("invalid new state");
        }
        if !self.actors.contains_key(&actor_id) {
            return Err("actor does not exist");
        }
        self.actors.insert(actor_id, new_state);
        Ok(())
    }

    pub fn is_valid(&self) -> bool {
        self.actors.values().all(|state| state.is_valid())
    }
}

impl Default for ActorSystem {
    fn default() -> Self {
        Self::new()
    }
}
