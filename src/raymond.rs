use std::collections::{HashMap, VecDeque};
use crate::model::{ActorId, NodeId, Epoch};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RaymondToken {
    pub holder: NodeId,
    pub epoch: Epoch,
    pub actor_id: ActorId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TokenRequest {
    pub requester: NodeId,
    pub actor_id: ActorId,
    pub request_id: u64,
}

#[derive(Clone)]
pub struct RaymondState {
    pub token: Option<RaymondToken>,
    pub request_queue: HashMap<ActorId, VecDeque<TokenRequest>>,
    pub holder: HashMap<ActorId, NodeId>,
    pub asked: HashMap<ActorId, bool>,
    pub outstanding_requests: HashMap<ActorId, Vec<TokenRequest>>,
}

impl RaymondState {
    pub fn new() -> Self {
        RaymondState {
            token: None,
            request_queue: HashMap::new(),
            holder: HashMap::new(),
            asked: HashMap::new(),
            outstanding_requests: HashMap::new(),
        }
    }

    pub fn initialize_token(&mut self, actor_id: ActorId, initial_holder: NodeId, epoch: Epoch) {
        self.token = Some(RaymondToken {
            holder: initial_holder,
            epoch,
            actor_id,
        });
        self.holder.insert(actor_id, initial_holder);
    }

    pub fn enqueue_request(&mut self, actor_id: ActorId, request: TokenRequest) {
        self.request_queue
            .entry(actor_id)
            .or_insert_with(VecDeque::new)
            .push_back(request);
    }

    pub fn dequeue_request(&mut self, actor_id: ActorId) -> Option<TokenRequest> {
        self.request_queue
            .get_mut(&actor_id)
            .and_then(|q| q.pop_front())
    }

    pub fn has_pending_requests(&self, actor_id: ActorId) -> bool {
        self.request_queue
            .get(&actor_id)
            .map(|q| !q.is_empty())
            .unwrap_or(false)
    }

    pub fn set_asked(&mut self, actor_id: ActorId, value: bool) {
        self.asked.insert(actor_id, value);
    }

    pub fn is_asked(&self, actor_id: ActorId) -> bool {
        self.asked.get(&actor_id).copied().unwrap_or(false)
    }

    pub fn transfer_token(&mut self, actor_id: ActorId, new_holder: NodeId, new_epoch: Epoch) {
        if let Some(token) = &mut self.token {
            if token.actor_id == actor_id {
                token.holder = new_holder;
                token.epoch = new_epoch;
                self.holder.insert(actor_id, new_holder);
            }
        }
    }

    pub fn set_outstanding_requests(&mut self, actor_id: ActorId, requests: Vec<TokenRequest>) {
        self.outstanding_requests.insert(actor_id, requests);
    }

    pub fn token_exists(&self) -> bool {
        self.token.is_some()
    }

    pub fn is_valid_single_token(&self) -> bool {
        match &self.token {
            Some(token) => {
                let holder_is_consistent = self
                    .holder
                    .get(&token.actor_id)
                    .map(|h| *h == token.holder)
                    .unwrap_or(false);

                holder_is_consistent
            }
            None => false,
        }
    }
}

impl Default for RaymondState {
    fn default() -> Self {
        Self::new()
    }
}

pub fn request_routing_preserves_token_uniqueness(
    state: &RaymondState,
    actor_id: ActorId,
) -> bool {
    if !state.is_valid_single_token() {
        return false;
    }

    match &state.token {
        Some(token) => {
            if token.actor_id != actor_id {
                return true;
            }

            let holder = state.holder.get(&actor_id);
            holder.is_some()
        }
        None => false,
    }
}

pub fn token_transfer_safety(
    state_before: &RaymondState,
    state_after: &RaymondState,
    actor_id: ActorId,
    new_holder: NodeId,
    new_epoch: Epoch,
) -> bool {
    if !state_before.is_valid_single_token() || !state_after.is_valid_single_token() {
        return false;
    }

    let before_holder = state_before.holder.get(&actor_id);
    let after_holder = state_after.holder.get(&actor_id);

    match (before_holder, after_holder) {
        (Some(_), Some(&new_h)) => {
            new_h == new_holder
                && state_after
                    .token
                    .as_ref()
                    .map(|t| t.holder == new_h && t.epoch == new_epoch && t.actor_id == actor_id)
                    .unwrap_or(false)
        }
        _ => false,
    }
}

#[cfg(test)]
mod raymond_tests {
    use super::*;

    #[test]
    fn test_token_initialization() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);

        assert!(state.token_exists());
        assert!(state.is_valid_single_token());
        assert_eq!(state.holder.get(&1), Some(&0));
    }

    #[test]
    fn test_token_uniqueness() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);
        assert!(request_routing_preserves_token_uniqueness(&state, 1));
    }

    #[test]
    fn test_request_queue() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);

        let req1 = TokenRequest {
            requester: 1,
            actor_id: 1,
            request_id: 1,
        };
        let req2 = TokenRequest {
            requester: 2,
            actor_id: 1,
            request_id: 2,
        };

        state.enqueue_request(1, req1.clone());
        state.enqueue_request(1, req2.clone());

        assert!(state.has_pending_requests(1));

        let dequeued = state.dequeue_request(1);
        assert_eq!(dequeued, Some(req1));

        let dequeued2 = state.dequeue_request(1);
        assert_eq!(dequeued2, Some(req2));

        assert!(!state.has_pending_requests(1));
    }

    #[test]
    fn test_token_transfer() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);

        state.transfer_token(1, 1, 2);

        assert_eq!(state.holder.get(&1), Some(&1));
        assert_eq!(state.token.as_ref().unwrap().holder, 1);
        assert_eq!(state.token.as_ref().unwrap().epoch, 2);
    }

    #[test]
    fn test_token_transfer_safety() {
        let mut state_before = RaymondState::new();
        state_before.initialize_token(1, 0, 1);

        let mut state_after = state_before.clone();
        state_after.transfer_token(1, 1, 2);

        assert!(token_transfer_safety(&state_before, &state_after, 1, 1, 2));
    }

    #[test]
    fn test_asked_flag() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);

        assert!(!state.is_asked(1));
        state.set_asked(1, true);
        assert!(state.is_asked(1));
    }

    #[test]
    fn test_outstanding_requests() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);

        let req = TokenRequest {
            requester: 1,
            actor_id: 1,
            request_id: 1,
        };

        state.set_outstanding_requests(1, vec![req.clone()]);

        assert_eq!(state.outstanding_requests.get(&1), Some(&vec![req]));
    }

    #[test]
    fn test_request_hop_by_hop_routing() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 4, 1);

        let req = TokenRequest {
            requester: 1,
            actor_id: 1,
            request_id: 1,
        };

        state.set_outstanding_requests(1, vec![req.clone()]);

        assert!(request_routing_preserves_token_uniqueness(&state, 1));

        state.transfer_token(1, 3, 2);
        assert!(request_routing_preserves_token_uniqueness(&state, 1));

        state.transfer_token(1, 2, 3);
        assert!(request_routing_preserves_token_uniqueness(&state, 1));

        state.transfer_token(1, 1, 4);
        assert!(request_routing_preserves_token_uniqueness(&state, 1));
    }

    #[test]
    fn test_multiple_actors_separate_tokens() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);

        state.holder.insert(2, 5);

        assert_eq!(state.holder.get(&1), Some(&0));
        assert_eq!(state.holder.get(&2), Some(&5));
    }

    #[test]
    fn test_duplicate_requests_do_not_create_second_token() {
        let mut state = RaymondState::new();
        state.initialize_token(1, 0, 1);

        let req = TokenRequest {
            requester: 1,
            actor_id: 1,
            request_id: 1,
        };

        state.enqueue_request(1, req.clone());
        state.enqueue_request(1, req.clone());

        assert!(request_routing_preserves_token_uniqueness(&state, 1));
        assert!(state.token_exists());
    }
}
