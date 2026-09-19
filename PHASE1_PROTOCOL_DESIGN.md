# Phase 1: Distributed Protocol Implementation

**Objective**: Build the actual network-based distributed ownership protocol using the verified state machine.

**Estimated Effort**: 3-4 weeks
**Prerequisite**: PRODUCTION_READINESS.md Phase 0 (Verus verification)

---

## Overview

Currently, we have a state machine that is **correct** (safety proven) but **not distributed** (no network, no concurrency, no message passing). Phase 1 bridges this gap by:

1. Implementing jetstream wire format messages (mandatory for production)
2. Adding network transport using jetstream wire protocol
3. Building the actual Raymond token routing algorithm
4. Coordinating transfers across nodes
5. Handling concurrent requests and failures

**Critical Constraint**: All message serialization MUST use the jetstream wire format. This is a hard requirement, not an implementation detail.

---

## Architecture

### Current (State Machine Only)

```
┌─────────────────────┐
│  OwnershipState     │
│  (in-memory)        │
│                     │
│  Owned              │
│  Transferring       │
│  Unowned            │
└─────────────────────┘
       │
       │ validate
       ▼
┌─────────────────────┐
│  apply_transition() │ (all in single process)
└─────────────────────┘
```

### Phase 1 (Distributed)

```
┌──────────┐
│ Node A   │
│ ─────────│
│ Actor X  │  
│ Owned    │  ◄─── Owner (can mutate)
└──────────┘
     │
     │ Epoch 41
     │
     ▼
  Network
  (gRPC)
     ▲
     │
     │ Transfer to B at epoch 42
     │
     ▼
┌──────────┐
│ Node B   │
│ ─────────│
│ Actor X  │  
│ Unowned  │  ◄─── Wait for ownership
└──────────┘
```

---

## Work Breakdown

### 1. Implement Jetstream Wire Format Messages

**Critical**: All messages MUST use the jetstream wire format. This is not a choice—it's a mandatory constraint for production deployment.

Create `src/wire/mod.rs` to define ownership messages using jetstream wire format:

```rust
// Messages encoded/decoded using jetstream wire format
pub struct TransferRequest {
    pub actor_id: ActorId,
    pub requester_node_id: NodeId,
    pub current_epoch: Epoch,
}

pub struct TransferResponse {
    pub accepted: bool,
    pub new_epoch: Epoch,
    pub reason: Option<String>,
}

pub struct TransferNotification {
    pub actor_id: ActorId,
    pub from_node_id: NodeId,
    pub to_node_id: NodeId,
    pub new_epoch: Epoch,
}

pub struct TransferAck {
    pub acknowledged: bool,
    pub actor_id: ActorId,
}

// Implement jetstream wire format serialization/deserialization
impl JetstreamSerializable for TransferRequest {
    fn to_bytes(&self) -> Result<Vec<u8>> { /* ... */ }
    fn from_bytes(data: &[u8]) -> Result<Self> { /* ... */ }
}
// ... similar for other message types
```

**Effort**: 2-3 days (depends on jetstream wire format complexity and existing codec availability)
**Key Decision**: Understand jetstream wire format spec before starting. Codec must be 100% compatible for interop.

---

### 2. Implement Transport Layer (Jetstream Wire Protocol)

Create `src/transport/mod.rs` using jetstream wire format for message serialization:

```rust
pub trait OwnershipTransport {
    async fn send_message(
        &self,
        target: NodeId,
        message: JetstreamMessage,
    ) -> Result<(), TransportError>;
    
    async fn receive_message(
        &self,
    ) -> Result<JetstreamMessage, TransportError>;
}

pub struct JetstreamTransport {
    node_id: NodeId,
    connections: HashMap<NodeId, JetstreamConnection>,
    server_handle: ServerHandle,
}

impl JetstreamTransport {
    pub async fn new(
        node_id: NodeId,
        listen_addr: String,
    ) -> Result<Self> {
        // Start jetstream wire protocol server
        // Create connection pool using jetstream wire format codec
        // All message serialization uses jetstream format
    }
    
    async fn request_transfer(
        &self,
        target: NodeId,
        req: TransferRequest,
    ) -> Result<TransferResponse, TransportError> {
        let wire_msg = req.to_jetstream_bytes()?;
        self.send_message(target, wire_msg).await?;
        // Receive response, deserialize using jetstream codec
    }
}
```

**Effort**: 3-4 days
**Key Decisions**:
- Use jetstream wire format codec (NOT gRPC/HTTP)
- Async/await with Tokio
- Connection pooling using jetstream connections
- Timeouts for RPC calls (default: 5s)
- Retry strategy for transient failures
- **MUST be compatible with existing jetstream ecosystem**

---

### 3. Implement Local Ownership Manager

Create `src/manager.rs`:

```rust
pub struct OwnershipManager {
    system: ActorSystem,
    transport: Arc<dyn OwnershipTransport>,
    node_id: NodeId,
    pending_transfers: HashMap<ActorId, TransferInProgress>,
}

impl OwnershipManager {
    pub async fn request_ownership(
        &mut self,
        actor_id: ActorId,
    ) -> Result<(), OwnershipError> {
        // 1. Find current owner from local state
        // 2. Send transfer request via transport
        // 3. Wait for transfer completion
        // 4. Update local state
    }
    
    pub async fn handle_transfer_request(
        &mut self,
        req: TransferRequest,
    ) -> Result<Epoch, OwnershipError> {
        // 1. Validate current ownership
        // 2. Check epoch is monotonically increasing
        // 3. Transition to Transferring state
        // 4. Return new epoch
    }
    
    pub fn can_mutate(&self, actor_id: ActorId, epoch: Epoch) -> bool {
        match self.system.get_actor_state(actor_id) {
            Some(state) => may_mutate(state, self.node_id, epoch),
            None => false,
        }
    }
}
```

**Effort**: 4-5 days
**Key Challenges**:
- Handling concurrent transfer requests for same actor
- Timeout and retry for failed RPC calls
- Atomic state transitions (at least from protocol perspective)
- Detecting and recovering from partial failures

---

### 4. Implement Request Routing (Raymond's Algorithm)

Create `src/routing.rs`:

```rust
pub struct RequestRouter {
    holder_pointers: HashMap<ActorId, NodeId>,
    request_queues: HashMap<ActorId, VecDeque<TokenRequest>>,
    parent: HashMap<ActorId, NodeId>,  // Tree structure for routing
}

impl RequestRouter {
    pub async fn route_request(
        &mut self,
        actor_id: ActorId,
        from: NodeId,
    ) -> Result<Epoch, RoutingError> {
        // 1. Check if we hold the token (holder_pointers)
        // 2. If yes: process request immediately
        // 3. If no: route toward holder via parent pointer
        // 4. Maintain request queue for fairness
    }
    
    pub async fn transfer_token(
        &mut self,
        actor_id: ActorId,
        new_holder: NodeId,
    ) -> Result<(), RoutingError> {
        // 1. Update holder_pointers
        // 2. Send token to new holder
        // 3. Process queued requests
    }
}
```

**Effort**: 3-4 days
**Key Challenges**:
- Building dynamic tree topology
- Handling token loss (node crashes)
- Request fairness (FIFO per actor)

---

### 5. Failure Recovery

Create `src/recovery.rs`:

```rust
pub struct FailureDetector {
    heartbeat_interval: Duration,
    heartbeat_timeout: Duration,
    failure_threshold: usize,
}

impl FailureDetector {
    pub async fn detect_failures(&self) -> Vec<NodeId> {
        // 1. Send periodic heartbeats
        // 2. Track failed heartbeats per node
        // 3. Mark node as down after threshold
        // 4. Return list of failed nodes
    }
}

pub async fn recover_from_node_failure(
    manager: &mut OwnershipManager,
    failed_node: NodeId,
) -> Result<(), RecoveryError> {
    // 1. Find actors owned by failed node
    // 2. Transition to Unowned state
    // 3. Re-route requests to alternative owners
    // 4. Rebuild tree structure
}
```

**Effort**: 3-4 days
**Key Challenges**:
- False positive detection (network delays)
- Handling cascading failures
- Rebuilding state after recovery
- Detecting split-brain scenarios

---

### 6. Integration Tests

Create `tests/integration_test.rs`:

```rust
#[tokio::test]
async fn test_two_node_transfer() {
    let mut manager_a = OwnershipManager::new(1, transport.clone());
    let mut manager_b = OwnershipManager::new(2, transport.clone());
    
    // Create actor owned by A
    manager_a.create_actor(100, epoch(1));
    assert!(manager_a.can_mutate(100, epoch(1)));
    
    // Request transfer to B
    manager_b.request_ownership(100).await.unwrap();
    
    // Verify B owns it after transfer
    assert!(manager_b.can_mutate(100, epoch(2)));
    assert!(!manager_a.can_mutate(100, epoch(1)));
}

#[tokio::test]
async fn test_failure_and_recovery() {
    // Simulate node failure, verify recovery
}

#[tokio::test]
async fn test_concurrent_transfer_requests() {
    // Multiple nodes request same actor simultaneously
    // Verify only one succeeds
}
```

**Effort**: 2-3 days
**Tests Needed**:
- Simple two-node transfer
- Multi-node chain transfers
- Failure and recovery
- Concurrent requests
- Network partitions (if possible to simulate)

---

## Implementation Order

1. **Week 1**: Jetstream Wire Format + Transport Layer
   - Understand and implement jetstream wire format codec
   - Create message types compatible with jetstream wire protocol
   - Build jetstream transport layer (connections, serialization, error handling)
   - **BLOCKER**: Must have 100% correct jetstream wire format implementation

2. **Week 2**: Ownership Manager
   - State machine integration with jetstream transport
   - Transfer request handling with wire format serialization
   - Concurrent request coordination

3. **Week 3**: Routing Algorithm
   - Token routing implementation using jetstream messages
   - Request queue management
   - Tree topology management

4. **Week 4**: Failure handling + Integration tests
   - Failure detection
   - Recovery procedures
   - End-to-end testing with jetstream wire format validation

---

## Testing Strategy

### Unit Tests (per module)

```bash
cargo test --test integration_test
```

### Integration Tests

- Two nodes, simple transfer
- Three nodes, chain transfer
- Concurrent requests to same actor
- Simulated node failure and recovery

### Scenario Tests

- Network delay (simulate with tokio::time::sleep)
- Message reordering (queue randomization)
- Timeouts and retries

### Benchmarks

```bash
cargo bench
```

Key metrics:
- Transfer latency (p50, p99)
- Throughput (transfers/sec)
- Message overhead per transfer

---

## Key Design Decisions

### 1. Jetstream Wire Format (MANDATORY)

**Decision**: Use jetstream wire format for all message serialization
- **Pros**: Mandatory for production interoperability with jetstream ecosystem
- **Cons**: Requires learning jetstream wire format specification
- **No Alternatives**: This is a hard requirement, not optional
- **Risk**: Wire format implementation bugs break interop—must be thoroughly tested

### 2. Async/Await with Tokio

**Decision**: Use async Tokio runtime with jetstream wire protocol
- **Pros**: Efficient concurrent I/O, standard Rust ecosystem
- **Cons**: More complex than sync code
- **Alternative**: Sync with thread pool (simpler but less scalable)

### 3. Soft State with Timeouts

**Decision**: Assume eventual consistency, use timeouts for failures
- **Pros**: Handles network delays, simple recovery
- **Cons**: Must ensure safety even with delayed messages
- **Guarantee**: Epoch monotonicity ensures safety holds

### 4. Tree-Based Token Routing (Raymond's)

**Decision**: Use dynamic tree structure for token routing
- **Pros**: Optimal (O(log N) hops per request with balancing)
- **Cons**: Requires maintaining tree structure
- **Alternative**: Broadcast (simpler, but O(N) messages)

---

## Error Handling Strategy

```rust
#[derive(Debug)]
pub enum OwnershipError {
    NotOwner,
    EpochMismatch,
    TransportError(String),
    Timeout,
    ConcurrentTransfer,
    InvalidStateTransition,
}
```

**Policy**:
- Transient errors (timeout, network): Retry with backoff
- Logic errors (not owner, epoch mismatch): Propagate to caller
- Fatal errors (invalid transition): Panic (indicates bug)

---

## Monitoring and Observability

Add metrics:

```rust
lazy_static::lazy_static! {
    static ref TRANSFER_DURATION: Histogram = /* ... */;
    static ref CONCURRENT_TRANSFERS: Gauge = /* ... */;
    static ref FAILED_TRANSFERS: Counter = /* ... */;
}
```

Log events:
- Transfer requested
- Transfer approved
- Transfer completed
- Node failure detected
- Recovery initiated

---

## Safety Verification

After implementation, verify:

1. **State Machine Safety Unchanged**
   - Existing 33 tests still pass
   - No new mutations to OwnershipState logic

2. **No Concurrent Mutations**
   - Impossible for two nodes to mutate simultaneously
   - Verified by existing tests + integration tests

3. **Epoch Monotonicity Preserved**
   - Every transfer increases epoch
   - No epoch rollbacks after network failures

4. **Failure Resilience**
   - Stale owners can't mutate after failure recovery
   - Tested by `test_failure_and_recovery`

---

## Cost Analysis

| Phase | Duration | Effort | Risk |
|-------|----------|--------|------|
| Protocol definition | 1 day | Low | Low |
| Transport layer | 3-4 days | Medium | Medium |
| Ownership manager | 4-5 days | High | High |
| Routing algorithm | 3-4 days | High | High |
| Failure recovery | 3-4 days | High | Medium |
| Integration tests | 2-3 days | Medium | Low |
| **Total** | **3-4 weeks** | **High** | **Medium** |

---

## Success Criteria

Phase 1 is complete when:
- ✅ All 33 original tests still pass
- ✅ Two-node transfer works end-to-end
- ✅ Multi-node chain transfers work
- ✅ Concurrent requests handled correctly
- ✅ Failure detection and recovery works
- ✅ Integration tests cover all major scenarios
- ✅ No clippy warnings or formatting issues
- ✅ Documentation updated

---

## Optional: Phase 1.5 - Local Testing

Before full Phase 1 implementation, consider a local-only version:

```rust
pub struct LocalOwnershipCluster {
    nodes: HashMap<NodeId, OwnershipManager>,
}

impl LocalOwnershipCluster {
    pub async fn new_test_cluster(node_count: usize) -> Self {
        // Create N nodes with in-memory messaging
        // Useful for testing routing and failure scenarios
    }
}
```

**Advantage**: Test distributed logic without gRPC setup
**Effort**: 1-2 days
**Value**: Catch distributed bugs early, easier to debug

---

## Next Step

Once PRODUCTION_READINESS.md Phase 0 is complete (Verus verification), Phase 1 can begin. The implementation order above ensures:

1. Incrementally building complexity
2. Testing at each stage
3. Maintaining safety invariants
4. Clear integration points

**Recommendation**: Start with a 1-week spike focused on prototype transport layer and basic two-node transfer. This will reveal unknowns and refine the estimate.
