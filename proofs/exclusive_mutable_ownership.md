# Exclusive Mutable Ownership Proof

**Claim**: For every actor and reachable system state, if nodes A and B are both permitted to mutate the actor, then A == B.

**Formal Statement**:
```
∀ state: OwnershipState, node_a: NodeId, epoch_a: Epoch, node_b: NodeId, epoch_b: Epoch.
  may_mutate(state, node_a, epoch_a) ∧ may_mutate(state, node_b, epoch_b)
    ⟹ (node_a = node_b ∧ epoch_a = epoch_b)
```

## Proof Strategy

We prove this by exhaustive case analysis on the three possible ownership states.

### Definition of `may_mutate`

```rust
pub open spec fn may_mutate_spec_fn(
    state: OwnershipState,
    node: NodeId,
    epoch: Epoch
) -> bool {
    match state {
        OwnershipState::Owned { owner, epoch: e } =>
            owner == node && e == epoch,
        OwnershipState::Transferring { .. } =>
            false,
        OwnershipState::Unowned { .. } =>
            false,
    }
}
```

### Case 1: Owned State

**Hypothesis**:
- `state = Owned { owner, epoch: e }`
- `may_mutate(state, node_a, epoch_a)` = true
- `may_mutate(state, node_b, epoch_b)` = true

**By definition of `may_mutate` in Owned state**:
- From first hypothesis: `owner == node_a && e == epoch_a`
- From second hypothesis: `owner == node_b && e == epoch_b`

**By transitivity**:
- `node_a == owner == node_b` ⟹ `node_a == node_b`
- `epoch_a == e == epoch_b` ⟹ `epoch_a == epoch_b`

**Conclusion**: `node_a == node_b && epoch_a == epoch_b` ✓

### Case 2: Transferring State

**Hypothesis**:
- `state = Transferring { from, to, old_epoch, new_epoch }`
- `may_mutate(state, node_a, epoch_a)` = true
- `may_mutate(state, node_b, epoch_b)` = true

**By definition of `may_mutate` in Transferring state**:
- `may_mutate(state, node_a, epoch_a)` = false (always)
- `may_mutate(state, node_b, epoch_b)` = false (always)

**Contradiction**: We assumed both were true, but both are false.

**Conclusion**: This case is vacuously true (false antecedent) ✓

### Case 3: Unowned State

**Hypothesis**:
- `state = Unowned { epoch, intended_owner }`
- `may_mutate(state, node_a, epoch_a)` = true
- `may_mutate(state, node_b, epoch_b)` = true

**By definition of `may_mutate` in Unowned state**:
- `may_mutate(state, node_a, epoch_a)` = false (always)
- `may_mutate(state, node_b, epoch_b)` = false (always)

**Contradiction**: We assumed both were true, but both are false.

**Conclusion**: This case is vacuously true (false antecedent) ✓

## Summary

By exhaustive case analysis on the three ownership state variants:
1. **Owned**: Direct proof from definition (both nodes must be the owner at the same epoch)
2. **Transferring**: Vacuous (no node can mutate)
3. **Unowned**: Vacuous (no node can mutate)

Therefore, the exclusive mutable ownership claim holds for all reachable states.

## Verus Implementation

See `../verus/ownership.rs` for the formal Verus proof:

```rust
pub proof fn exclusive_mutable_ownership_t(
    state: OwnershipState,
    node_a: NodeId,
    epoch_a: Epoch,
    node_b: NodeId,
    epoch_b: Epoch,
)
    requires
        may_mutate_spec_fn(state, node_a, epoch_a),
        may_mutate_spec_fn(state, node_b, epoch_b),
    ensures
        node_a == node_b && epoch_a == epoch_b,
{
    match state {
        OwnershipState::Owned { owner, epoch: e } => {
            assert!(owner == node_a && e == epoch_a);
            assert!(owner == node_b && e == epoch_b);
            assert!(node_a == node_b);
            assert!(epoch_a == epoch_b);
        }
        OwnershipState::Transferring { .. } => {
            assert!(false);  // Contradiction: both assumed true but spec is false
        }
        OwnershipState::Unowned { .. } => {
            assert!(false);  // Contradiction: both assumed true but spec is false
        }
    }
}
```

## Implications

This proof guarantees:
1. **At most one node can mutate at any time** - A direct consequence
2. **Mutual exclusion** - No two distinct nodes can hold mutable authority simultaneously
3. **Safety** - The system maintains exclusive ownership semantics across all state transitions (in combination with transfer proofs)
