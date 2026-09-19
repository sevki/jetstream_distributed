# Proof Index

This directory contains proof sketches and formal verification documentation for the distributed ownership protocol.

## Structure

- **exclusive_mutable_ownership.md** - Core claim: at most one node can mutate
- **mutual_exclusion.md** - Two distinct nodes cannot both have authority
- **state_safety.md** - Each ownership state variant maintains invariants
- **global_invariant.md** - All reachable states maintain exclusivity

## Main Claim

**Exclusive Mutable Ownership**: For every actor and reachable system state, if nodes A and B are both permitted to mutate the actor, then A == B.

## Formalization Approach

We use Verus (a verifier for Rust) to provide machine-checked proofs. See `../verus/` for the complete formalization.

### Specification (Verus)

```rust
pub open spec fn may_mutate_spec_fn(
    state: OwnershipState,
    node: NodeId,
    epoch: Epoch
) -> bool {
    match state {
        OwnershipState::Owned { owner, epoch: e } =>
            owner == node && e == epoch,
        OwnershipState::Transferring { .. } => false,
        OwnershipState::Unowned { .. } => false,
    }
}
```

### Implementation (Rust)

```rust
pub fn may_mutate(
    state: &OwnershipState,
    node: NodeId,
    epoch: Epoch
) -> bool {
    match state {
        OwnershipState::Owned { owner, epoch: e } =>
            *owner == node && *e == epoch,
        OwnershipState::Transferring { .. } => false,
        OwnershipState::Unowned { .. } => false,
    }
}
```

## Proof Outline

```
may_mutate_invariant_holds_t
├─ exclusive_mutable_ownership_t (core theorem)
│  ├─ Case: Owned state
│  │  └─ owner == node_a && e == epoch_a
│  │     owner == node_b && e == epoch_b
│  │     ∴ node_a == node_b && epoch_a == epoch_b
│  ├─ Case: Transferring state
│  │  └─ False (no mutation allowed)
│  └─ Case: Unowned state
│     └─ False (no mutation allowed)
├─ owned_state_safe_t
│  └─ Specialization for Owned variant
├─ transferring_state_safe_t
│  └─ Vacuously true (no mutations possible)
└─ unowned_state_safe_t
   └─ Vacuously true (no mutations possible)
```

## Verification Status

| Claim | Status | Location |
|-------|--------|----------|
| Exclusive mutable ownership | ✅ Verified | `../verus/ownership.rs:exclusive_mutable_ownership_t` |
| Mutual exclusion | ✅ Verified | `../verus/ownership.rs:mutual_exclusion_t` |
| Owned state safety | ✅ Verified | `../verus/ownership.rs:owned_state_safe_t` |
| Transferring state safety | ✅ Verified | `../verus/ownership.rs:transferring_state_safe_t` |
| Unowned state safety | ✅ Verified | `../verus/ownership.rs:unowned_state_safe_t` |
| Global invariant | ✅ Verified | `../verus/ownership.rs:may_mutate_invariant_holds_t` |
