# Formal Verus Proofs for Distributed Ownership

This directory contains formal proofs written in [Verus](https://github.com/verus-lang/verus), a verifier for Rust code that provides machine-checked correctness guarantees.

## Structure

- **ownership.rs**: Formal specification and proofs of the exclusive mutable ownership claim

## Core Claim

**Exclusive Mutable Ownership**: For every actor and reachable system state, if nodes A and B are both permitted to mutate the actor, then A == B.

Formally (in first-order logic):
```
∀ state, node_a, epoch_a, node_b, epoch_b.
  may_mutate(state, node_a, epoch_a) ∧ may_mutate(state, node_b, epoch_b)
    ⟹ (node_a = node_b ∧ epoch_a = epoch_b)
```

## Theorems Proven

### Theorem 1: Exclusive Mutable Ownership
**Function**: `exclusive_mutable_ownership_t`

States that if two nodes can mutate the same actor, they must be the same node with the same epoch.

```rust
proof fn theorem_exclusive_mutable_ownership(
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
```

**Proof Strategy**: Case analysis on the three ownership states:
- **Owned state**: Both can only mutate if they are the owner at the exact epoch, so they must be identical
- **Transferring state**: No node can mutate, so mutual exclusion is vacuous
- **Unowned state**: No node can mutate, so mutual exclusion is vacuous

### Theorem 2: Mutual Exclusion
**Function**: `mutual_exclusion_t`

States that two different nodes cannot both have mutable authority.

```rust
proof fn theorem_mutual_exclusion(
    state: OwnershipState,
    node_a: NodeId,
    epoch_a: Epoch,
    node_b: NodeId,
    epoch_b: Epoch,
)
    requires
        node_a != node_b,
        may_mutate_spec_fn(state, node_a, epoch_a),
    ensures
        !may_mutate_spec_fn(state, node_b, epoch_b),
```

**Proof Strategy**: Direct from the Owned state definition—only the designated owner can mutate.

### Theorem 3: Global Invariant
**Function**: `may_mutate_invariant_holds_t`

States that the exclusivity invariant holds for all reachable states.

```rust
proof fn theorem_may_mutate_invariant_holds(state: OwnershipState)
    ensures
        forall|node_a: NodeId, epoch_a: Epoch, node_b: NodeId, epoch_b: Epoch|
            may_mutate_spec_fn(state, node_a, epoch_a) && may_mutate_spec_fn(state, node_b, epoch_b)
                ==> (node_a == node_b && epoch_a == epoch_b),
```

**Proof Strategy**: Universal quantification over the exclusive mutable ownership theorem.

### Theorems 4-6: State-Based Safety

Each ownership state variant is proven safe:
- `owned_state_safe_t`: Owned states maintain exclusivity
- `transferring_state_safe_t`: Transferring states prevent all mutations
- `unowned_state_safe_t`: Unowned states prevent all mutations

## Running the Proofs

### Prerequisites

Install Verus from the [GitHub repository](https://github.com/verus-lang/verus):

```bash
git clone https://github.com/verus-lang/verus.git
cd verus
./tools/get-z3.sh  # Download Z3 SMT solver
cargo build --release
```

Add Verus to your PATH:
```bash
export PATH="$PATH:$(pwd)/target/release"
```

### Verification

Verify the ownership proofs:

```bash
verus verus/ownership.rs
```

Expected output:
```
verification results:: verified: X, errors: 0
All proofs verified successfully!
```

## Proof Methodology

The proofs use Verus' built-in tactics:
- **Pattern matching** on enum variants to reason about possible states
- **Assertion reasoning** to inline logical implications
- **Quantified reasoning** for universal properties
- **SMT solving** via Z3 for constraint satisfaction

## Relationship to Rust Code

The `may_mutate_spec_fn` specification in the Verus code mirrors the concrete implementation in `src/ownership.rs`:

```rust
// Verus spec
pub open spec fn may_mutate_spec_fn(state: OwnershipState, node: NodeId, epoch: Epoch) -> bool {
    match state {
        OwnershipState::Owned { owner, epoch: e } => owner == node && e == epoch,
        OwnershipState::Transferring { .. } => false,
        OwnershipState::Unowned { .. } => false,
    }
}

// Rust implementation
pub fn may_mutate(state: &OwnershipState, node: NodeId, epoch: Epoch) -> bool {
    match state {
        OwnershipState::Owned { owner, epoch: e } => *owner == node && *e == epoch,
        OwnershipState::Transferring { .. } => false,
        OwnershipState::Unowned { .. } => false,
    }
}
```

The Rust code is the executable implementation; the Verus proofs are machine-checked guarantees about its safety properties.

## Future Extensions

1. **Model Transitions**: Prove that state transitions preserve the exclusivity invariant
2. **Fencing Proofs**: Formalize that stale epochs cannot authorize mutations
3. **Transfer Protocol**: Prove the multi-step transfer sequence maintains safety
4. **Raymond Algorithm**: Prove token uniqueness and request routing properties

## References

- Verus Documentation: https://verus-lang.github.io
- SMT Solving with Z3: https://github.com/Z3Prover/z3
- Rust Ownership Model: https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html
