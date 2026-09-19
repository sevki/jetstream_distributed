# distributed-ownership

A small, machine-checked model of **exclusive mutable ownership across
machines**, written in [Verus](https://github.com/verus-lang/verus).

```text
Rust:
    at most one mutable reference

Distributed ownership:
    at most one authoritative mutable owner
```

## What this is, and what it is not

This repository does **not** claim that Rust's borrow checker has been extended
across machines. Nothing here is checked at compile time for your application
code, no lifetime crosses a network link, and no `&mut` is transported anywhere.

What this is: a **runtime protocol** for moving exclusive write authority over
an `ActorId` between nodes, together with **machine-checked proofs** that the
protocol's exclusivity and fencing properties hold in every reachable state,
including under crashes, partitions, duplicated messages and interrupted
handovers.

The analogy to Rust is about the *shape* of the guarantee, not the mechanism.
Rust's `&mut T` is exclusive because the compiler refuses to create a second
one. Here, authority is exclusive because `may_mutate` is only ever true in one
shape - the actor is `Owned`, the caller is the owner, and the caller's fencing
epoch is exactly the actor's current epoch - and because the protocol's
transitions provably keep it that way.

This is a *model*. There is no networking, no persistence and no actor runtime
here, and that is deliberate.

## The state machine

```rust
pub type ActorId = nat;
pub type NodeId  = nat;
pub type Epoch   = nat;

pub enum OwnershipState {
    Owned        { owner: NodeId, epoch: Epoch },
    Transferring { from: NodeId, to: NodeId, old_epoch: Epoch, new_epoch: Epoch },
    Unowned      { epoch: Epoch, intended_owner: NodeId },
}
```

Ownership never moves atomically. A handover is four protocol transitions:

```text
Owned(A, 41)
      |  BeginTransfer(A -> B)         epoch 42 is allocated here
Transferring(A, B, 41, 42)
      |  CompleteRelease
Unowned(42, B)
      |  Acquire(B)
Owned(B, 42)
```

Two deliberate design points:

* **The epoch advances at the *start* of a handover, not at the end.** From the
  moment `A` agrees to transfer, `current_epoch` is 42, so `A`'s epoch-41
  authority is already fenced out. `A` does not have to be reachable, or even
  alive, for this to take effect.
* **During the two middle stages nobody has authority at all.** That is the
  trade this design makes: it gives up availability during a handover so that
  double ownership is not representable. It is acceptable for neither node to
  have mutable authority during a transfer; it is never acceptable for both to.

### The two specification functions

```rust
// Who may perform an authoritative mutation.
spec fn may_mutate(s: OwnershipState, node: NodeId, epoch: Epoch) -> bool {
    match s {
        Owned { owner, epoch: e } => node == owner && epoch == e,
        Transferring { .. }       => false,
        Unowned { .. }            => false,
    }
}

// The fence check a server performs on an incoming request.
spec fn valid_fence(s: OwnershipState, e: Epoch) -> bool { e >= current_epoch(s) }
```

`current_epoch` reports `new_epoch` while `Transferring`, which is what makes
the outgoing owner stale immediately.

### Capability tokens

A `Token { actor, epoch, holder }` is a *physical* artifact. It can be copied,
it survives a crash, and a node that was partitioned away for an hour can come
back still clutching one. The model reflects that: `System::issued` is the set
of every token ever issued and it **never shrinks**.

Whether a token confers *authority* is a completely separate question, answered
by `token_authorized`, which consults the actor's current state. Stale physical
tokens exist; they are inert.

## Failure model

These are the assumptions the proofs rest on. They are part of the system model,
not hidden side conditions.

| Assumption | How it is modelled |
| --- | --- |
| The network may duplicate, reorder, delay and lose messages arbitrarily | `System::network` is a set that only grows, and delivery does not consume. A message is therefore deliverable zero, one or many times, in any order, at any later point. `Step::Replay` additionally makes duplication an explicit transition. |
| Nodes may crash at any time | `Step::Crash` removes a node from `live`. It does **not** remove that node's tokens from `issued`. |
| Crashed nodes may come back with stale beliefs | `Step::Recover` puts the node back in `live`. It regains nothing else - in particular it still holds only its old, superseded tokens. |
| Failure detection is unreliable | `Step::RevokeOwner` may fire against a node that is perfectly healthy. Safety must come from the epoch bump, not from the detector being right. |
| A handover may be interrupted at any point | `Step::AbortTransfer` fires from `Transferring` and burns *another* epoch, so a `Grant` for the abandoned epoch is already stale when it arrives. `Step::ReassignUnowned` covers an intended owner that never picks the actor up. |
| Epoch allocation is done by the protocol, not by a clock | Every epoch-advancing transition sets the new epoch to `old + 1` of the state it reads, so epochs are per-actor and totally ordered by construction. |
| Nodes are not Byzantine | There is no transition that mints a token, fabricates an `Owned` state, or forges a state transition. A node can replay any message it has seen and present any token it was ever given; it cannot invent one. |
| Epochs do not overflow | `Epoch = nat`, so the model has unbounded epochs. A `u64` implementation must treat exhaustion as a hard failure. |

What is **not** claimed: **liveness**. Nothing here says a transfer completes,
that a request is eventually served, or that an actor ever becomes owned again.
Under arbitrary crashes and partitions none of those are achievable anyway.
Safety survives every case above; progress does not, and is treated separately.

## Claimed invariants and the proofs that establish them

Every row names a `proof fn` that Verus checks in CI. If a row's proof stops
verifying, the build fails.

| # | Invariant | Verus theorem | Assumptions |
| --- | --- | --- | --- |
| 1 | **Exclusive mutable ownership** - in any reachable state, if `A` and `B` may both mutate an actor then `A == B` (and their epochs are equal) | `proofs::exclusivity::theorem_exclusive_mutable_ownership` | reachability; none beyond the model |
| 1a | The same, structurally: no state at all, reachable or not, admits two mutable owners | `proofs::exclusivity::theorem_exclusive_mutable_ownership_structural` | none |
| 1b | Two capability tokens that both confer authority over the same actor are the same token | `proofs::exclusivity::theorem_authorized_token_unique` | reachability |
| 2 | **Unique current epoch** - an actor has exactly one authoritative fencing epoch, and it exists | `proofs::fencing::theorem_unique_current_epoch` | none |
| 3 | **Stale-owner fencing** - `current_epoch(actor) > supplied_epoch ==> !can_mutate(actor, node, supplied_epoch)` | `proofs::fencing::theorem_stale_epoch_cannot_mutate` | none |
| 3a | Advancing `n -> n+1` strips authority from every holder of `n` | `proofs::fencing::theorem_epoch_advance_fences_previous` | none |
| 3b | For issued tokens the fence check is exactly epoch equality (no token is ever ahead of the actor) | `proofs::fencing::theorem_fence_is_exact_for_issued_tokens` | reachability |
| 4 | **Transfer safety** - every permitted transition preserves the ownership and fencing invariants | `proofs::transfer::theorem_transition_preserves_invariants` | `inv` holds before the step |
| 4a | Across a whole handover, the epoch never decreases, nobody has authority at the middle stages, and the outgoing owner is fenced from the first transition onwards | `proofs::transfer::theorem_handover_safety` | `A != B` |
| 4b | At no stage of a handover can both nodes have authority | `proofs::transfer::theorem_handover_never_both` | `A != B` |
| 4c | An interrupted handover fences both the old and the abandoned new epoch | `proofs::transfer::theorem_interrupted_transfer_fences_both` | none |
| 4d | Ownership cannot be manufactured: the only step that can make `may_mutate` true is `Acquire`, from `Unowned` at that exact epoch with a matching grant | `proofs::transfer::theorem_ownership_only_via_acquire` | none |
| 5 | **Epoch monotonicity** - no transition decreases an actor's epoch | `proofs::fencing::theorem_epoch_monotone_step`, `..._next`, `..._execution` | none |
| 6 | **Token uniqueness (authority)** - at most one token confers authority per `(ActorId, Epoch)` | `proofs::tokens::theorem_valid_token_unique_per_actor_epoch` | none |
| 6a | **Token uniqueness (physical)** - at most one token is ever *issued* per `(ActorId, Epoch)` | `proofs::tokens::theorem_issued_token_unique_per_actor_epoch` | reachability |
| 6b | Stale physical tokens confer no authority | `proofs::tokens::theorem_stale_token_has_no_authority` | none |
| 6c | No token is ever minted for a future epoch | `proofs::tokens::theorem_no_future_tokens` | reachability |
| I | The inductive invariant holds in every reachable state (`init ==> inv`, `inv /\ next ==> inv`) | `proofs::invariant::theorem_reachable_inv` | the model's transition relation |
| S | **The headline scenario**: `A` owns X@41, a transfer and a crash/recovery occur, `B` owns X@42, `A` returns still holding its epoch-41 token - and cannot perform an authoritative mutation | `proofs::adversarial::scenario_stale_owner_returns` | `A != B` |
| S1 | A stale `Grant` cannot resurrect a superseded epoch | `proofs::adversarial::theorem_stale_grant_cannot_be_used` | none |
| S2 | Message duplication / reordering / delay cannot change ownership | `proofs::adversarial::theorem_network_steps_cannot_change_ownership` | none |
| S3 | Crash and stale-node recovery cannot change ownership | `proofs::adversarial::theorem_crash_recovery_cannot_change_ownership` | none |
| S4 | An interrupted transfer leaves nobody with authority and burns the epoch | `proofs::adversarial::scenario_interrupted_transfer` | `inv` holds before the step |
| R1 | **Raymond: at most one valid token** | `proofs::raymond::theorem_ray_at_most_one_token`, preserved by `lemma_ray_step_preserves_inv` | Raymond invariant |
| R2 | **Raymond: holder/routing changes cannot manufacture ownership** | `proofs::raymond::theorem_routing_cannot_manufacture_ownership` | Raymond invariant, coupling |
| R3 | **Raymond: duplicate/reordered requests cannot create a second owner** | `proofs::raymond::theorem_duplicate_requests_are_safe` | Raymond invariant |
| R4 | **Raymond: token transfer preserves ownership safety** | `proofs::raymond::theorem_token_transfer_preserves_ownership_safety` | the actor is not `Owned` when the token moves |
| R5 | Composed exclusivity: under the coupling, the only node that can mutate is the token holder | `proofs::raymond::theorem_coupled_exclusivity` | Raymond invariant, coupling |

"Reachability" means the hypothesis `reachable(sys)`, i.e. some finite execution
starting from an `init` state ends in `sys`. It is discharged once and for all by
`theorem_reachable_inv`.

## The Raymond layer

`src/raymond.rs` models Raymond's distributed mutual-exclusion algorithm as a
**routing** layer, kept strictly separate from ownership semantics. Per node it
tracks a `holder` pointer (the next hop towards the token), a request `queue`,
an `asked` flag (outstanding request) and `using` (token possession / critical
section).

Requests travel hop-by-hop towards the token and the token travels back along
the reverse of the request path:

```text
request:  D -> B -> A -> C[token]
token:    C -> A -> B -> D
```

Routing and ownership are glued by one predicate:

```rust
spec fn couples(r: Raymond, s: OwnershipState) -> bool {
    forall|n: NodeId, e: Epoch| may_mutate(s, n, e) ==> has_token(r, n)
}
```

Note the direction: routing never *grants* authority, it only constrains who
could possibly have it. Authority still comes exclusively from the ownership
state and its epoch. That is why a routing step - including a duplicated or
reordered request - cannot manufacture an owner: it does not touch `holder` at
all, so it cannot even change *who could* be the owner.

Raymond's **liveness** (every request is eventually served) needs FIFO,
reliable links and no crashes. None of those are assumed here and none of it is
claimed.

## Repository layout

```text
distributed-ownership/
├── Cargo.toml
├── rust-toolchain.toml
├── README.md
├── src/
│   ├── lib.rs
│   ├── model.rs        state space + transition relation (no specification)
│   ├── ownership.rs    may_mutate, tokens, the system invariant
│   ├── fencing.rs      current_epoch, valid_fence, staleness
│   ├── transfer.rs     the multi-step handover and its lemmas
│   ├── raymond.rs      Raymond routing layer + the coupling predicate
│   └── proofs/
│       ├── mod.rs
│       ├── invariant.rs    init ==> inv, inv /\ next ==> inv, reachable ==> inv
│       ├── exclusivity.rs  claim 1
│       ├── fencing.rs      claims 2, 3, 5
│       ├── transfer.rs     claim 4
│       ├── tokens.rs       claim 6
│       ├── adversarial.rs  concrete adversarial executions
│       └── raymond.rs      claim 7
└── .github/workflows/verify.yml
```

This differs from a plain `proofs/` directory at the repository root: Verus
verifies a *crate*, so every proof file has to be a module of that crate. Keeping
them under `src/proofs/` is the ordinary Rust way to express that; a top-level
`proofs/` would need `#[path = "../proofs/..."]` attributes for no benefit.

Specification and proof code are kept apart from the model: `src/model.rs`
defines only the state space and the transition relation and does not import the
specification layer, so a specification cannot be quietly weakened to fit the
model.

## Verifying locally

```bash
# 1. Install the Rust toolchain that the pinned Verus release was built against
rustup toolchain install 1.98.1-x86_64-unknown-linux-gnu \
  --component rustc-dev,llvm-tools,rust-std,cargo,rustfmt

# 2. Download the pinned Verus release
VERUS=0.2026.09.13.671956e
curl -fL -o verus.zip \
  "https://github.com/verus-lang/verus/releases/download/release%2F${VERUS}/verus-${VERUS}-x86-linux.zip"
unzip -q verus.zip && export PATH="$PWD/verus-x86-linux:$PATH"

# 3. Verify
verus --crate-type=lib src/lib.rs
```

CI (`.github/workflows/verify.yml`) runs exactly this on every push and pull
request, so a PR fails if any proof stops verifying.

## No escape hatches

The proofs use no `assume`, `admit`, `external_body`, `axiom`, or any other way
of asserting something Verus did not check. Everything the proofs rely on that
is not derived is a modelled transition or an explicitly documented entry in the
failure-model table above.
