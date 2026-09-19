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
| The network may duplicate, reorder, delay and lose messages arbitrarily | `System::network` is a set that only grows, and delivery does not consume. A message is therefore deliverable zero, one or many times, in any order, at any later point. `Step::Replay` additionally makes duplication an explicit transition. The Raymond layer models its requests the same way, via `Raymond::requests`. |
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
| E | The runtime `u64` fence check returns exactly the model's verdict, and rejects any superseded epoch | `exec::FenceGuard::accepts`, `exec::FenceGuard::rejects_stale` | the guard is the node's own record of one actor, immutable after `FenceGuard::new` (private fields, no setter), so nothing in this API can change who owns what |
| P1 | **Issued tokens never disappear** — no crash, partition or recovery retracts a capability, which is why stale tokens must be fenced rather than revoked | `proofs::properties::theorem_issued_monotone` | none |
| P2 | **Sent messages never disappear** — the fact that makes duplication, reordering and unbounded delay free in the model | `proofs::properties::theorem_network_monotone` | none |
| P3 | **The actor population is constant** — no transition creates or destroys an actor | `proofs::properties::theorem_actor_domain_constant` | none |
| P4 | **An epoch advances by at most one per transition** — with claim 5, the epoch sequence is non-decreasing and never skips a generation | `proofs::properties::theorem_epoch_increases_by_at_most_one` | none |
| P5 | **Ownership at a given epoch is final** — once owned by `n` at `e`, every later state still at `e` is still owned by `n` at `e`; a handover *must* burn the epoch | `proofs::properties::theorem_ownership_at_an_epoch_is_final` | valid execution |
| P6 | **An epoch determines its owner** — any two points of an execution owned at the same epoch have the same owner | `proofs::properties::theorem_epoch_determines_owner` | valid execution |
| P7 | **Staleness is permanent** — a fenced-out node can never be fenced back in by waiting | `proofs::properties::theorem_stale_stays_stale` | valid execution |
| P8 | **No authority without a capability** — a node that may mutate provably holds an issued token for exactly that `(actor, epoch)` | `proofs::properties::theorem_no_authority_without_token` | reachability |
| P9 | **Epoch monotonicity survives composition** | `proofs::properties::theorem_composed_epoch_monotone` | none |
| R9 | **Exactly one token** — `ray_inv` gives at most one; with `ray_token_exists` (preserved by every step, so the token is never lost) there is exactly one | `proofs::raymond::theorem_ray_exactly_one_token`, `lemma_ray_token_exists_init`, `lemma_ray_token_exists_step` | Raymond invariant |
| R10 | **Raymond critical sections are exclusive** — at most one node is inside at a time | `proofs::raymond::theorem_ray_critical_section_is_exclusive` | Raymond invariant |
| I | The inductive invariant holds in every reachable state (`init ==> inv`, `inv /\ next ==> inv`) | `proofs::invariant::theorem_reachable_inv` | the model's transition relation |
| S | **The headline scenario**: `A` owns X@41, a transfer and a crash/recovery occur, `B` owns X@42, `A` returns still holding its epoch-41 token - and cannot perform an authoritative mutation | `proofs::adversarial::scenario_stale_owner_returns` | `A != B` |
| S1 | A stale `Grant` cannot resurrect a superseded epoch | `proofs::adversarial::theorem_stale_grant_cannot_be_used` | none |
| S2 | Message duplication / reordering / delay cannot change ownership | `proofs::adversarial::theorem_network_steps_cannot_change_ownership` | none |
| S3 | Crash and stale-node recovery cannot change ownership | `proofs::adversarial::theorem_crash_recovery_cannot_change_ownership` | none |
| S4 | An interrupted transfer leaves nobody with authority and burns the epoch | `proofs::adversarial::scenario_interrupted_transfer` | `inv` holds before the step |
| R1 | **Raymond: at most one valid token** | `proofs::raymond::theorem_ray_at_most_one_token`, preserved by `lemma_ray_step_preserves_inv` | Raymond invariant |
| R2 | **Raymond: holder/routing changes cannot manufacture ownership** | `proofs::raymond::theorem_routing_cannot_manufacture_ownership` | Raymond invariant, coupling |
| R3 | **Raymond: duplicate/reordered requests cannot create a second owner** | `proofs::raymond::theorem_duplicate_requests_are_safe` | Raymond invariant |
| R4 | **Raymond: token transfer preserves ownership safety** | `proofs::composed::lemma_composed_pass_token_preserves_inv` (and, as a layer-local lemma, `proofs::raymond::theorem_token_transfer_preserves_ownership_safety`) | none — in the composed machine the release-before-transfer condition is a *guard*, not an assumption |
| R5 | **Composed exclusivity**: in every reachable composed state at most one node may mutate the actor, and it is the node holding the token | `proofs::composed::theorem_composed_exclusivity` | composed reachability |
| C0 | **Non-degeneracy**: a composed state in which a node is *actually inside* the critical section is reachable from `composed_init` — driven through `RequestCs`, `EnterCs`, `ExitCs` — so the composed claims are not restricted to a `using`-free fragment | `proofs::composed_scenario::scenario_composed_critical_section` | `A != B` |
| C0a | (Step-level lemma backing C0) `EnterCs`/`ExitCs` are legal `ComposedStep::Ray` transitions and preserve the composed invariant | `proofs::composed::theorem_composed_admits_critical_section`, `..._exit` | composed invariant holds before the step |
| C1 | **Non-vacuity**: a complete handover driven through *both* layers is reachable — `A` owns X@41 while holding the token, releases it, the token moves `A → B`, and `B` ends up owning X@42 *and* holding the token, with `A`'s epoch-41 token still issued and powerless | `proofs::composed_scenario::scenario_composed_handover` | `A != B` |
| C | The coupling is an **invariant** of the composed machine: `composed_init ==> composed_inv`, `composed_inv /\ composed_next ==> composed_inv`, hence `composed_reachable ==> composed_inv` | `proofs::composed::theorem_composed_reachable_inv`, `theorem_composed_step_preserves_inv` | the composed transition relation |
| R6 | A concrete routing execution: request `D → B → A → C[token]`, token `C → A → B → D`, with the unique-token invariant carried through all eleven hops, then a twelfth step redelivering `D`'s original request after the token has finished moving | `proofs::raymond_routing::scenario_request_and_token_routing` | four distinct nodes |
| R7 | A request outlives the topology it was routed against: after the token moves it is still in `requests` and still deliverable | `proofs::raymond::theorem_delayed_request_survives_token_move` | none |
| R8 | Delivering an arbitrarily delayed request preserves the Raymond invariant and leaves token possession completely unchanged | `proofs::raymond::theorem_delayed_request_delivery_is_safe` | Raymond invariant |

"Reachability" means the hypothesis `reachable(sys)`, i.e. some finite execution
starting from an `init` state ends in `sys`. It is discharged once and for all by
`theorem_reachable_inv`.

## The Raymond layer

`src/raymond.rs` models Raymond's distributed mutual-exclusion algorithm as a
**routing** layer, kept strictly separate from ownership semantics. Per node it
tracks a `holder` pointer (the next hop towards the token), a request `queue`,
an `asked` flag (outstanding request) and `using` (token possession / critical
section).

Requests in flight are explicit state: `Raymond::requests` records every request
ever sent as `(originator, destination)`, never shrinks, and is not consumed by
delivery — the same modelling choice the ownership layer makes for `network`. The
destination is resolved at *send* time, which is what lets a request be delivered
after the token has moved and the holder pointers it was routed against are gone.
A guard phrased against the live `holder[from]` would instead drop such a request
silently, so "arbitrary delay" would have been claimed but not modelled.

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

On its own, though, `couples` is only a predicate: `ray_assign_privilege` never
sees the ownership state, so nothing in the routing layer stops a token from
moving out from under a node that still has authority. `src/composed.rs` closes
that gap by defining a single state machine over both layers in which the
synchronisation is a **guard**:

* `PassToken` may only fire while the actor is *not* `Owned` — ownership must be
  released before the token is allowed to move;
* `AcquireUnderToken` may only fire for a node that *holds* the token — authority
  cannot be taken by a node routing has not elected;
* `Ray` carries every Raymond step that does *not* move the token — request
  routing and critical-section entry/exit alike — and `Own` carries every
  ownership transition that does not create authority over the actor.

The `Ray` carrier is guarded on `preserves_token`, deliberately wider than
`is_routing_step`: if it admitted only routing, no composed execution could ever
enter a critical section, every composed-reachable state would keep `using`
uniformly false, and the theorems below would cover only a degenerate fragment
of the real behaviour. `scenario_composed_critical_section` rules that out the
only way that really counts — by building an execution from `composed_init` that
*reaches* a state with `using` set, rather than assuming the entry transition and
checking it type-checks as a composed step.

`couples` is then an invariant of that machine rather than a side condition,
which is what makes "token transfer preserves ownership safety" a claim about
the system instead of a hypothetical.

Every composed theorem is of the form "every *reachable* composed state
satisfies ...", and such statements are worthless if nothing interesting is
reachable. Two executions close that off, both built from `composed_init` via
`lemma_composed_reachable_step`:

* `scenario_composed_handover` — a complete handover driven through both layers
  at once, ending in a reachable state where `B` genuinely owns the actor at
  epoch 42 *and* holds the token, while `A`'s epoch-41 token is still issued and
  powerless;
* `scenario_composed_critical_section` — a reachable state in which a node is
  actually inside the critical section.

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
│   ├── composed.rs     both layers as one machine; coupling enforced by guards
│   ├── exec.rs         the only executable code: the u64 fence check
│   └── proofs/
│       ├── mod.rs
│       ├── invariant.rs    init ==> inv, inv /\ next ==> inv, reachable ==> inv
│       ├── properties.rs   structural, temporal and capability properties
│       ├── exclusivity.rs  claim 1
│       ├── fencing.rs      claims 2, 3, 5
│       ├── transfer.rs     claim 4
│       ├── tokens.rs       claim 6
│       ├── adversarial.rs  concrete adversarial executions
│       ├── raymond.rs      claim 7
│       ├── composed.rs     the coupling as a composed-machine invariant
│       ├── composed_scenario.rs  an end-to-end handover across both layers
│       └── raymond_routing.rs  the D → B → A → C routing execution
└── .github/workflows/verify.yml
```

This differs from a plain `proofs/` directory at the repository root: Verus
verifies a *crate*, so every proof file has to be a module of that crate. Keeping
them under `src/proofs/` is the ordinary Rust way to express that; a top-level
`proofs/` would need `#[path = "../proofs/..."]` attributes for no benefit.

Executable code is confined to `src/exec.rs`, which holds the `u64`-valued
fence check a node actually runs, proved to return exactly the model's verdict.
It offers **queries only**: a `FenceGuard` has private fields, a single
constructor and no setter, so its ghost view is fixed at construction. Were it
mutable — by a `bump` method or by assigning to a public field — its view could
drift from `Owned(A, e)` to `Owned(B, e + 1)`, exactly the atomic ownership
assignment this model refuses to admit. Observing a new generation means
constructing a new guard. Making a
guard follow the protocol needs the refinement relation listed under future work.
Everything else in the crate is specification or proof.

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

## Status: proven, modelled, future work

Against the pinned Verus release, `verus --crate-type=lib src/lib.rs` reports
`88 verified, 0 errors`. CI writes the current count into each run's job summary,
which is the authoritative figure if this snapshot has drifted.

**Machine-checked** (every `proof fn` in `src/proofs/` is checked by Verus in
CI, with no `assume`/`admit`/`external_body`/`axiom`):

* exclusive mutable ownership, in every reachable state;
* unique authoritative epoch (existence and uniqueness);
* stale-owner fencing, including the headline `A@41 / B@42 / A returns` scenario
  as a concrete eleven-state reachable execution;
* epoch monotonicity, per step, per `next`, and along whole executions;
* transfer safety - the inductive invariant is preserved by every transition,
  and no stage of a handover admits two owners;
* token uniqueness, both "at most one token confers authority per
  `(ActorId, Epoch)`" and the stronger "at most one token is ever issued per
  `(ActorId, Epoch)`";
* stale tokens surviving crash, partition and recovery confer no authority;
* Raymond: at most one token, routing cannot manufacture ownership, duplicate,
  reordered and arbitrarily delayed requests are safe, and token transfer
  preserves the coupling to the ownership layer;
* the coupling itself, as an invariant of the composed machine: in every
  reachable composed state the only node that may mutate the actor is the node
  holding the token.

**Modelled but not proven** (present in the state machine, no theorem beyond
invariant preservation):

* the specific message shapes (`Revoke` / `Released` / `Grant`) - safety does
  not depend on them, which is itself the point, but no separate theorem says
  the message flow is the *only* way to make progress;
* Raymond's holder pointers are proven to have a unique root, but the model does
  not prove the pointers always form an acyclic tree. Safety here does not need
  it; routing termination would.

**Future work** (deliberately out of scope):

* **liveness** of either layer - progress, fairness, termination of a handover,
  and Raymond's "every request is eventually served". These need assumptions
  (reliable FIFO links, eventual failure detection) that this model does not
  make.
* a refinement from the `nat`-valued model to an executable `u64` implementation,
  with the epoch-exhaustion case handled. Until that exists, `src/exec.rs`
  deliberately offers no way to *advance* a node's fence guard - only to consult
  it - so that no executable API can perform a handover the model does not;
* the actual actor runtime: networking, persistence, and the code that obeys the
  protocol. Verifying the protocol says nothing about whether an implementation
  follows it.

## No escape hatches

The proofs use no `assume`, `admit`, `external_body`, `axiom`, or any other way
of asserting something Verus did not check. Everything the proofs rely on that
is not derived is a modelled transition or an explicitly documented entry in the
failure-model table above.
