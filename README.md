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
| **Ownership records are updated atomically (linearizably)** | Every epoch-advancing transition reads `pre.actors[a]` and writes `post.actors.insert(a, ..)` in one step, so an actor's record is a single value with no interleaving. This is the **strongest assumption in the model** and it is load-bearing: it rules out, by construction, two coordinators deciding concurrently — both reading `Owned { owner, epoch }` and both allocating `epoch + 1` for different successors. A real deployment must buy that atomicity from consensus or from a store with compare-and-swap, which is what makes "read `Owned { A, 41 }`, write `Unowned { 42, B }`" one step. `System::actors` is that registry, **not** per-node state. |
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
| 2 | **Unique current epoch** - existence stated outright, and uniqueness as an implication over *arbitrary* epochs (not under the assumption that a witness was already supplied) | `proofs::fencing::theorem_unique_current_epoch` | none |
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
| E | The runtime `u64` check returns exactly the model's verdict **for the generation the guard records**, and rejects any epoch superseded *within that record* | `exec::FenceGuard::accepts`, `exec::FenceGuard::rejects_stale` | the guard is the node's own belief, immutable after `FenceGuard::new`. **This is node-local staleness rejection, not fencing**: a partitioned `A` still holding `FenceGuard::new(A, 41)` accepts `(A, 41)` while the system is at `Owned { B, 42 }`. A node cannot fence itself — see below |
| P1 | **Issued tokens never disappear** — no crash, partition or recovery retracts a capability, which is why stale tokens must be fenced rather than revoked | `proofs::properties::theorem_issued_monotone` | none |
| P2 | **Sent messages never disappear** — the fact that makes duplication, reordering and unbounded delay free in the model | `proofs::properties::theorem_network_monotone` | none |
| P3 | **The actor population is constant** — no transition creates or destroys an actor | `proofs::properties::theorem_actor_domain_constant` | none |
| P4 | **An epoch advances by at most one per transition** — with claim 5, the epoch sequence is non-decreasing and never skips a generation | `proofs::properties::theorem_epoch_increases_by_at_most_one` | none |
| P5 | **Ownership at a given epoch is final** — once owned by `n` at `e`, every later state still at `e` is still owned by `n` at `e`; a handover *must* burn the epoch | `proofs::properties::theorem_ownership_at_an_epoch_is_final` | valid execution |
| P6 | **An epoch determines its owner** — any two points of an execution owned at the same epoch have the same owner | `proofs::properties::theorem_epoch_determines_owner` | valid execution |
| P7 | **Staleness is permanent** — a fenced-out node can never be fenced back in by waiting | `proofs::properties::theorem_stale_stays_stale` | valid execution |
| P8 | **No authority without a capability** — a node that may mutate provably holds an issued token for exactly that `(actor, epoch)` | `proofs::properties::theorem_no_authority_without_token` | reachability |
| P9 | **Epoch monotonicity survives composition** | `proofs::properties::theorem_composed_epoch_monotone` | none |
| R9 | **The token is never lost** — every Raymond transition preserves token existence, which is why it can live in `ray_inv` | `proofs::raymond::lemma_ray_token_exists_init`, `lemma_ray_token_exists_step` | Raymond invariant |
| R10 | **Raymond critical sections are exclusive** — at most one node is inside at a time | `proofs::raymond::theorem_ray_critical_section_is_exclusive` | Raymond invariant |
| I | The inductive invariant holds in every reachable state (`init ==> inv`, `inv /\ next ==> inv`) | `proofs::invariant::theorem_reachable_inv` | the model's transition relation |
| S | **The headline scenario**: `A` owns X@41, a transfer and a crash/recovery occur, `B` owns X@42, `A` returns still holding its epoch-41 token - and cannot perform an authoritative mutation. The postcondition exports the `Crash(A)` and `Recover(A)` steps themselves, with the epoch-41 token retained across both, so the theorem cannot be satisfied by an ordinary live handover | `proofs::adversarial::scenario_stale_owner_returns` | `A != B` |
| S1 | A stale `Grant` cannot resurrect a superseded epoch | `proofs::adversarial::theorem_stale_grant_cannot_be_used` | none |
| S2 | Message duplication / reordering / delay cannot change ownership | `proofs::adversarial::theorem_network_steps_cannot_change_ownership` | none |
| S3 | Crash and stale-node recovery cannot change ownership | `proofs::adversarial::theorem_crash_recovery_cannot_change_ownership` | none |
| S4 | An interrupted transfer leaves nobody with authority and burns the epoch. A step property, not a constructed execution — hence `theorem_`, not `scenario_` | `proofs::adversarial::theorem_interrupted_transfer_burns_the_epoch` | `inv` holds before the step (and so, by `theorem_reachable_inv`, every reachable state) |
| S4a | **An interrupted transfer really happens**: `init → IssueGrant → Acquire(A@41) → BeginTransfer(A→B) → AbortTransfer`, with the abort exported as a named step between reachable states ending at `Unowned(43, A)` and nobody able to mutate at 41 or 42. Without it, S4 stays provable even if `AbortTransfer` were changed to be always false — a conditional lemma about an unreachable transition | `proofs::adversarial::scenario_interrupted_transfer` | `A != B` |
| S5 | **A fabricated `Released` is inert.** `HandleRevoke` lets any live node manufacture a `Released` from any `Revoke` ever sent, however old. `CompleteRelease` is the only step that consumes one, and it re-reads the actor's current state, so if it fires the actor is `Transferring` right now and the network holds the `Released` naming exactly that handover's `from` and `new_epoch` | `proofs::adversarial::theorem_complete_release_needs_the_matching_released` | none |
| S6 | **A fabricated `Released` cannot steer a handover.** The resulting epoch is read from the live `Transferring` record, not from the message | `proofs::adversarial::theorem_complete_release_outcome_is_fixed_by_state` | none |
| R1 | **Raymond: exactly one valid token** - `ray_inv` carries token *existence* as well as uniqueness, so a root is guaranteed rather than merely not-duplicated | `proofs::raymond::theorem_ray_exactly_one_token`, `theorem_ray_at_most_one_token`, preserved by `lemma_ray_step_preserves_inv` | Raymond invariant |
| R2 | **Raymond: holder/routing changes cannot manufacture ownership** | `proofs::raymond::theorem_routing_cannot_manufacture_ownership` | Raymond invariant, coupling |
| R3 | **Raymond: duplicate/reordered requests cannot create a second owner** | `proofs::raymond::theorem_duplicate_requests_are_safe` | Raymond invariant |
| R4 | **Raymond: token transfer preserves ownership safety** | `proofs::composed::lemma_composed_pass_token_preserves_inv` (and, as a layer-local lemma, `proofs::raymond::theorem_token_transfer_preserves_ownership_safety`) | none — in the composed machine the release-before-transfer condition is a *guard*, not an assumption |
| R5 | **Composed exclusivity**: in every reachable composed state at most one node may mutate the actor, and it is the node holding the token | `proofs::composed::theorem_composed_exclusivity` | composed reachability |
| C0 | **Non-degeneracy**: a composed state in which a node is *actually inside* the critical section is reachable from `composed_init` — driven through `RequestCs`, `EnterCs`, `ExitCs` — so the composed claims are not restricted to a `using`-free fragment | `proofs::composed_scenario::scenario_composed_critical_section` | `A != B` |
| C0a | (Step-level lemma backing C0) `EnterCs`/`ExitCs` are legal `ComposedStep::Ray` transitions and preserve the composed invariant | `proofs::composed::theorem_composed_admits_critical_section`, `..._exit` | composed invariant holds before the step |
| C1 | **Non-vacuity**: a complete *voluntary* handover driven through **both** layers is reachable. The contract exports the `CompleteRelease` step out of a `Transferring` state, linked by `composed_reachable_from` to the outcome, *and* the `PassToken` step with `A` still live. Both are needed: the endpoint alone is also reached by crash takeover (`SeizeToken`) and by revoking a live `A` (no release at all) | `proofs::composed_scenario::scenario_composed_handover` | `A != B` |
| C2 | **Crash-driven takeover is reachable in the composed machine**: `A` owns X@41 holding the token, crashes and takes no further step; the coordinator burns the epoch; the token is *seized*; `B` ends up owning X@42 and holding the token, with `A`'s epoch-41 token still issued and powerless. The postcondition exports the `SeizeToken` step itself, from a state where `A` is already non-live, so the theorem cannot be satisfied by a voluntary handover followed by a crash | `proofs::composed_scenario::scenario_composed_crash_takeover` | `A != B` |
| C3 | Seizing the token preserves the coupling and leaves the target holding the one token — safety comes from the epoch being burned first, not from the holder agreeing to let go | `proofs::composed::lemma_composed_seize_preserves_inv`, `proofs::raymond::lemma_seize_preserves_inv` | composed invariant; **the seized node has fail-stopped** (`!live`) — see below |
| C4 | **Token movement is partitioned by the holder's liveness**: a live holder passes it on, a fail-stopped one is seized from, and no other composed step moves the token at all | `proofs::composed::theorem_token_movement_is_partitioned` | composed invariant |
| C5 | The two layers describe the **same cluster**: `ray.nodes == own.nodes` is part of `composed_inv` and `composed_init`. Without it a Raymond root could be a node the ownership layer never heard of, so `!own.live.contains(n)` would hold for it with no `Crash` having happened, and the seizure guard would be satisfied by unmodelled liveness rather than by a fail-stop | `composed::composed_inv`, preserved by `proofs::composed::theorem_composed_step_preserves_inv` | — |
| P10 | **The node population is constant** — `Crash` and `Recover` move nodes in and out of `live`, never out of `nodes` | `proofs::properties::theorem_node_domain_constant` | none |
| C6 | **A seized node cannot rejoin `live` while still seized** — `cs_own` refuses `Recover` for it, so the only way back is through `Reconcile`, which makes the reconciliation a real deployment must perform a step an execution has to contain rather than an assumption | `proofs::composed::theorem_seized_node_cannot_recover` | — |
| C7 | Reconciliation is **not a dead end**: `A` can be told what happened and then rejoin, holding no token and no authority | `proofs::composed_scenario::scenario_composed_crash_takeover` (third witness) | `A != B` |
| C | The coupling is an **invariant** of the composed machine: `composed_init ==> composed_inv`, `composed_inv /\ composed_next ==> composed_inv`, hence `composed_reachable ==> composed_inv` | `proofs::composed::theorem_composed_reachable_inv`, `theorem_composed_step_preserves_inv` | the composed transition relation |
| R6 | A concrete routing execution: request `D → B → A → C[token]`, token `C → A → B → D`, then a twelfth step redelivering `D`'s original request after the token has finished moving. The contract pins `r0 == routing_init_state(a, b, c, d)` and exports the final redelivery step with `ray_reachable_from(r0, p)` — `ray_init` alone constrains only the root and the empty queues, not the holder tree, so without the pin a `D → B → C` tree satisfies the scenario with `A` never participating | `proofs::raymond_routing::scenario_request_and_token_routing` | four distinct nodes |
| R7 | A request outlives the topology it was routed against: after the token moves it is still in `requests` and still deliverable | `proofs::raymond::theorem_delayed_request_survives_token_move` | none |
| R8 | Delivering an arbitrarily delayed request preserves the Raymond invariant and leaves token possession completely unchanged | `proofs::raymond::theorem_delayed_request_delivery_is_safe` | Raymond invariant |

"Reachability" means the hypothesis `reachable(sys)`, i.e. some finite execution
starting from an `init` state ends in `sys`. It is discharged once and for all by
`theorem_reachable_inv`.

### Token movement is partitioned by liveness

A live holder hands the token on (`ComposedStep::PassToken`, which requires
`pre.own.live.contains(n)`); a fail-stopped one has it taken
(`ComposedStep::SeizeToken`, which requires `!pre.own.live.contains(from)`).
`proofs::composed::theorem_token_movement_is_partitioned` proves there is no
third way: routing steps, ownership transitions and acquisition all leave token
possession exactly as they found it.

The liveness guard on `PassToken` is what makes that step mean what it is
written as. `ray_assign_privilege` models the holder *acting* — choosing to hand
the privilege to the head of its queue — and a crashed node cannot act. Adding
seizure without it would have opened the forcible path while leaving the
impossible one open beside it.

### A seized node must reconcile before it returns

`cs_seize_token` rewrites the seized node's `holder` and `using` entries **while
it is down**, and `Step::Recover`'s contract says a node comes back *with no
knowledge of what happened meanwhile*. Left alone, recovery would silently
inherit that rewrite: the model would have the returning node know it had lost
the token, while the real one would still believe `holder[n] == n` and could
enter its Raymond critical section beside the new holder. Ownership would stay
safe — the epoch fences it — but Raymond's critical section has no epoch, which
is the same asymmetry as above.

So `Composed` carries `seized`, the set of nodes whose routing state was
rewritten behind their back. `cs_own` refuses `Step::Recover` for a node in it,
and `ComposedStep::Reconcile` is the only way out. The reconciliation a real
deployment must perform — re-read the routing state rather than trust what you
remember — is therefore a **modelled transition** rather than an assumption:
an execution has to contain it. `scenario_composed_crash_takeover` runs it
through to `A` rejoining afterwards, so the guard is a discipline rather than an
unreachable restriction.

### Seizure only applies to a crashed node

`ComposedStep::SeizeToken` requires `!pre.own.live.contains(from)`, and
`is_unowned` alone would not be enough.

`RevokeOwner` may fire against a perfectly healthy owner — unreliable detection
is modelled on purpose — so without the liveness guard a seizure could fire
against a live node that is inside its Raymond critical section. `ray_seize`
clears `using[from]`, so the model would then report exclusivity while two nodes
were really inside: the invariant would be preserved by *erasing* the first
node's execution rather than by anything the protocol does.

The asymmetry is the point, and it is worth stating because it marks the edge of
what epochs buy. Revoking the **ownership record** is safe against a healthy
node, because the epoch fences it. Seizing the **token** is not, because
Raymond's critical section has no epoch — there is nothing to fence a node that
believes it still holds the privilege. So seizure is restricted to fail-stopped
nodes, where clearing `using` is a fact about the world rather than a modelling
convenience.

### A node cannot fence itself

Row E is narrower than it looks, and the gap is worth stating plainly rather
than leaving a reader to infer it.

`FenceGuard::accepts` consults the node's **own** belief about the actor —
whatever generation it last observed. A partitioned `A` still holding
`FenceGuard::new(A, 41)` gets `accepts(A, 41) == true` while the system has
already moved to `Owned { B, 42 }`. The stale owner from the headline scenario
passes its own fence, every time.

That is not a contradiction: the postcondition promises
`may_mutate(self.view(), ..)`, and `view()` is exactly that stale belief. But
the safety property proved here is about the *system's* state
(`can_mutate(sys, ..)`), and nothing in `src/exec.rs` connects a guard to it.
What a guard buys is **node-local staleness rejection, not fencing**.

Real fencing has to happen where the effect lands, against authoritative state:
the storage layer refusing a write whose epoch is superseded, or a reply gate
that re-reads the ownership record after a write is durable and before
acknowledging it, refusing the acknowledgement if the record no longer names
this node at this epoch. That check is what turns exclusivity into a property an
outsider can rely on. It is not in this crate, and proving the protocol says
nothing about whether an implementation performs it.

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

* `PassToken` may only fire while the actor is `Unowned` — ownership must be
  genuinely released before the token is allowed to move. (`Transferring` also
  satisfies `!is_owned`, so guarding on that weaker condition would let the token
  move while a handover was still in flight and the outgoing owner had not yet
  acknowledged the revoke.);
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

A second job runs the same crate through `cargo verus verify`, which checks it
against the `vstd` version pinned in `Cargo.toml` rather than the prebuilt one
inside the Verus release. That entry point needs

```toml
[package.metadata.verus]
verify = true
```

in `Cargo.toml`: without it, `cargo verus verify` compiles this crate with
ordinary rustc, verifies only `vstd`, prints *vstd's* `verification results`
line and exits 0. It is a false green that survives a naive grep for the
summary, because a summary is present — just not this crate's. The CI step
therefore requires a summary emitted *after* Cargo starts compiling this
crate.

## Status: proven, modelled, future work

Against the pinned Verus release, `verus --crate-type=lib src/lib.rs` verifies
the whole crate with no errors. CI writes the current count into each run's job
summary, which is the authoritative figure — the snapshot in prose drifts, the
job summary does not.

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

**Not modelled at all** (a gap, stated rather than papered over):

* **Raymond itself has no crash model.** The ownership layer models crash,
  recovery and unreliable failure detection; Raymond's own steps do not. A
  Raymond in which nobody holds the token is not reachable, because
  `ray_token_exists` is an invariant.

  What *is* now modelled is the case that matters for the composed claim:
  `ComposedStep::SeizeToken` re-establishes the token at another node **without
  the holder acting**, so crash-driven takeover is reachable rather than
  requiring a dead node to cooperate. Before that existed, the only token
  movement in the composed machine was `PassToken`, which requires
  `has_token(pre.ray, from)` and models `from` voluntarily handing the privilege
  on — so `theorem_composed_reachable_inv` was quantified over executions in
  which the token always moves *voluntarily*, and crash-driven takeover, the
  case epochs exist for, was not among them. That was a real narrowing of the
  composed claim, and it is fixed rather than documented away
  (`scenario_composed_crash_takeover` exhibits the execution).

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

### Scenarios export runs, not endpoints

The recurring defect on this PR was a scenario whose postcondition described the
world afterwards but never how it got there — and "how it got there" is the
entire content of a scenario. Exporting a *step* was the first fix; it was not
enough, because a step and an endpoint exported as independent existentials can
come from different executions.

So both layers now carry a reachability-**from** relation —
`composed_reachable_from` and `ray_reachable_from` — and the scenarios export
runs:

* `scenario_composed_crash_takeover` exports the `SeizeToken` step *and*
  `composed_reachable_from(q, fin)`, so the `B`-owned outcome is reachable from
  the seizure post-state rather than merely reachable; likewise `Reconcile`
  linked to `A` being back and running.
* `scenario_request_and_token_routing` exports `ray_init(r0, c)` and
  `ray_reachable_from(r0, p)`, pinning where the run began — four nodes, token
  at `C` — so a directly built state with `D` already root cannot satisfy it and
  `A` and `C` must participate.

## No escape hatches

The proofs use no `assume`, `admit`, `external_body`, `axiom`, or any other way
of asserting something Verus did not check.

There are also no raised solver budgets: no `#[verifier::rlimit]` anywhere. The
long concrete scenarios are kept tractable purely by **splitting** them:

* `scenario_composed_handover` = `handover_phase_release` +
  `handover_phase_request` + `handover_phase_pass_token` +
  `handover_phase_acquire`;
* `scenario_request_and_token_routing` = `routing_phase_requests` +
  `routing_phase_token_hops` + `routing_phase_delivery`, with the token hops
  themselves delegated to `routing_one_hop`, proved once against an abstract
  state.

Each phase hands the intermediate state to the next as an *abstract*
characterisation, so no single query reasons about a dozen nested `Map`/`Set`
literals at once, and every phase verifies within Verus's default budget. Two
phases previously carried `#[verifier::rlimit(40)]`, and between them dominated
the cost of the entire proof run; splitting them removed the need. (`rlimit`
would not have been an escape hatch — it is a solver budget and cannot admit an
unproven fact — but a proof that needs a raised ceiling is usually a proof that
wants splitting.)

Splitting also surfaced a genuine defect in the specification. Reduced to a
single `AssignPrivilege` step, `routing_one_hop` *still* exceeded the solver's
limit — a cost that scaled with nothing in the proof. `verus --profile` named
the cause: `ray_wf` was a **matching loop**. Under the trigger
`r.nodes.contains(n)`, its conclusion `r.nodes.contains(r.holder[n])` matched
that same trigger at `r.holder[n]`, and so on without bound — 171,941
instantiations of one quantifier, 40% of 419,801 in a single proof.

`ray_wf` is now `ray_maps_total` (entries exist, triggered on
`r.nodes.contains(n)`) and `ray_holder_closed` (pointers stay in the cluster,
triggered on `r.holder[n]`). The second trigger fires only for holder pointers
some term already mentions, and its conclusion creates no new `holder[_]` term,
so nothing regenerates it. This mattered beyond speed: a matching loop makes
proofs pass or fail according to how many instantiations the solver burns before
it stumbles on the argument, which is precisely the kind of fragility a proof
suite should not have.

Every quantifier in `src/` has since been audited for the same defect, and three
more were found and fixed: `ray_init`'s non-root clause and `ray_holder_closed`
regenerated each other across two quantifiers, and `valid_execution` /
`composed_valid_execution` walked off the end of a sequence (`tr[i]` introduces
`tr[i + 1]`, which matches the trigger at `i + 1`; the `i < tr.len() - 1`
antecedent is checked *after* instantiation, so it does not stop e-matching).
Both now use multi-triggers naming the terms that must already exist.

The same care applies to `assert forall`, which carries whatever trigger is
written at the assertion site — `lemma_ray_frame_inv` and `lemma_reachable_step`
had each rebuilt a loop locally that the specification no longer contained.

CI greps `src/` for the real escape hatches and fails the build if any appear.
Everything the proofs rely on that is not derived is a modelled transition or an
explicitly documented entry in the failure-model table above.
