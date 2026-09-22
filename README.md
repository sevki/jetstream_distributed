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

## Relation to Chubby

The obvious prior art is [*The Chubby lock service for loosely-coupled
distributed systems*](https://storage.googleapis.com/gweb-research2023-media/pubtools/4444.pdf)
(Burrows, OSDI 2006). It is worth being precise about the relationship, because
the central mechanism here is Chubby's, not a new one.

**The fencing mechanism is the same idea.** Chubby §2.4: a lock holder may
request a *sequencer*, "an opaque byte-string that describes the state of the
lock immediately after acquisition", containing the lock name, the mode, and the
**lock generation number** — a per-node counter that "increases when the node's
lock transitions from free to held". The client passes it to the resource
server, which "is expected to test whether the sequencer is still valid ... if
not, it should reject the request". That is exactly `Token { actor, epoch,
holder }` plus `valid_fence`, and Chubby's lock generation number is this
model's `Epoch`. This repository is a formalisation of that design, not an
alternative to it.

**What this adds is the proof, and the precision that a proof forces.** Chubby
is an experience paper: it describes the initial design, compares it with actual
use, and explains how the design had to change. It carries no machine-checked
proofs, and it does not need to — its evidence is years of production at scale.
The evidence here is different in kind. "The recipient server is expected to
test whether the sequencer is still valid" is doing a great deal of work in that
sentence, and writing the obligation down as a state machine is what turns it
into something checkable:

* who may mutate is a single predicate, `may_mutate`, and
  `theorem_no_authority_without_token` proves that anyone who satisfies it
  provably holds an issued token for exactly that `(actor, epoch)`;
* the headline scenario — `A` owns at 41, `B` takes over at 42, `A` returns
  still holding its epoch-41 token — is the situation sequencers exist for, and
  it is discharged as a nine-step execution rather than argued informally;
* the awkward part, **a node cannot fence itself**, becomes impossible to leave
  implicit. `FenceGuard::accepts` consults the node's own belief, so a
  partitioned holder accepts its own stale epoch; the rejection that matters
  happens where the effect lands. Chubby's locks are *advisory* for exactly this
  reason — "holding a lock called F neither is necessary to access the file F,
  nor prevents other clients from doing so" — and this model is advisory in the
  same sense, but has to say so in a proof obligation rather than in prose.

**Three deliberate differences, and why.**

| | Chubby | here |
| --- | --- | --- |
| Timing | `lock-delay`: after a holder fails, the lock is withheld for up to a minute, protecting servers that do **not** check sequencers. Described in the paper as "imperfect but easier". | No timing assumptions at all. Messages never expire, `issued` and `network` never shrink, and safety rests only on epoch ordering. A delay-based argument cannot be proved safe in an asynchronous model, so the unmodified-server path is deliberately not modelled. |
| Consensus | A Chubby cell is five replicas running Paxos; that is what makes a lock's state a single agreed fact. | Assumed, not modelled. "Ownership records are updated atomically" is the first row of the failure-model table, and Chubby is precisely the kind of thing that would discharge it. |
| Topology | Centralised: clients talk to a master. | The privilege is routed **peer-to-peer** by Raymond's algorithm, and `couples` proves routing cannot manufacture authority. Chubby has no analogue, because it does not need one. |

The third difference is where this model has something Chubby does not, and it
is also where it was recently found to be wrong. Because privilege moves between
peers rather than being held centrally, a node can be left believing it holds
the privilege after the privilege has moved. Chubby handles the corresponding
case by checking a sequencer "against the server's Chubby cache or ... the most
recent sequencer that the server has observed" — belief is checked against
authority. This model originally had no such split on the routing side and
resolved a seizure by editing the absent node's state, which no implementation
can do; see [The holder graph is a tree](#the-holder-graph-is-a-tree-and-now-says-so)
and the `believes_holds` / `has_token` split in `src/raymond.rs`.

**What Chubby has that this does not**: a deployed system, sessions and
KeepAlives, failover, caching with invalidations, a filesystem namespace, ACLs,
events, and liveness of any kind. This model proves safety only, and says so.

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
| E1 | **Acquire refines `tr_acquire`** — when the step fires the model fires, to exactly the record the step computed; when it refuses a request naming the actor's current epoch, *no* post state satisfies `tr_acquire`; and however the model acquires, the record it lands on is the one the step computes | `proofs::refinement::theorem_acquire_step_refines_tr_acquire`, `..._refuses_exactly_when_disabled`, `..._outcome_is_the_step` | the couplings (see the module docs of `proofs::refinement`); the refusal direction additionally assumes the request named the current epoch, which is the one place the executable step is narrower than the model |
| E2 | **Begin-transfer refines `tr_begin_transfer`**, in the same three parts. Refusal is exactly disablement *or* epoch exhaustion, and the refusal says which | `proofs::refinement::theorem_begin_transfer_step_refines_tr_begin_transfer`, `..._refuses_exactly_when_disabled`, `..._outcome_is_the_step` | the couplings; `u64` exhaustion is the implementation's, not the model's |
| E3 | **Release refines `tr_handle_revoke` followed by `tr_complete_release`** — two model transitions, one method, with the middle state exhibited rather than assumed to exist. A refused release is provably not the handover the model would complete | `proofs::refinement::theorem_release_step_refines_handle_revoke_then_complete_release`, `theorem_refused_release_is_not_the_models_release` | the couplings, and that the `Revoke` being acknowledged is on the network — which `tr_begin_transfer` put there |
| E4 | **Forced revocation refines all three of its transitions**: `tr_revoke_owner` from `Owned`, `tr_reassign_unowned` from `Unowned`, `tr_abort_transfer` from `Transferring` — and in the last case the actor provably goes back to the node the transfer came from, whatever successor the coordinator named | `proofs::refinement::theorem_force_step_refines_tr_revoke_owner`, `..._tr_reassign_unowned`, `..._tr_abort_transfer` | the roster answers `pre.nodes.contains(next)` |
| E5 | **A poll is `tr_issue_grant` or the delivery of a `Revoke`**, and the epoch it offers is the actor's current one — so a poll can never hand out a generation the registry has already left. `Nothing` is returned only to a node that is owed nothing | `proofs::refinement::theorem_poll_step_refines_tr_issue_grant`, `..._tr_handle_revoke`, `theorem_poll_step_offers_nothing_only_when_nothing_is_owed` | the couplings |
| E6 | **The registry's fence is the *system's* fence** — `may_write_step` on the registry's own record is `can_mutate`, not a node's belief about it. Same postcondition as E, different thing, bought entirely by where it is called | `steps::may_write_step`, `proofs::refinement::theorem_may_write_step_is_the_system_fence` | the record the step is handed is the actor's |
| E7 | **The refinement theorems are not vacuous.** Each is an implication under hypotheses, and hypotheses that cannot all hold make a theorem true and empty — a refinement suite can be green and say nothing. So one concrete system is written out in full and a whole handover walked through it, each theorem applied to the state the previous one produced, with what came out asserted | `proofs::refinement::scenario_a_handover_through_the_verified_steps` | none: the system is exhibited |
| E7a | The same for the *refusal* theorems, whose hypotheses are the negation of a guard and so are untouched by a run in which the guard holds. In a system where no grant was published, **no** post state satisfies `tr_acquire` — quantified over all of them, not over one the server had in mind | `proofs::refinement::scenario_the_refusals_are_refusals_of_something_real` | none |
| P1 | **Issued tokens never disappear** — no crash, partition or recovery retracts a capability, which is why stale tokens must be fenced rather than revoked | `proofs::properties::theorem_issued_monotone` | none |
| P2 | **Sent messages never disappear** — the fact that makes duplication, reordering and unbounded delay free in the model | `proofs::properties::theorem_network_monotone` | none |
| P3 | **The actor population is constant** — no transition creates or destroys an actor | `proofs::properties::theorem_actor_domain_constant` | none |
| P4 | **An epoch advances by at most one per transition** — with claim 5, the epoch sequence is non-decreasing and never skips a generation | `proofs::properties::theorem_epoch_increases_by_at_most_one` | none |
| P5 | **Ownership at a given epoch is final** — once owned by `n` at `e`, every later state still at `e` is still owned by `n` at `e`; a handover *must* burn the epoch | `proofs::properties::theorem_ownership_at_an_epoch_is_final` | valid execution |
| P6 | **An epoch determines its owner** — any two points of an execution owned at the same epoch have the same owner | `proofs::properties::theorem_epoch_determines_owner` | valid execution |
| P7 | **Staleness is permanent** — a fenced-out node can never be fenced back in by waiting | `proofs::properties::theorem_stale_stays_stale` | valid execution |
| P8 | **No authority without a capability** — a node that may mutate provably holds an issued token for exactly that `(actor, epoch)` | `proofs::properties::theorem_no_authority_without_token` | reachability |
| P9 | **Epoch monotonicity survives composition** | `proofs::properties::theorem_composed_epoch_monotone` | none |
| R9 | **The privilege is never lost** — every Raymond transition leaves `privilege` pointing at a node | `proofs::raymond::lemma_ray_token_exists_init`, `lemma_ray_token_exists_step` | Raymond invariant |
| R10 | **Raymond critical sections are exclusive — while nobody's belief is stale.** The hypothesis is not a weakening; it is the algorithm's real scope. Raymond's mutual exclusion rests on every node agreeing where the privilege is, and a seizure breaks that until the seized node reconciles | `proofs::raymond::theorem_ray_critical_section_is_exclusive` | Raymond invariant, `ray_no_stale_holders` |
| R10a | **At most one node is *authorised* to be in its critical section**, with no side conditions: the authorised occupant is the privilege holder, and there is one of those by construction. This is the part of R10 that survives a seizure | `proofs::raymond::theorem_authorised_critical_section_is_exclusive` | Raymond invariant |
| R13 | **A stale holder confers no authority.** A node that believes it holds the privilege, does not, and may still be inside its critical section, still cannot mutate the actor — `couples` is written against possession, not belief. The routing counterpart of 6b, and what survives imperfect failure detection | `proofs::raymond::theorem_stale_holder_confers_no_authority` | the coupling |
| R14 | **Reconciliation repairs the belief**: the stale holder drops it, leaves the critical section it thought it was in, and re-points at the real holder | `proofs::raymond::lemma_reconcile_preserves_inv` | Raymond invariant |
| R11 | **The holder pointers are acyclic** — part of `ray_inv`, preserved by every transition. A handover rewrites two pointers and needs a new rank (the old one shifted up by one, new root at zero); a seizure only makes the new holder point at itself, which *removes* a constraint, so the old rank still works | `proofs::raymond::lemma_frame_acyclic`, `lemma_repoint_acyclic` | Raymond invariant |
| R12 | **Every node reaches the privilege holder by following holder pointers** — what makes "requests travel hop-by-hop towards the token" a checked claim. Two hypotheses, both load-bearing: R11 says the walk terminates rather than circling, and `ray_no_stale_holders` says it terminates at the real holder rather than at somebody who merely thinks so. The second was free when authority *was* belief; it is not free now, and it should not be — after a seizure a node whose belief-path leads to the seized holder genuinely cannot route to the privilege | `proofs::raymond::theorem_every_node_reaches_the_token` | Raymond invariant, `ray_no_stale_holders` |
| I | The inductive invariant holds in every reachable state (`init ==> inv`, `inv /\ next ==> inv`) | `proofs::invariant::theorem_reachable_inv` | the model's transition relation |
| S | **The headline scenario**: `A` owns X@41, a transfer and a crash/recovery occur, `B` owns X@42, `A` returns still holding its epoch-41 token - and cannot perform an authoritative mutation. The postcondition exports the whole nine-step run, so the crash, the recovery and the outcome are the same execution — exported as separate existentials they need not have been, and an ordinary live handover could supply the outcome | `proofs::adversarial::scenario_stale_owner_returns` | `A != B` |
| S1 | A stale `Grant` cannot resurrect a superseded epoch | `proofs::adversarial::theorem_stale_grant_cannot_be_used` | none |
| S2 | Message duplication / reordering / delay cannot change ownership | `proofs::adversarial::theorem_network_steps_cannot_change_ownership` | none |
| S3 | Crash and stale-node recovery cannot change ownership | `proofs::adversarial::theorem_crash_recovery_cannot_change_ownership` | none |
| S4 | An interrupted transfer leaves nobody with authority and burns the epoch. A step property, not a constructed execution — hence `theorem_`, not `scenario_` | `proofs::adversarial::theorem_interrupted_transfer_burns_the_epoch` | `inv` holds before the step (and so, by `theorem_reachable_inv`, every reachable state) |
| S4a | **An interrupted transfer really happens**: the run is exported with its four labels, so the `AbortTransfer` at index 3 interrupts the very `BeginTransfer` at index 2 that opened the transfer, ending at `Unowned(43, A)` with nobody able to mutate at 41 or 42. Without it, S4 stays provable even if `AbortTransfer` were changed to be always false — a conditional lemma about an unreachable transition | `proofs::adversarial::scenario_interrupted_transfer` | `A != B` |
| S5 | **A fabricated `Released` is inert.** `HandleRevoke` lets any live node manufacture a `Released` from any `Revoke` ever sent, however old. `CompleteRelease` is the only step that consumes one, and it re-reads the actor's current state, so if it fires the actor is `Transferring` right now and the network holds the `Released` naming exactly that handover's `from` and `new_epoch` | `proofs::adversarial::theorem_complete_release_needs_the_matching_released` | none |
| S6 | **A fabricated `Released` cannot steer a handover.** The resulting epoch is read from the live `Transferring` record, not from the message | `proofs::adversarial::theorem_complete_release_outcome_is_fixed_by_state` | none |
| R1 | **Raymond: exactly one valid privilege** - now *structural*: `Raymond::privilege` is one node id, so uniqueness needs no invariant. It used to be inductive, and that was exactly what made a returning stale holder unrepresentable | `proofs::raymond::theorem_ray_exactly_one_token`, `theorem_ray_at_most_one_token`, preserved by `lemma_ray_step_preserves_inv` | Raymond invariant |
| R2 | **Raymond: holder/routing changes cannot manufacture ownership** | `proofs::raymond::theorem_routing_cannot_manufacture_ownership` | Raymond invariant, coupling |
| R3 | **Raymond: duplicate/reordered requests cannot create a second owner** | `proofs::raymond::theorem_duplicate_requests_are_safe` | Raymond invariant |
| R4 | **Raymond: token transfer preserves ownership safety** | `proofs::composed::lemma_composed_pass_token_preserves_inv` (and, as a layer-local lemma, `proofs::raymond::theorem_token_transfer_preserves_ownership_safety`) | none — in the composed machine the release-before-transfer condition is a *guard*, not an assumption |
| R5 | **Composed exclusivity**: in every reachable composed state at most one node may mutate the actor, and it is the node holding the token | `proofs::composed::theorem_composed_exclusivity` | composed reachability |
| C0 | **Non-degeneracy**: a composed state in which a node is *actually inside* the critical section is reachable from `composed_init`. The contract exports the run: three labels, `RequestCs` / `EnterCs` / `ExitCs`, with `using` false at indices 0, 1 and 3 and true at 2 — so the node inside got there by entering, and the exit leaves the state it entered | `proofs::composed_scenario::scenario_composed_critical_section` | `A != B` |
| C0a | (Step-level lemma backing C0) `EnterCs`/`ExitCs` are legal `ComposedStep::Ray` transitions and preserve the composed invariant | `proofs::composed::theorem_composed_admits_critical_section`, `..._exit` | composed invariant holds before the step |
| C1 | **Non-vacuity**: a complete *voluntary* handover driven through **both** layers is reachable. The contract exports the whole run: `labels == handover_labels(x, a, b)` — ten steps, `BeginTransfer` at 2, `CompleteRelease` at 4, `PassToken` at 8 — plus the `Transferring { a, b, 41, 42 }` state at index 3, since the labels carry no epochs. No other execution satisfies it: the substitutes that satisfied earlier versions were crash takeover, revoking a live `A`, and an unrelated 39 → 40 transfer | `proofs::composed_scenario::scenario_composed_handover` | `A != B` |
| C2 | **Crash-driven takeover is reachable in the composed machine**: `A` owns X@41 holding the token, crashes and takes no further step; the coordinator burns the epoch; the token is *seized*; `B` ends up owning X@42 and holding the token, with `A`'s epoch-41 token still issued and powerless. The postcondition exports the whole run — eight labels with `Crash(A)` at 2, `RevokeOwner` at 3 and `SeizeToken` at 4, and no `CompleteRelease` anywhere, so a voluntary release before the crash cannot stand in for the revocation | `proofs::composed_scenario::scenario_composed_crash_takeover` | `A != B` |
| C3 | Seizing the token preserves the coupling and leaves the target holding the one token — safety comes from the epoch being burned first, not from the holder agreeing to let go | `proofs::composed::lemma_composed_seize_preserves_inv`, `proofs::raymond::lemma_seize_preserves_inv` | composed invariant. **No liveness assumption**: the epoch was burned first, so this holds even when the seized node is healthy and was suspected wrongly — see below |
| C4 | **Privilege movement is partitioned by cooperation**: a holder that acts passes it on, a holder that does not has it taken, and no other composed step moves it at all. This used to be partitioned by *liveness*, which required a guard no coordinator can evaluate | `proofs::composed::theorem_token_movement_is_partitioned` | composed invariant |
| C5 | The two layers describe the **same cluster**: `ray.nodes == own.nodes` is part of `composed_inv` and `composed_init`. Without it a Raymond root could be a node the ownership layer never heard of, so `!own.live.contains(n)` would hold for it with no `Crash` having happened, and the seizure guard would be satisfied by unmodelled liveness rather than by a fail-stop | `composed::composed_inv`, preserved by `proofs::composed::theorem_composed_step_preserves_inv` | — |
| P10 | **The node population is constant** — `Crash` and `Recover` move nodes in and out of `live`, never out of `nodes` | `proofs::properties::theorem_node_domain_constant` | none |
| C6 | **A seized node cannot rejoin `live` while still seized** — `cs_own` refuses `Recover` for it, so the only way back is through `Reconcile`, which now carries the content the claim always asserted: it is where the stale belief is dropped, by the node that holds it. Backed by `composed_inv`'s "every stale holder owes a reconciliation", which is what makes `seized` mean somethint must perform a step an execution has to contain rather than an assumption | `proofs::composed::theorem_seized_node_cannot_recover` | — |
| C7 | Reconciliation is **not a dead end**: `A` can be told what happened and then rejoin, holding no token and no authority | `proofs::composed_scenario::scenario_composed_crash_takeover` (third witness) | `A != B` |
| C | The coupling is an **invariant** of the composed machine: `composed_init ==> composed_inv`, `composed_inv /\ composed_next ==> composed_inv`, hence `composed_reachable ==> composed_inv` | `proofs::composed::theorem_composed_reachable_inv`, `theorem_composed_step_preserves_inv` | the composed transition relation |
| R6 | A concrete routing execution: request `D → B → A → C[token]`, token `C → A → B → D`, then a twelfth step redelivering `D`'s original request after the token has finished moving. The contract exports the whole run — `tr[0] == routing_init_state(a, b, c, d)` and `labels == routing_labels(a, b, c, d)` — which pins the *path* and not just the endpoints: exactly one `RequestCs`, `D`'s, so each forward is caused by the receive before it. Pinning `r0` alone was not enough, because reachability still admitted `A`, `B` and `D` requesting independently and serving their own queue heads | `proofs::raymond_routing::scenario_request_and_token_routing` | four distinct nodes |
| R7 | A request outlives the topology it was routed against: after the token moves it is still in `requests` and still deliverable | `proofs::raymond::theorem_delayed_request_survives_token_move` | none |
| R8 | Delivering an arbitrarily delayed request preserves the Raymond invariant and leaves token possession completely unchanged | `proofs::raymond::theorem_delayed_request_delivery_is_safe` | Raymond invariant |

"Reachability" means the hypothesis `reachable(sys)`, i.e. some finite execution
starting from an `init` state ends in `sys`. It is discharged once and for all by
`theorem_reachable_inv`.

### Privilege movement is partitioned by cooperation

A holder that acts hands the privilege on (`ComposedStep::PassToken`, which
requires `pre.own.live.contains(n)` and `believes_holds`); a holder that does
not has it taken (`ComposedStep::SeizeToken`).
`proofs::composed::theorem_token_movement_is_partitioned` proves there is no
third way: routing steps, ownership transitions, acquisition and reconciliation
all leave possession exactly as they found it.

The `SeizeToken` arm used to claim `!pre.own.live.contains(m)` as well, because
seizure was guarded on it. It no longer is, and the arm now says only what is
true and checkable: the privilege moved away from `m` without `m` taking a step.
That is the distinction a deployment can act on — a coordinator knows whether
*it* is forcing the transfer; it does not know whether the node is alive. See
[Seizure needs no oracle](#seizure-needs-no-oracle-belief-versus-authority).

The liveness guard on `PassToken` stays, and means something different: it is
not a detection requirement but a statement about who is acting.
`ray_assign_privilege` models the holder *choosing* to hand the privilege to the
head of its queue, and a crashed node cannot choose anything.

### A seized node must reconcile before it returns

A seizure leaves the seized node's `holder` and `using` entries exactly as they
were — nobody can reach into a machine that is down — and `Step::Recover`'s
contract says a node comes back *with no knowledge of what happened meanwhile*.
So a node that is simply allowed to recover comes back still believing
`holder[n] == n`, and can enter its Raymond critical section beside the new
holder. Ownership stays safe, because the epoch fences it; Raymond's critical
section has no epoch.

So `Composed` carries `seized`, the set of nodes whose privilege was taken and
whose belief has not yet been repaired, and `composed_inv` ties it to reality:
**every stale holder owes a reconciliation**. `cs_own` refuses `Step::Recover`
for a node in that set, and `ComposedStep::Reconcile` is the only way out.

The reconciliation a real deployment must perform — re-read the routing state
rather than trust what you remember — is therefore a **modelled transition**
with content, not a marker: it is the step in which the belief is dropped, the
critical section left, and the holder pointer re-aimed at the node that actually
holds the privilege. `scenario_composed_crash_takeover` runs it through to `A`
rejoining afterwards, so the guard is a discipline rather than an unreachable
restriction.

It is not guarded on the node being down. Seizure is no longer restricted to
crashed nodes, so a live node can be left stale by a coordinator that suspected
it wrongly, and must be able to learn the truth too. What the ordering rule
still enforces is the crashed case: you cannot come back and start acting on a
belief you never corrected.

### Seizure needs no oracle: belief versus authority

An earlier version of this model guarded `ComposedStep::SeizeToken` on
`!pre.own.live.contains(from)`, with this argument: `RevokeOwner` may fire
against a perfectly healthy owner, so without a liveness guard a seizure could
fire against a live node inside its Raymond critical section; `ray_seize` clears
`using[from]`, so the model would report exclusivity while two nodes were really
inside.

The analysis was right and the conclusion was wrong, twice over.

**It conflated two guarantees.** Ownership safety is fenced by the epoch, which
is burned *before* the seizure fires, so it never needed the node to be dead.
Only Raymond's critical-section exclusivity needed anything, and what it needs
is a condition on the *state* — `ray_no_stale_holders` — not a guard on the
step. The difference matters: a state condition is something a deployment can
restore, by reconciling; a step guard is something it must evaluate.

**And `!live` is ground truth, which no coordinator has.** It has a suspicion —
which is exactly why `RevokeOwner` is modelled as firing against healthy nodes.
Guarding the forcible path on perfect failure detection put the composed
machine's strongest theorems out of reach of any real deployment, in a clause
that read like an ordinary guard.

The repair was the one the ownership layer had already made once. `issued` keeps
a crashed node's capability for ever and `token_authorized` decides whether it
still confers anything; the routing layer now makes the same split:

| | physical / believed | authoritative |
| --- | --- | --- |
| ownership | `issued` | `token_authorized` |
| routing | `holder[n]` — state stored *at* `n` | `Raymond::privilege` |
| predicate | `believes_holds(r, n)` | `has_token(r, n)` |

`ray_seize` now touches only the new holder. `from`'s `holder`, `using` and
`asked` entries are left exactly as they are, because they live on a machine
nobody can reach — editing them was modelling something no implementation can
do. What that creates is a **stale holder**: a node that believes it holds the
privilege, does not, and may still be inside its critical section believing that
too.

That state is the point. It could not previously be written down, because
`ray_unique_token` was an inductive invariant over the holder pointers and the
state violated it outright — the invariant held partly because the dangerous
state was unrepresentable, which is the pattern the ownership layer takes such
care to avoid. Uniqueness is now *structural* (`privilege` is one value), the
stale state is representable, and `theorem_stale_holder_confers_no_authority`
proves it inert: `couples` is written against possession, so belief confers
nothing however firm it is.

**The rule this leaves behind.** Not all liveness guards are oracles, and the
difference is which node the step makes *act*:

> **Liveness may guard the nodes a step makes act, and may not guard the ones it
> does not.**

A guard on an acting node is a statement about who takes part — nobody has to
determine anything, because if the node is down the exchange simply does not
happen. A guard on a non-acting node is an oracle, because something must
evaluate it before the step may fire. `!live(from)` was the second kind, which
is why it had to go; `live(n)` on `cs_pass_token` was always the first kind.

Applying the rule uniformly closed two more holes of exactly the shape the
review found, on the *receiving* side:

* `cs_pass_token` now guards `head` as well as `n`. `ray_assign_privilege` has
  `head` record `holder[head] := head`, so if `head` crashed after its request
  reached `n`, the old step installed a belief in a node that could not receive
  it — and a later `Recover(head)` framed it in, modelling the node as knowing
  about an event it never observed.
* `cs_seize_token` guards `to` for the same reason: the coordinator hands it the
  privilege and it records that, so it is acting.

The rule covers the **ownership** layer too, and enumerating it there found the
last gap: `tr_begin_transfer` is documented as "the current owner agrees to hand
`actor` over", which is an action by `from`, and it had no liveness guard. So
`Acquire(A) → Crash(A) → BeginTransfer(A, B)` was accepted — a crashed node
volunteering. That one matters beyond tidiness: `RevokeOwner` and `SeizeToken`
exist precisely for the case where the owner *cannot* cooperate, and a model in
which the dead cooperate does not need them.

The full audit, by who acts:

| transition | acting node | guard |
| --- | --- | --- |
| `Acquire` | the acquiring node | `live(n)` |
| `BeginTransfer` | the outgoing owner | `live(from)` — **added** |
| `HandleRevoke` | the revoked node | `live(target)` |
| `Crash` / `Recover` | the node | `live` / `!live`, being the boundary itself |
| `IssueGrant`, `CompleteRelease`, `AbortTransfer`, `RevokeOwner`, `ReassignUnowned` | none — the coordinator | correctly unguarded |
| `Replay` | none — the network | correctly unguarded |
| `Stutter` | none — it does nothing | correctly unguarded |

That is all twelve variants of `Step`, which is the point: a table that omits
one cannot support a coverage argument, however right the rows it does contain
are. This one omitted `ReassignUnowned` and `Stutter` when first published.

`RevokeOwner` being unguarded is the design, not an oversight: it is the step
that fires *without* the owner's cooperation, against a node that may be
perfectly healthy. `ReassignUnowned` is the same shape — the coordinator
re-offering an actor that nobody owns, burning an epoch to do it.

`cs_ray` guards whichever node the Raymond step makes act
(`ray_step_actor`), which is the carrier that has most of them. Without it a
crashed node could queue requests, forward them, and — the serious case — enter
its critical section: after `Crash(A) → RevokeOwner → SeizeToken(A, B)`,
`Ray { EnterCs(A) }` fired on `A`'s untouched holder and queue while `A` was
still down and still marked, walking straight past the
reconciliation-before-acting discipline. `ReceiveRequest` acts at `at`; `from`
sent its request earlier and takes no part in the delivery.

`cs_reconcile` guards nobody, and that is not an exception to the rule but a
consequence of what `live` means here. `live` is *participating in the
protocol*, not *powered on* — the field's documentation said "currently up"
until this was chased down, which was a second meaning hiding in one set. Reconciliation is the boundary step — the node
re-reading authoritative state as part of coming back, before it resumes
participating — which is why it may fire while `!live` and why `Recover` is a
separate step that follows it. A node that was seized while live may also
reconcile at any time, since it is acting either way.

**Granting the privilege discharges the debt.** Both grant steps now clear the
recipient from `seized`, because receiving the privilege *is* the node learning
the truth: it is live, it records `holder := itself`, and it really does hold, so
its belief is correct again. Without that, a node marked by an earlier seizure
and later handed the privilege back would stop being stale while staying marked
— and `cs_reconcile` requires `is_stale_holder`, so the marker could never be
cleared and `recovers_a_seized_node` would reject that node's recovery for ever.

That state became reachable only when the `!live(from)` guard came off. Before,
a marked node was always dead and had to reconcile before rejoining, so it could
never be a live grant target; afterwards it can be. A guard removed for good
reasons opened a path that had to be closed somewhere else.

Three consequences worth stating plainly:

* **`cs_seize_token` has no liveness guard at all.** Ownership safety survives
  seizure from a node that is perfectly healthy and wrongly suspected, which is
  the case a deployment will actually hit.
* **Raymond's mutual exclusion has a window.** Between a seizure and the seized
  node's reconciliation, two nodes can be inside their critical sections. That
  is true of any system that takes a privilege away from a node it cannot reach,
  and the model now says so instead of hiding it.
* **`cs_reconcile` acquired its content.** It used to remove a marker and change
  nothing else; the work it claimed to model had already been done at seizure
  time, by the coordinator, to a node it could not talk to. Now it is where the
  belief is dropped — by the node that holds it.

Chubby reaches the same place from the other direction: a sequencer's validity
is checked "against the server's Chubby cache or ... the most recent sequencer
that the server has observed", which is belief checked against authority. See
[Relation to Chubby](#relation-to-chubby).

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
tracks a `holder` pointer (that node's **belief** about the next hop towards the
privilege), a request `queue`, an `asked` flag (outstanding request) and `using`
(inside the critical section). Alongside them, and deliberately *not* derived
from them, is `Raymond::privilege`: the node that **actually** holds it.

That split is the routing counterpart of `issued` versus `token_authorized` in
the ownership layer, and it is what lets a seizure take the privilege from a
node without reaching into it. `believes_holds(r, n)` is belief, `has_token(r, n)`
is authority, and `is_stale_holder(r, n)` is the gap — see
[Seizure needs no oracle](#seizure-needs-no-oracle-belief-versus-authority).

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
│   ├── steps.rs        the transitions as executable u64 functions
│   ├── exec.rs         the u64 fence check a node runs on its own belief
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
│       ├── raymond_routing.rs  the D → B → A → C routing execution
│       └── refinement.rs   steps.rs agrees with the model's tr_* transitions
├── tests/
│   ├── scenario_body/mod.rs    the executable protocol + the runtime oracles
│   ├── turmoil_ownership.rs    named stories, each with an expected ending
│   ├── turmoil_scenarios.rs    the blind seed search + the regression replay
│   └── seeds/scenarios.txt     seeds that once broke something
├── services/
│   └── ownership/              the protocol as a Jetstream service
└── .github/workflows/verify.yml
```

This differs from a plain `proofs/` directory at the repository root: Verus
verifies a *crate*, so every proof file has to be a module of that crate. Keeping
them under `src/proofs/` is the ordinary Rust way to express that; a top-level
`proofs/` would need `#[path = "../proofs/..."]` attributes for no benefit.

Executable code *in the crate* is confined to two modules. `src/steps.rs` holds
the protocol's transitions as small `u64`-valued functions — one per request a
server answers — each with a postcondition stated in terms of the model and a
theorem in `src/proofs/refinement.rs` discharging it. `src/exec.rs` holds the
fence check a node runs against its own belief, which is a different thing from
the fence a registry runs and says so at length. Other executable code in the
repository lives under `tests/` and `services/`, where it is simulation and
service rather than library — see
[Network resiliency](#network-resiliency-the-model-run-for-real)
and [The protocol as a Jetstream service](#the-protocol-as-a-jetstream-service).
`exec` offers **queries only**: a `FenceGuard` has private fields, a single
constructor and no setter, so its ghost view is fixed at construction. Were it
mutable — by a `bump` method or by assigning to a public field — its view could
drift from `Owned(A, e)` to `Owned(B, e + 1)`, exactly the atomic ownership
assignment this model refuses to admit. Observing a new generation means
constructing a new guard. Making a
guard follow the protocol needs a refinement of the *node* side; the registry
side is `src/steps.rs`.
Everything else in the crate is specification or proof.

Specification and proof code are kept apart from the model: `src/model.rs`
defines only the state space and the transition relation and does not import the
specification layer, so a specification cannot be quietly weakened to fit the
model.

## The protocol as a Jetstream service

Everything above is a model and a simulation of it. `services/ownership/` is the
protocol served over [Jetstream](https://github.com/sevki/jetstream) RPC — a
`#[service] trait Ownership` with `poll`, `acquire`, `write`, `begin_transfer`
and `release`, implemented by a `Registry` that performs the fence with
`exec::FenceGuard`.

**The service form removes a class of defect rather than guarding against it.**
The line protocol in `tests/` carries the sender as a field — `WRITE 0 41`
*claims* to be node 0 — so the registry has to be told to believe the connection
rather than the claim, and every request is a place to get that wrong. Four
rounds of review on that suite were spent hardening exactly that rule. Here no
method takes a node number at all. Who is calling is the `Context`, which
Jetstream fills in from the transport: *"The context is the transport's, not the
frame's"* (`jetstream_rpc::server`). A caller cannot forge it, so "the line lied
about who sent it" is not defended against — it is unrepresentable.

`force` is absent from the trait for the same reason. It is the coordinator's
own transition, and the line protocol needed a dedicated control connection to
stop a node sending it; a node-facing service simply does not offer it.

**The assumption, stated rather than assumed.** `Context::peer()` is the
authenticated identity and is `None` over plain TCP — jetstream's own comment
says a plain stream authenticates nothing. The authenticated forms are a TLS
certificate or an iroh `NodeId`, and `NodeId`'s value is private with no
accessor outside `jetstream_rpc`, so neither is usable yet. The service
therefore identifies a caller by address, against a roster fixed at
construction. **An address is not a credential.** In a simulated network nothing
can spoof one; on a real network it is worth very little. Replacing it with TLS
identity is the first thing to do, and what does not change when it is replaced
is the shape: identity arrives with the connection, never in an argument.

**Neither durable nor replicated — and one of those is now fixed.** The
registry's state lives in an `Arc<Mutex<..>>`, which supplies the *atomic* half
of the model's strongest assumption and none of the *durable* half. That gap is
not a tidiness problem: every fencing theorem assumes epochs only go up, and a
registry that comes back not knowing where it was can offer an epoch it already
burned. A partitioned owner still holding that epoch is then unfenced — not
because the fence failed, but because it was asked about a world that had been
rewound.

So the starting epoch is no longer a number from the caller. It is read from an
`EpochFloor`: a durable, monotone high-water mark of every epoch the registry
has ever used. `Registry::new` starts strictly above it and writes that down
before serving, and each later burn is recorded *before* the state depending on
it is visible, so a registry that dies mid-decision skips an epoch — the safe
direction, since epochs must not repeat but need not be consecutive.
`services/ownership/tests/durability.rs` runs the same handover against a floor
that remembers and against one that forgot, and asserts in the second case that
the already-fenced owner writes again at the burned epoch while the node holding
the *later* epoch is the one refused.

What is still missing is replication. Two registries sharing one floor would
both read it and both believe they had allocated the next epoch: durability and
atomicity want to come from the same place, which is why the row above says a
real deployment keeps the ownership record in a store with compare-and-swap.
This is the same class of caveat as the address-identity one, and it breaks the
same guarantee.

**What is verified about it, precisely.** Every decision the service makes about
the actor, and nothing else. `poll`, `acquire`, `write`, `begin_transfer`,
`release` and `force` each look the actor's record up, hand it to a function in
`distributed_ownership::steps`, and store what comes back; those functions are
executable `u64` code with postconditions stated in terms of the model, and
`proofs::refinement` is where the postconditions are tied to `tr_acquire`,
`tr_begin_transfer`, `tr_handle_revoke`, `tr_complete_release`,
`tr_revoke_owner`, `tr_reassign_unowned`, `tr_abort_transfer` and
`tr_issue_grant` — rows E1 to E6 above.

Two things are worth being exact about. First, the refinement is stated in both
directions where the notion makes sense: a step function that refused everything
would satisfy "whenever it fires, the model steps" perfectly, so the theorems
also say that a refusal means the model's step is *not enabled*. Second, what is
left outside is named rather than left to be discovered: **the lock, the identity
lookup, the durable epoch floor and the audit log are not verified.** They are
the server's business, and a step function that also resolved identity would
have quietly folded an unverified lookup inside a verified transition.

The couplings that connect one actor's `u64` record to a whole `System` are
hypotheses of the theorems rather than silent assumptions — the registry's
issued-grant set stands for `network.contains(Grant { .. })`, its roster for
`nodes.contains(..)`, an open connection for `live.contains(..)` — and the
module docs of `proofs::refinement` tabulate which part of the service
discharges each one.

The grant coupling is the one a server can *break*, and one did. `granted` is
an **input** to the verified acquire step, so the registry's set has to hold
every grant the model's network would — and **four** transitions publish one,
not just the poll: `tr_complete_release`, `tr_revoke_owner`,
`tr_reassign_unowned` and `tr_abort_transfer` each offer the actor on as part of
moving it. A registry that recorded only the poll's grant was applying the
refusal theorem under a hypothesis that did not hold, which is worth nothing at
all. The visible symptom was much smaller than the real one: a node that took
the actor without polling first was refused, although the model had already
published its grant.

**Status.** The service is pinned to the Jetstream working tree rather than to a
release — `16.3.1` is not on crates.io, which the dependency resolution caught.
Its dependency graph resolves, but the environment it was written in cannot
reach crates.io's tarballs, so **CI is the first place it is compiled**. That is
the same footing the fuzz target was on when it was added, and it is stated here
rather than discovered.

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

## Network resiliency: the model, run for real

Everything above is a claim about a transition relation. It says nothing about
whether an implementation follows it, and the gap has always been listed under
future work. `tests/` closes part of it by simulation rather than by proof.

Under [turmoil](https://github.com/tokio-rs/turmoil) — a deterministic,
seeded, simulated network with a simulated clock — an *executable* ownership
protocol runs over real sockets: a coordinator holding the registry, and three
nodes polling, acquiring, writing and releasing. Partitions, delays and
reordering happen underneath it while the model's own theorems are checked as
runtime oracles over the coordinator's audit log:

| Oracle | The claim it comes from |
| --- | --- |
| two accepted writes at the same epoch came from the same node | claim 1, exclusive mutable ownership |
| every burn strictly increases the epoch, and never below the high-water mark | claim 5, epoch monotonicity |
| an epoch is acquired once, by the node it was offered to | P5 / P6, ownership at an epoch is final |
| a handover goes to another node; its stand-down order and its release both name the node it is taking the actor from | claim 4, transfer safety |
| no write below a burned epoch is ever accepted | claims 2 / 3, stale-owner fencing |
| every acquire is by the node the registry offered the actor to, at an epoch it was actually offered | P8 at the grant, no authority without a capability |
| every accepted write is backed by an earlier acquire of that exact `(node, epoch)` | P8 at the token, no authority without a capability |
| no write is *refused* while the registry's own log says that node holds that epoch | the definition of `may_mutate` — **not a theorem**, see below |

The last row is different in kind from the seven above it and is listed
separately for that reason. Every theorem in this repository has the form
"this cannot happen": none of them says a write is ever *accepted*, and none
could — that is liveness, and it is not what the proofs are about. The
consequence is a hole with a definite shape. A coordinator whose `WRITE` arm
answered `FENCED` unconditionally satisfies all seven oracles above, because
each is a claim about writes that got through and there would not be any. So
the eighth checks the other direction of `may_mutate`'s definition — the
registry accepts exactly when the actor is `Owned` by that node at that epoch,
so a refusal aimed at the current owner is a state the model does not have.
It is derived from a definition rather than from a proof, which is weaker
provenance than the rest of the table, and it is the reason the table has a
row the "claim it comes from" column cannot fill honestly.

### The search over what arrives, not over what a correct node sends

The largest category of defect this suite found was a guard the search
*structurally could not reach*. `Action::from_pair` emits only well-formed
requests, and a named story drives the same node agent, which sends what a
correct node would send — so a guard against a handover to the sender itself,
a release from the node receiving the actor, or a line that does not parse is
invisible to the scenario walk however long it counts. Not "not yet found":
unreachable. Six of them were written by hand, one test each, after a reviewer
pointed at each in turn.

`tests/protocol_lines.rs` makes the malformed request something the search
produces rather than something somebody remembered. It generates a connection
and a line — well formed, corrupted, or arbitrary bytes — and drives the
registry directly, asserting that **no sequence of arbitrary lines from
arbitrary peers can drive it into a state whose audit log the oracles reject**.
That is the property each of those six tests checks a single instance of.

Getting it to reach anything took four rounds of measurement, and the numbers
are worth keeping because they are what a generator looks like when it is
lying to you:

| | requests served | acquires | writes | handovers completed |
| --- | --- | --- | --- | --- |
| first version | 122 | 15 | 0 | 0 |
| node/epoch fields split | 1 387 | 31 | 4 | 0 |
| verbs weighted, runs longer | 1 531 | 102 | 31 | 0 |
| generator echoes what it was told | 2 934 | 370 | 265 | 5 |

Every version passed the oracles. The first one passed them while reaching no
write at all — it was refused at the parser 17 871 times out of 17 993 and
would have looked like diligence. What caught it was a vacuity floor on
requests that got *through*, and what caught the three after it was a floor on
writes specifically, since polls alone satisfy the first floor while the run
never gets as far as holding the actor.

The last change is the one to understand. A generator that could not echo the
epoch it was just granted could not reach a write, because reaching one means
quoting an epoch something else has usually just burned — so a minority of
fields are filled from the registry's last reply rather than from a table.
That is what a node knows, not what the registry knows: giving the generator
the actual state would make it emit only requests that succeed, which is the
action alphabet again.

**The floors are on what the generator produced, not on what came back.**
The first version of this walk floored *refusals*, on the reasoning that a
refusal is evidence of malformed input. It is not. `NONE`, `NO` and `FENCED`
are ordinary answers to well-formed, authenticated requests — a poll when the
actor is held, an acquire that was never offered, a write at a burned epoch.
Deleting every malformed generation mode and leaving only `well_formed` left
this walk green with a *higher* refusal count than before, over more served
requests. The check written specifically to stop a check from saying nothing
was itself saying nothing. Each mode is now counted where it is built, and
deleting any one of them takes its count to zero and fails. The limit of that
is worth stating: the counters measure the *label* a step was generated under,
so they catch a mode being removed and would not catch one hollowed out while
keeping its label.

**The oracles cannot see a request, only a log.** They audit what the registry
*did*, and a request that should have been refused and was executed instead
leaves a perfectly legal log — it is a thing the registry is allowed to do, done
for the wrong reason. So each step also carries an obligation, decided from the
line and the connection alone: an unknown verb, the wrong field count, a field
that is not a `u64`, or a `FORCE` off the control path must be refused *in every
state*. Only unconditional refusals belong there; whether `ACQUIRE 0 41` should
succeed depends on the registry's state and is the oracles' business.

That obligation is the only thing in this walk that catches the parser defect
`filter_map` was. It needed one generation mode to reach it. Every other
corruption here changes the field *count*, which even the lenient parser
rejected by accident; the shape that parser turned back into a valid request is
a **surplus** non-number, inserted rather than substituted — `POLL junk 0`
arriving as `POLL 0`, right arity, executed. Measured both ways: with that mode
deleted and the parser regressed, 20 000 seeds stay green; with it present, the
walk fails on seed 0.

**A refusal also has to be in the words that request uses.** The reply check
started as a flat set of the protocol's tokens, which accepts any of them for
any request — and a wrong-vocabulary refusal leaves the log *unchanged*, which
is exactly what a refusal is supposed to leave behind, so no log-reading oracle
can see it. Measured: with a refused `RELEASE` answered `FENCED`, and again
with a refused `ACQUIRE` answered `NONE`, this search passed 20 000 seeds
apiece while the registry spoke a protocol no node parses. The vocabulary is
now per verb, read off what each request *asks* rather than off the handler's
branches: a poll is answered with a grant, a revocation or nothing; a write
either lands carrying the sequence number it landed at or is stopped by the
fence; everything else takes effect or does not. `NO` and `ERR` stay universal,
because *when* a refusal is owed is the obligation's business, not the
vocabulary's. **An unwarranted refusal is a separate question, and I got it wrong once.** A
refusal moves no state and writes no log entry, and I concluded from that that
no such refusal is judged anywhere — liveness, out of scope. That is wrong.
`may_mutate (refusals)` judges exactly this for writes: a registry that refuses
its own current owner, which is what `oracles_catch_an_overfencing_coordinator`
exists for. The real distinction is not safety against liveness but **logged
against unlogged** — that oracle fires on `Event::Fenced`, so the same refusal
spelled `NO` or `ERR` walks straight past it, and the aggregate floors are no
help against a defect that is selective rather than total.

Which generalises, and the general form is the useful part:

> Any correct behaviour whose absence leaves the log unchanged is invisible to
> an oracle that reads the log.

So the same hole existed in every transition, not just the write. Measured, one
legitimate request in three refused with an unlogged `NO`, before the check
existed — each of these passed **20 000 seeds, over half a million requests**,
with every floor satisfied:

| refused transition | seeds survived | now fails in |
| --- | --- | --- |
| `WRITE` — the current owner's write | 20 000 | 0.07s |
| `ACQUIRE` — the intended owner taking an issued grant | 20 000 | 0.07s |
| `BEGIN` — the owner agreeing to hand over | 20 000 | 0.07s |
| `RELEASE` — the outgoing owner acknowledging | 20 000 | 0.09s |
| `FORCE` — a forced revoke naming a node that exists | 20 000 | 0.08s |

`Standing` reconstructs the registry's state from the audit log and answers
whether the model permits a request. It is the same reconstruction
`may_mutate (refusals)` was already doing for one question, made whole and
shared with it rather than copied. After the check, 200 000 seeds pass with
counts *identical* to before it — so it rejects nothing legitimate.

**And the dual of it, which that fix was missing.** The check above catches a
registry that *does nothing and says no*. It says nothing about one that **says
yes and does nothing** — an `ACQUIRE` answered `OK` with no acquire logged, a
`POLL` answered `GRANT 41` with no grant issued. An unchanged log is a
perfectly *valid* log, so no oracle handed the finished run can see it, and
each of those passed 20 000 seeds.

Together the two halves say the whole thing:

> **The reply and the log must agree.** Every reply names a transition or names
> none, and the events the step appended have to be exactly that.

That correspondence can only be checked *during* the run. An oracle handed a
finished log cannot tell which entry belongs to which request — which is
precisely the information a lie about success destroys. Five lies are checked
both ways, including a write's `OK` carrying a sequence number one off from the
one it landed at. It costs about eighteen per cent more wall clock, which is
the only reason to mention it.

**Provenance, stated because it is weaker than most of this file.** No Verus
theorem says any request is ever accepted; the proofs are all of the form "this
cannot happen", and liveness is not what they are about. `may_mutate
(refusals)` already crossed that line deliberately, for writes, and this
extends the same argument to the other transitions. It inherits the same weaker
provenance rather than pretending otherwise.

What is genuinely out of scope is a good `POLL` answered `NO`. `tr_issue_grant`
being *enabled* is not the model requiring it to fire, and `NONE` answers any
poll, so a registry that refused every one would satisfy every oracle here.

Writing that obligation down went wrong three times, the same way each time,
and none of the three was caught by reading it. The two refusal reasons are independent, so
every one that *can* be established has to be: an obligation that drops a reason
it could have known demands one exact refusal where two are defensible, and then
reports a sound registry as defective for choosing the other. `FORCE 41.0` from
a node is both unparseable and unauthorised, and deciding the fields first
demanded `ERR` from a registry that refuses strangers before parsing their input
— which is the better order, not a fault. Fixing that for `FORCE` and stopping
there was one case short of the rule: `WRITE 0 junk` on the control connection
is the same shape, because the *sender* field is legible even though the epoch
is not. Fixing that for the *sender* field and stopping there was one field short
again: `BEGIN junk 99` names a successor that does not exist and `FORCE 99
junk` does too, and an all-or-nothing parse let one illegible field hide what
the legible ones carried. Three catches of one mistake, each a field further
out, so it is written down as the rule instead of as a third case: **a
permission check uses its own field's parse result, never the whole line's.**
Authority is decided from whatever is legible, before the line is judged well
formed at all, and the tests pin it in both directions — relaxing an obligation
is only safe while the strict cases stay strict.

**Still thin.** Completed handovers are reached 5 times in 1 024 runs, so
claim 4 is barely exercised here — it is covered by the scenario walk and the
named stories instead. That count is reported and deliberately not asserted
on: a floor on a rate that low would be a flaky test rather than an
informative one.

CI walks 100 000 of these seeds — 2.7 million requests in twelve seconds,
against forty-six for the 256 simulated scenarios in the same job. The window is fixed so
a red result means the change did it; `JETSTREAM_PROTOCOL_START` moves it. The
default stays at 1 024 so a contributor's `cargo test` is instant.

`fuzz/` is the coverage-guided front end to the same generator, registry and
oracles, run for a minute on every pull request, and is the arm that explores
somewhere new on every run. It needs nightly, so it is
its own workspace and its own job; the pinned stable toolchain the proofs are
built with is never in question for it.

Two searches reach them. `turmoil_ownership.rs` holds named stories, each of
which asserts what it was supposed to *reach* — the headline one is A owning
the actor at epoch 41, being cut off, the coordinator handing the actor to B at
42, and A returning still holding a guard that says yes.
`turmoil_scenarios.rs` counts seeds upwards, generating action sequences it has
no opinion about, and replays every seed in `tests/seeds/scenarios.txt` first so
a fixed bug stays fixed. Both drive the same runner and the same oracles.
`Scenario::from_bytes` is the entry point a coverage-guided fuzzer would use to
drive that same runner; the fuzz target that exists drives the protocol-line
generator instead, for the reason given above — the action alphabet cannot
express the inputs most of these guards are about.

**What this is evidence of.** A divergence is one of two things: an
implementation that does not follow the protocol, or a protocol whose proof
rests on something the network does not give you. Both are findings. What it is
*not* is a check on the proofs — those are static, and no simulation can
contradict them. It is also not a substitute for a refinement: the coordinator
*in `tests/`* is hand-written to match the model and nothing machine-checks that
it does — which is exactly the gap `src/steps.rs` closes for the Jetstream
service in `services/ownership/`, and the reason the two coordinators are worth
keeping side by side.

**Would the oracles notice?** A suite that cannot fail is indistinguishable
from one that passes, so `oracles_catch_an_unfenced_coordinator` runs one story
twice with a single bit changed — the coordinator stops checking writes against
the registry — and requires the oracles to *reject* the second run. Same
actions, same seed, same network, same oracles; what separates them is exactly
the check `src/exec.rs` says has to happen where the effect lands.
`oracles_catch_a_write_at_a_burned_epoch` does the same for the fencing oracle,
on the case the others cannot see: a stale write with nothing written after it.
`oracles_catch_an_overfencing_coordinator` is the mirror of the first: the same
story again with the fence jammed *on* rather than off, which is the failure
none of the seven proof-derived oracles can see, and which the eighth exists
for. The write floor in the seed walk catches the totally degenerate version of
it by counting accepted writes across the window, but a registry that fenced
only one node, or one request in three, clears that floor comfortably.

Beyond those two, **every oracle in the table has a witness**: a hand-built log
that it, and not one of its neighbours, rejects — paired where it matters with
a nearly identical log it accepts, so a check cannot pass by rejecting
everything. The logs are hand-built on purpose. Several are ones this
coordinator cannot produce, and that is the point: an oracle which is sound
only because the thing it audits is correct is not auditing anything. Writing
those witnesses is what found most of the defects in this table: of the six
oracles that existed when the audit started, three were checking something
weaker than the theorem they named, and one of those was checking the wrong
thing entirely — the P5/P6 oracle read
write epochs, which is a *consequence* of "an epoch determines its owner"
rather than the claim, and accepted an epoch changing hands with nothing burned
between.

That second one exists because the first version of `check_invariants` did not
catch it. Comparing writes against writes notices a stale write only once the
replacement owner has written too, so `Acquire(0)@41, Force→42, Write(0)@41`
had one writer per epoch, a strictly increasing burn and an acquire behind
every write — and sailed past every check, which is precisely the failure the
epoch exists to prevent. A burn is what makes an epoch stale, so a burn is what
the high-water mark has to follow.

**Where the executable code lives, and why.** Entirely in `tests/`. CI greps
`src/` for `verifier::external`, so unverified protocol code there would need
that attribute and would fail the build by design. The one piece of `src/` the
simulation uses is `FenceGuard`, because it is the node-local check a real node
performs — and watching a stale guard say yes while the coordinator says no is
precisely the asymmetry `src/exec.rs` documents.

Where the model makes a node act, the simulation makes that node send the
request. `tr_begin_transfer` carries `pre.live.contains(from)` — agreeing to
hand over is an action *by* the owner — so `BEGIN` originates at the owner's
host and names itself, and the registry checks the sender. A partitioned
owner's agreement is swallowed by the partition, which is what that liveness
guard means here. Routing it through the driver instead would let a node nobody
can reach volunteer, reopening in the simulation the exact hole the guard was
added to the model to close.

For the same reason, the three ways the coordinator forces progress are kept
distinct rather than merged: `tr_revoke_owner` from `Owned`,
`tr_reassign_unowned` from `Unowned`, and `tr_abort_transfer` from
`Transferring`. Only the first two take a successor from the caller; an aborted
transfer returns the actor to the node it was being taken from, and a
coordinator that redirected it anywhere else would be stepping outside the
transition relation.

**One place where the simulator is kinder than a network.** turmoil knows
whether a route exists, so a request made across a partition that is already in
place fails immediately at the sender. A real partition drops the packet and
the sender learns nothing until its own deadline expires. The node-side counters
keep the two apart — `writes_failed` against `writes_timed_out` — and the seed
walk prints both, so the difference is visible rather than assumed.

Printing them is how the gap was found. A run reported 284 writes sent across
256 seeds with **zero** unanswered at the deadline: every failure was a removed
route, so the node's deadline had never once fired and the scenarios contained
no request that was accepted for delivery and then ignored. Since "duplicate,
reordered and arbitrarily delayed requests are safe" is one of the claims in the
table above, a search that could not produce a delayed request was not reaching
it. `Stall` and `Resume` use turmoil's `hold`/`release` to do exactly that.

Three stories then split the case apart, because one story could not carry it.
`a_held_request_expires_and_the_node_carries_on` shows the node giving up and
going on working. That alone is satisfied by a run in which nothing is ever
delivered late, so
`a_delayed_write_arrives_at_a_registry_that_moved_on` releases the hold while
the node is still waiting: the write is delivered into a registry that burned
its epoch meanwhile, and is fenced on arrival, which is the claim itself. And
`a_timeout_is_not_evidence_the_write_did_not_land` covers the direction no
network behaviour produces — the registry applies the write and answers after
the caller has given up, so a node that read its own timeout as a verdict would
be wrong about a write that had already landed. It costs
nothing here only because nothing in the protocol reads them: a node that
distinguished "no route" from "no reply" would hold information a real one does
not, and treating either as a decision about ownership is exactly the mistake
the fence exists to make unnecessary.

Two places where the simulation is deliberately coarser than what was proved,
stated rather than glossed:

* `tr_handle_revoke` and `tr_complete_release` are folded into one `RELEASE`
  request, so the simulation never occupies the intermediate state the model
  distinguishes;
* the registry is a `Mutex`, which is the executable form of the model's
  load-bearing assumption that ownership records are updated atomically. A
  deployment buys that from consensus or a compare-and-swap store. Saying so is
  the point: the assumption is visible rather than smuggled in.

```bash
cargo test --test turmoil_ownership -- --nocapture   # the named stories
cargo test --test turmoil_scenarios -- --nocapture   # the seed search

# search further: a moving, non-overlapping window
JETSTREAM_SCENARIO_START=100000 JETSTREAM_SCENARIO_SEEDS=20000 \
  cargo test --test turmoil_scenarios --release
```

A third CI job runs both on every pull request. It needs no Verus toolchain:
ordinary `rustc` erases the ghost code in `verus!` and leaves `FenceGuard`
behind.

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
* ~~Raymond's holder pointers have a unique root but are not proven acyclic~~ —
  both halves of that were wrong by the time it was written, in opposite
  directions. **Acyclicity is proved**: `ray_acyclic` is part of `ray_inv` and
  every transition preserves it (R11). And the pointers do **not** have a unique
  root: after `SeizeToken(A, B)` both `holder[A] == A` and `holder[B] == B`, and
  that is deliberate — `A` is a stale holder whose belief nobody could reach in
  to correct. Uniqueness belongs to `Raymond::privilege`, the authoritative
  field, not to the belief graph.

  So the unconditional guarantee is an **acyclic forest of beliefs** plus a
  single authoritative holder. Reaching that holder by following pointers (R12)
  needs `ray_no_stale_holders` on top, which is exactly what reconciliation
  restores. Routing termination would need the liveness the model does not
  claim.

**Not modelled at all** (a gap, stated rather than papered over):

* **Raymond itself has no crash model.** The ownership layer models crash,
  recovery and unreliable failure detection; Raymond's own steps do not. A
  Raymond in which nobody holds the privilege is not reachable, because
  `Raymond::privilege` always names a node and `ray_wf` keeps it inside
  `nodes` — which is now structural rather than an inductive invariant.

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
* **done, for the registry's transitions**: the refinement from the `nat`-valued
  model to an executable `u64` implementation, with the epoch-exhaustion case
  handled, is `src/steps.rs` and `src/proofs/refinement.rs` — see rows E1 to E6.
  What remains unrefined is the *node* side: `src/exec.rs` still offers no way
  to advance a node's fence guard, only to consult it, so that no executable API
  can perform a handover the model does not;
* the actual actor runtime: networking, persistence, and the code that obeys the
  protocol. Verifying the protocol says nothing about whether an implementation
  follows it. `tests/` now exercises a hand-written one against the model's own
  theorems on a simulated network (see
  [Network resiliency](#network-resiliency-the-model-run-for-real)), which is
  evidence rather than proof: nothing machine-checks that the coordinator in
  `tests/` refines the transition relation in `src/`.

### The holder graph is a tree, and now says so

`ray_unique_token` and `ray_token_exists` together say there is exactly one
root. That is not the same as the holder graph being a tree: nothing stopped a
set of non-root nodes from pointing at each other in a cycle, off to one side of
the real root. `ray_init` permitted it too — it forbids only a non-root pointing
at *itself*, so `A → B`, `B → A` beside a root `C → C` satisfied it.

The consequence was visible in `src/raymond.rs`'s own opening comment: "requests
travel hop-by-hop towards the token" is false for a node inside such a cycle,
whose request would circle for ever. Nothing in the safety proofs depended on the
claim, which is exactly why it went unchecked for eight review rounds.

`ray_acyclic` is now part of both `ray_inv` and `ray_init`, stated as the
existence of a rank — a `nat` per node that strictly decreases along every
non-root edge, which is well-foundedness and so admits no cycle. The existential
is the form the proofs want, because a step preserves acyclicity by *exhibiting*
a new rank. For both token movers that rank is the old one shifted up by one with
the new root sent to zero, and `lemma_repoint_acyclic` proves it once for both:
they rewrite exactly the same two pointers, and neither the old token position
nor any parent-child relationship between the two nodes is needed.

`theorem_every_node_reaches_the_token` is the payoff, by induction on the rank.
It is still a safety property — the route exists in the current state — and not
liveness, which would need the assumptions listed above.

### Scenarios export labelled runs, not endpoints

The recurring defect on this PR was a scenario whose postcondition described the
world afterwards but never how it got there — and "how it got there" is the
entire content of a scenario. The repair went through three stages, and only the
third one holds:

1. **`ensures true`** — a scenario that proved nothing.
2. **An exported *step*** — better, but a step and an endpoint exported as
   independent existentials can come from different executions.
3. **A reachability-*from* relation** tying them together — better still, and
   still not enough: `composed_reachable_from(c, d)` says *some* run joins `c`
   to `d`, but which steps that run took is hidden inside `composed_next`'s
   existential. Every scenario built this way turned out to be satisfiable by a
   substitute execution, and each repair excluded only the one substitute that
   had been found:

   | Scenario | Substitute execution that satisfied it |
   | --- | --- |
   | crash takeover | `Acquire(A@41) → BeginTransfer → HandleRevoke → CompleteRelease → Crash(A) → SeizeToken → Acquire(B@42)` — `A` gave the actor up *voluntarily*, and no `RevokeOwner` occurred at all |
   | voluntary handover | an unrelated `A → B` transfer at epochs 39 → 40, then `Acquire(A@41)`, then `RevokeOwner` to reach `B@42` — the advertised 41 → 42 release never happened |
   | request routing | `A`, `B` and `D` each call `RequestCs` independently and then serve their own queue heads — `D`'s request is never forwarded `B → A → C` |

4. **The labelled run.** `composed_run(tr, labels)` and `ray_run(tr, labels)`
   carry the step labels alongside the states, and a scenario exports the whole
   object. Fixing every entry of `labels` says exactly which steps the run
   consists of and in what order, so no other run can satisfy it — not because
   each alternative was anticipated and ruled out, but because nothing is left
   free to vary.

`lemma_composed_labelled_execution_is_execution` and `lemma_ray_run_is_segment`
show the labelled forms imply the unlabelled ones, so every theorem stated over
`composed_reachable` still applies; the scenarios only got stronger.

What labels do **not** carry is data the step takes from the state it fires in.
`ComposedStep::Own { own_step: Step::BeginTransfer { actor, from, to } }` names
no epochs, so the handover's label sequence alone is satisfied by a 39 → 40
transfer. The scenario therefore also exports the `Transferring` state *at the
index it occupies*:

| Scenario | Exported run |
| --- | --- |
| `scenario_composed_crash_takeover` | 8 labels, `Crash(A)` at index 2 and `RevokeOwner` at index 3, with no `CompleteRelease` anywhere for a voluntary release to hide behind; plus `tr[4]` showing `A` crashed, epoch burned and still holding the token |
| `scenario_composed_handover` | `labels == handover_labels(x, a, b)` — 10 steps — plus `tr[3]` pinned to `Transferring { a, b, 41, 42 }` |
| `scenario_request_and_token_routing` | `labels == routing_labels(a, b, c, d)` — 12 steps — plus `tr[0] == routing_init_state(a, b, c, d)`. One `RequestCs` in the whole run and it is `D`'s, so `MakeRequest { node: b }` at index 3 can only fire because `ReceiveRequest { at: b, from: d }` at index 2 filled `B`'s queue |
| `scenario_composed_critical_section` | 3 labels, `RequestCs` / `EnterCs` / `ExitCs`, with `using` false at 0, 1 and 3 and true at 2 |
| `scenario_stale_owner_returns` (the headline) | 9 labels — `Crash(A)` at 5 between the release and `B`'s acquisition, `Recover(A)` at 7, the replay of `A`'s epoch-41 grant at 8 — plus the `Owned(A, 41)` and `Transferring` states at indices 2 and 3 |
| `scenario_interrupted_transfer` | 4 labels, the `AbortTransfer` at 3 interrupting the `BeginTransfer` at 2 |

The phases that keep these proofs tractable thread the run rather than an
anchor: each takes the run built so far, appends its own steps with their
labels, and hands the whole thing on, so splitting a scenario for the solver's
benefit costs nothing in what the scenario claims.

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

**What that audit is and is not.** It is manual inspection plus the absence of
resource-limit blowups; it is not a check anything enforces, and the distinction
matters because nothing would fail if a future quantifier reintroduced a loop
until it happened to exhaust a budget. Of the 176 quantifiers in `src/`, 151
carry an explicit `#[trigger]` or `#![trigger …]`; the remaining 25 rely on
Verus's inference, and are the ones where the inferred trigger is a single
application term with nothing to regenerate (`exists|s| step(pre, post, s)` and
the like). CI additionally passes `--triggers-mode silent`, which suppresses the
notes Verus would otherwise print about automatically chosen triggers — good for
signal-to-noise in the log, and worth knowing before treating the build's
silence as evidence about triggers. It is not.

CI greps `src/` for the real escape hatches and fails the build if any appear.
Everything the proofs rely on that is not derived is a modelled transition or an
explicitly documented entry in the failure-model table above.
