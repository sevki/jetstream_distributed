# Ownership: the model and its claims

## What this is, and what it is not

This repository does **not** claim that Rust's borrow checker has been extended
across machines. Nothing here is checked at compile time for your application
code, no lifetime crosses a network link, and no `&mut` is transported anywhere.

What this is: a **runtime protocol** for moving exclusive write authority over
an actor (named by an `Id`) between nodes, together with **machine-checked proofs** that the
protocol's exclusivity and fencing properties hold in every reachable state,
including under crashes, partitions, duplicated messages and interrupted
handovers.

The analogy to Rust is about the *shape* of the guarantee, not the mechanism.
Rust's `&mut T` is exclusive because the compiler refuses to create a second
one. Here, authority is exclusive because `may_mutate` is only ever true in one
shape - the actor is `Owned`, the caller is the owner, and the caller's fencing
epoch is exactly the actor's current epoch - and because the protocol's
transitions provably keep it that way.

The core of this repository is a *model*, and the proofs are about the model.
Each algorithm also has a service over Jetstream RPC, which runs the verified step
functions; what those services do and do not claim is stated in
[The protocol as a Jetstream service](services.md#the-protocol-as-a-jetstream-service) and
in each module's docs.

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
can do; see [The holder graph is a tree](status.md#the-holder-graph-is-a-tree-and-now-says-so)
and the `believes_holds` / `has_token` split in `src/raymond/model_t.rs`.

**What Chubby has that this does not**: a deployed system, sessions and
KeepAlives, failover, caching with invalidations, a filesystem namespace, ACLs,
events, and liveness of any kind. This model proves safety only, and says so.

## The state machine

```rust
// Id is `crate::id::Id`, a newtype around a `u128` (a UUID or a ULID converts to one);
// a model names a host, and an actor, by it directly. (An actor was a `nat` here
// before; the theorems now quantify over the `u128` actors a host always was, not
// over unbounded ones. No theorem relied on there being more.)
pub type Epoch   = nat;

pub enum OwnershipState {
    Owned        { owner: Id, epoch: Epoch },
    Transferring { from: Id, to: Id, old_epoch: Epoch, new_epoch: Epoch },
    Unowned      { epoch: Epoch, intended_owner: Id },
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
spec fn may_mutate(s: OwnershipState, node: Id, epoch: Epoch) -> bool {
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
| 1 | **Exclusive mutable ownership** - in any reachable state, if `A` and `B` may both mutate an actor then `A == B` (and their epochs are equal) | `ownership::proofs::exclusivity::theorem_exclusive_mutable_ownership` | reachability; none beyond the model |
| 1a | The same, structurally: no state at all, reachable or not, admits two mutable owners | `ownership::proofs::exclusivity::theorem_exclusive_mutable_ownership_structural` | none |
| 1b | Two capability tokens that both confer authority over the same actor are the same token | `ownership::proofs::exclusivity::theorem_authorized_token_unique` | reachability |
| 2 | **Unique current epoch** - existence stated outright, and uniqueness as an implication over *arbitrary* epochs (not under the assumption that a witness was already supplied) | `ownership::proofs::fencing::theorem_unique_current_epoch` | none |
| 3 | **Stale-owner fencing** - `current_epoch(actor) > supplied_epoch ==> !can_mutate(actor, node, supplied_epoch)` | `ownership::proofs::fencing::theorem_stale_epoch_cannot_mutate` | none |
| 3a | Advancing `n -> n+1` strips authority from every holder of `n` | `ownership::proofs::fencing::theorem_epoch_advance_fences_previous` | none |
| 3b | For issued tokens the fence check is exactly epoch equality (no token is ever ahead of the actor) | `ownership::proofs::fencing::theorem_fence_is_exact_for_issued_tokens` | reachability |
| 4 | **Transfer safety** - every permitted transition preserves the ownership and fencing invariants | `ownership::proofs::transfer::theorem_transition_preserves_invariants` | `inv` holds before the step |
| 4a | Across a whole handover, the epoch never decreases, nobody has authority at the middle stages, and the outgoing owner is fenced from the first transition onwards | `ownership::proofs::transfer::theorem_handover_safety` | `A != B` |
| 4b | At no stage of a handover can both nodes have authority | `ownership::proofs::transfer::theorem_handover_never_both` | `A != B` |
| 4c | An interrupted handover fences both the old and the abandoned new epoch | `ownership::proofs::transfer::theorem_interrupted_transfer_fences_both` | none |
| 4d | Ownership cannot be manufactured: the only step that can make `may_mutate` true is `Acquire`, from `Unowned` at that exact epoch with a matching grant | `ownership::proofs::transfer::theorem_ownership_only_via_acquire` | none |
| 5 | **Epoch monotonicity** - no transition decreases an actor's epoch | `ownership::proofs::fencing::theorem_epoch_monotone_step`, `..._next`, `..._execution` | none |
| 6 | **Token uniqueness (authority)** - at most one token confers authority per `(actor, Epoch)`, an actor being an `Id` | `ownership::proofs::tokens::theorem_valid_token_unique_per_actor_epoch` | none |
| 6a | **Token uniqueness (physical)** - at most one token is ever *issued* per `(actor, Epoch)` | `ownership::proofs::tokens::theorem_issued_token_unique_per_actor_epoch` | reachability |
| 6b | Stale physical tokens confer no authority | `ownership::proofs::tokens::theorem_stale_token_has_no_authority` | none |
| 6c | No token is ever minted for a future epoch | `ownership::proofs::tokens::theorem_no_future_tokens` | reachability |
| E | The runtime `u64` check returns exactly the model's verdict **for the generation the guard records**, and rejects any epoch superseded *within that record* | `ownership::exec::FenceGuard::accepts`, `ownership::exec::FenceGuard::rejects_stale` | the guard is the node's own belief, immutable after `FenceGuard::new`. **This is node-local staleness rejection, not fencing**: a partitioned `A` still holding `FenceGuard::new(A, 41)` accepts `(A, 41)` while the system is at `Owned { B, 42 }`. A node cannot fence itself — see below |
| E1 | **Acquire refines `tr_acquire`** — when the step fires the model fires, to exactly the record the step computed; when it refuses a request naming the actor's current epoch, *no* post state satisfies `tr_acquire`; and however the model acquires, the record it lands on is the one the step computes | `ownership::proofs::refinement::theorem_acquire_step_refines_tr_acquire`, `..._refuses_exactly_when_disabled`, `..._outcome_is_the_step` | the couplings (see the module docs of `ownership::proofs::refinement`); the refusal direction additionally assumes the request named the current epoch, which is the one place the executable step is narrower than the model |
| E2 | **Begin-transfer refines `tr_begin_transfer`**, in the same three parts. Refusal is exactly disablement *or* epoch exhaustion, and the refusal says which | `ownership::proofs::refinement::theorem_begin_transfer_step_refines_tr_begin_transfer`, `..._refuses_exactly_when_disabled`, `..._outcome_is_the_step` | the couplings; `u64` exhaustion is the implementation's, not the model's |
| E3 | **Release refines `tr_handle_revoke` followed by `tr_complete_release`** — two model transitions, one method, with the middle state exhibited rather than assumed to exist. A refused release is provably not the handover the model would complete | `ownership::proofs::refinement::theorem_release_step_refines_handle_revoke_then_complete_release`, `theorem_refused_release_is_not_the_models_release` | the couplings, and that the `Revoke` being acknowledged is on the network — which `tr_begin_transfer` put there |
| E4 | **Forced revocation refines all three of its transitions**: `tr_revoke_owner` from `Owned`, `tr_reassign_unowned` from `Unowned`, `tr_abort_transfer` from `Transferring` — and in the last case the actor provably goes back to the node the transfer came from, whatever successor the coordinator named | `ownership::proofs::refinement::theorem_force_step_refines_tr_revoke_owner`, `..._tr_reassign_unowned`, `..._tr_abort_transfer` | the roster answers `pre.nodes.contains(next)` |
| E5 | **A poll is `tr_issue_grant` or the delivery of a `Revoke`**, and the epoch it offers is the actor's current one — so a poll can never hand out a generation the registry has already left. `Nothing` is returned only to a node that is owed nothing | `ownership::proofs::refinement::theorem_poll_step_refines_tr_issue_grant`, `..._tr_handle_revoke`, `theorem_poll_step_offers_nothing_only_when_nothing_is_owed` | the couplings |
| E6 | **The registry's fence is the *system's* fence** — `may_write_step` on the registry's own record is `can_mutate`, not a node's belief about it. Same postcondition as E, different thing, bought entirely by where it is called | `ownership::steps::may_write_step`, `ownership::proofs::refinement::theorem_may_write_step_is_the_system_fence` | the record the step is handed is the actor's |
| E7 | **The refinement theorems are not vacuous.** Each is an implication under hypotheses, and hypotheses that cannot all hold make a theorem true and empty — a refinement suite can be green and say nothing. So one concrete system is written out in full and a whole handover walked through it, each theorem applied to the state the previous one produced, with what came out asserted | `ownership::proofs::refinement::scenario_a_handover_through_the_verified_steps` | none: the system is exhibited |
| E7a | The same for the *refusal* theorems, whose hypotheses are the negation of a guard and so are untouched by a run in which the guard holds. In a system where no grant was published, **no** post state satisfies `tr_acquire` — quantified over all of them, not over one the server had in mind | `ownership::proofs::refinement::scenario_the_refusals_are_refusals_of_something_real` | none |
| E8 | **The registry's record is the model, grants included.** `registry::RegistryCore` — the actor's record, the grants published and the writes landed — takes the model's step at every method: `poll` is `tr_issue_grant` and publishes the grant it answers with; `acquire` is `tr_acquire` and reads the grant from the published set; `begin_transfer` is `tr_begin_transfer`; `release` is `tr_handle_revoke` then `tr_complete_release` and publishes the grant that completes the handover; `force` is `tr_revoke_owner`, `tr_reassign_unowned` or `tr_abort_transfer` by state, and publishes the grant it offers the actor on with. The relation (`stands_for`) is an equality between the published set and the network's `Grant`s for that actor — the coupling E1's refusal theorem is worth nothing without, and the one a registry once broke | `ownership::proofs::registry::theorem_poll_is_issue_grant`, `theorem_acquire_is_tr_acquire`, `theorem_begin_transfer_is_tr_begin_transfer`, `theorem_release_is_handle_revoke_then_complete_release`, `theorem_force_from_owned_is_tr_revoke_owner`, `theorem_force_from_unowned_is_tr_reassign_unowned`, `theorem_force_from_transferring_is_tr_abort_transfer`, `theorem_a_landed_write_is_can_mutate` | the sender-side hypotheses E1–E6 already name (`live`, `nodes`), and for `release` the `Revoke` on the network, which `begin_transfer` put there |
| E9 | **A refused step is one the model could not take.** A refused `acquire` (for a request naming the actor's current epoch) and a refused `begin_transfer` are disabled in every post-state; a refusal changes nothing, publishes no grant and counts no write. A refusal that is the `u64` epoch running out is the one the model does not have, and says so | `ownership::proofs::registry::theorem_refused_acquire_is_disabled`, `theorem_refused_begin_transfer_is_disabled` and the `ensures` of each `RegistryCore` method | `stands_for` |
| P1 | **Issued tokens never disappear** — no crash, partition or recovery retracts a capability, which is why stale tokens must be fenced rather than revoked | `ownership::proofs::properties::theorem_issued_monotone` | none |
| P2 | **Sent messages never disappear** — the fact that makes duplication, reordering and unbounded delay free in the model | `ownership::proofs::properties::theorem_network_monotone` | none |
| P3 | **The actor population is constant** — no transition creates or destroys an actor | `ownership::proofs::properties::theorem_actor_domain_constant` | none |
| P4 | **An epoch advances by at most one per transition** — with claim 5, the epoch sequence is non-decreasing and never skips a generation | `ownership::proofs::properties::theorem_epoch_increases_by_at_most_one` | none |
| P5 | **Ownership at a given epoch is final** — once owned by `n` at `e`, every later state still at `e` is still owned by `n` at `e`; a handover *must* burn the epoch | `ownership::proofs::properties::theorem_ownership_at_an_epoch_is_final` | valid execution |
| P6 | **An epoch determines its owner** — any two points of an execution owned at the same epoch have the same owner | `ownership::proofs::properties::theorem_epoch_determines_owner` | valid execution |
| P7 | **Staleness is permanent** — a fenced-out node can never be fenced back in by waiting | `ownership::proofs::properties::theorem_stale_stays_stale` | valid execution |
| P8 | **No authority without a capability** — a node that may mutate provably holds an issued token for exactly that `(actor, epoch)` | `ownership::proofs::properties::theorem_no_authority_without_token` | reachability |
| P9 | **Epoch monotonicity survives composition** | `ownership::proofs::properties::theorem_composed_epoch_monotone` | none |
| R9 | **The privilege is never lost** — every Raymond transition leaves `privilege` pointing at a node | `raymond::proofs::routing_layer::lemma_ray_token_exists_init`, `lemma_ray_token_exists_step` | Raymond invariant |
| R10 | **Raymond critical sections are exclusive — while nobody's belief is stale.** The hypothesis is not a weakening; it is the algorithm's real scope. Raymond's mutual exclusion rests on every node agreeing where the privilege is, and a seizure breaks that until the seized node reconciles | `raymond::proofs::routing_layer::theorem_ray_critical_section_is_exclusive` | Raymond invariant, `ray_no_stale_holders` |
| R10a | **At most one node is *authorised* to be in its critical section**, with no side conditions: the authorised occupant is the privilege holder, and there is one of those by construction. This is the part of R10 that survives a seizure | `raymond::proofs::routing_layer::theorem_authorised_critical_section_is_exclusive` | Raymond invariant |
| R13 | **A stale holder confers no authority.** A node that believes it holds the privilege, does not, and may still be inside its critical section, still cannot mutate the actor — `couples` is written against possession, not belief. The routing counterpart of 6b, and what survives imperfect failure detection | `raymond::proofs::routing_layer::theorem_stale_holder_confers_no_authority` | the coupling |
| R14 | **Reconciliation repairs the belief**: the stale holder drops it, leaves the critical section it thought it was in, and re-points at the real holder | `raymond::proofs::routing_layer::lemma_reconcile_preserves_inv` | Raymond invariant |
| R11 | **The holder pointers are acyclic** — part of `ray_inv`, preserved by every transition. A handover rewrites two pointers and needs a new rank (the old one shifted up by one, new root at zero); a seizure only makes the new holder point at itself, which *removes* a constraint, so the old rank still works | `raymond::proofs::routing_layer::lemma_frame_acyclic`, `lemma_repoint_acyclic` | Raymond invariant |
| R12 | **Every node reaches the privilege holder by following holder pointers** — what makes "requests travel hop-by-hop towards the token" a checked claim. Two hypotheses, both load-bearing: R11 says the walk terminates rather than circling, and `ray_no_stale_holders` says it terminates at the real holder rather than at somebody who merely thinks so. The second was free when authority *was* belief; it is not free now, and it should not be — after a seizure a node whose belief-path leads to the seized holder genuinely cannot route to the privilege | `raymond::proofs::routing_layer::theorem_every_node_reaches_the_token` | Raymond invariant, `ray_no_stale_holders` |
| R15 | **The executable routing steps agree with the model, in both directions.** For each of `MakeRequest`, `ReceiveRequest`, `AssignPrivilege`, `EnterCs` and `ExitCs`: when the step fires the model's transition fires, to exactly the state computed; when it refuses, the model's transition is not enabled in *any* post-state. `AssignPrivilege`'s guard reads **both** `privilege == me` and `holder == me` — a step that read only the belief would let a stale holder pass a privilege it does not have — while `EnterCs`'s deliberately reads only the belief, as the model's does | `raymond::proofs::refinement::theorem_make_request_step_refines`, `theorem_receive_request_step_refines`, `theorem_assign_step_refines`, `theorem_enter_cs_step_refines`, `theorem_exit_cs_step_refines` and their `..._refuses_exactly_when_disabled` counterparts, `theorem_request_cs_post_is_the_model_step` | the couplings in the module's table: the scalars a step reads are the router's own table, read under its lock |
| R16 | **The routing record is the model.** `exec::RayTable` — every node's holder pointer, queue and flags, the requests sent, and where the privilege is — has a view that is a model `Raymond`, and each method's contract is the model's step: `request_cs`, `make_request`, `receive_request`, `assign_privilege`, `enter_cs` and `exit_cs` leave the view at the model's `*_post` with the model's transition enabled to it; `seize` and `reconcile` are the composed machine's two routing-side steps. The R15 theorems are applied to the live table inside each method, not assumed of it | `raymond::exec::RayTable::{request_cs, make_request, receive_request, assign_privilege, enter_cs, exit_cs, seize, reconcile}` (contracts), `lemma_update_entry`, `lemma_push_request`, `lemma_set_privilege` | the table is well formed (each node once; the privilege is at a node) |
| R17 | **A refusal is a step the model could not take, at any state.** Each of those methods, when it refuses, leaves the view unchanged and carries `forall post. !ray_*(old, post, ..)`: not "the code said no" but "no state is a legal result" — including for a node that is not on the roster, since every model step begins with `nodes.contains`. `assign_privilege` says it for *every* head, because with an empty queue none is named | the same contracts | the table is well formed |
| C1 | **Election Safety — at most one leader per term.** The headline. Three sentences: a leader won a majority; any two majorities share a member; a member votes once per term | `raft::proofs::election::theorem_election_safety`, `..._reachable` | the Raft invariant, discharged for reachable states by `theorem_reachable_raft_inv` |
| C2 | **Any two majorities of a cluster share a member.** The one piece of real mathematics, and the reason Raft needs no coordinator: two disjoint subsets whose sizes sum past the whole would make a union larger than a set containing it | `raft::proofs::election::lemma_quorums_intersect` | none |
| C3 | **A server votes at most once per term** — sentence three, and the clause `tr_grant_vote`'s guard exists to maintain | `raft::proofs::election::inv_votes_unique`, preserved by `lemma_raft_step_preserves_inv` | the Raft invariant |
| C4 | **A cast vote is never ahead of its voter's term.** Not in the headline argument and the clause without which it does not survive induction: it is what makes a fresh candidacy safe, because a server timing out into term `t + 1` can only be voting there for the first time | `raft::proofs::election::inv_vote_implies_term` | the Raft invariant |
| C5 | **The Raft invariant holds in every reachable state** (`raft_init ==> inv`, `inv /\ raft_next ==> inv`) | `raft::proofs::election::theorem_reachable_raft_inv` | the model's transition relation |
| C6 | **A majority, once won, stays won** — votes only accumulate and the cluster does not change size, so a leader elected at term 7 remains, as a matter of record, the winner of term 7 | `raft::proofs::election::lemma_quorum_survives` | none |
| C7 | **Terms never decrease, and votes are never retracted.** The Raft counterparts of epoch monotonicity (claim 5) and token permanence (P1) — and a vote is physical in the same sense a token is, which is exactly why a returning server must not vote again in a term it has already voted in | `raft::proofs::election::theorem_term_monotone_step`, `theorem_votes_monotone_step` | none |
| C8 | **The coupling guards agree with the composed model.** `PassToken` fires only once the actor is `Unowned` and the routing layer's own step fires; `SeizeToken` only from the holder, to a different node, with the actor `Unowned`; `AcquireUnderToken` only for the node holding the privilege; `Reconcile` only for a node that owes one and whose belief is stale. Each refuses exactly when the composed model's transition is not enabled | `composed::proofs::refinement::theorem_pass_token_step_refines`, `theorem_pass_token_refuses_while_the_actor_is_held`, `theorem_pass_token_refuses_when_the_routing_step_does`, `theorem_seize_step_refines`, `theorem_seize_step_refuses_exactly_when_disabled`, `theorem_acquire_under_token_step_refines`, `theorem_acquire_under_token_refuses_a_node_without_the_privilege`, `theorem_reconcile_step_refines`, `theorem_reconcile_step_refuses_exactly_when_disabled` | **every node is live** (`own.live.contains(..)`) — the service has no `Crash` step, so it refines the composed machine's crash-free executions; see below |
| C9 | **A step a layer already proved is carried by the composed machine without a second proof.** `cs_ray` adds only that the step does not move the privilege and that its actor is live; `cs_own` adds only that the step does not create authority over this actor and does not bring back a node owing a reconciliation | `composed::proofs::refinement::theorem_a_routing_step_is_carried`, `theorem_an_ownership_step_is_carried` | the hypotheses of the carried step |
| CX1 | **The composed steps over the layers' records are the composed model.** `composed::exec::pass_token`, `seize_token`, `acquire_under_token` and `reconcile` take the ownership record (`RegistryCore`), the routing record (`RayTable`) and the set of nodes that owe a reconciliation (`id::IdSet`), check the coupling guard, take the layers' steps and keep the debts — and each contract is `cs_pass_token`, `cs_seize_token`, `cs_acquire_under_token` or `cs_reconcile`: the privilege moves only once the actor is `Unowned`, only `to` acts on a seizure and the old holder then owes a reconciliation, the recipient of a passed privilege is discharged of its debt, a node acquires only holding the privilege. The relation (`stands_for_composed`) is the ownership relation of E8 (grants included), the routing view *being* `c.ray`, and the debts *being* `c.seized` | `composed::proofs::exec::theorem_pass_token_is_cs_pass_token`, `theorem_seize_token_is_cs_seize_token`, `theorem_acquire_under_token_is_cs_acquire_under_token`, `theorem_reconcile_is_cs_reconcile` | the nodes involved are live (`own.live`). The service's identity lookup speaks only for the *caller*; the recipient of a passed privilege and the target of a seizure are not callers, so for them this is a hypothesis nothing in the service establishes |
| CX2 | **A refused composed step is one the model could not take.** A refusal changes neither layer nor the debts and carries "the actor was not released, or the layer's own step was disabled in every post-state" (`pass_token`, `seize_token`), "the node does not hold the privilege" (`acquire_under_token`), or "the node owes nothing, or is not stale" (`reconcile`). **Not claimed**: that a refusal from the ownership layer inside `acquire_under_token` (no published grant, a wrong epoch) is a step the *composed* model could not take — it is the ownership layer's own refusal, covered by E8, and the composed theorem for `acquire_under_token` is about the privilege test only | `composed::proofs::exec::theorem_refused_pass_token_is_disabled`, `theorem_refused_seize_token_is_disabled`, `theorem_acquire_without_the_privilege_is_disabled`, `theorem_refused_reconcile_is_disabled` | `stands_for_composed` |
| C8 | **A lone self-vote is not a majority** in a cluster of more than one. The check that the `>` in the quorum threshold is load-bearing rather than decorative: with `>=` a single server could elect itself | `raft::proofs::election::theorem_a_lone_vote_is_not_a_majority` | a cluster of at least two |
| C9 | **An election actually happens.** A concrete three-server cluster walked from initialisation through a real election, exported with every step named, so C1 is not a safety property of a protocol that never elects anybody | `raft::proofs::scenario::scenario_a_leader_is_elected` | none: the cluster is exhibited |
| C10 | **The election steps refine the model**, in both directions: each executable step fires exactly when the model's transition is enabled, and lands where the model lands | `raft::proofs::refinement::theorem_timeout_step_refines_tr_timeout`, `..._grant_vote_...`, `..._become_leader_...`, `..._step_down_...`, and the `..._refuses_exactly_when_disabled` for each | the couplings, tabulated in `raft::proofs::refinement`'s module docs |
| C11 | **The `u64` tally answers the model's question about the set.** `is_majority` computes `votes + votes > members` with no multiplication to overflow and no subtraction that can go below zero; this is what makes that the same question as `is_quorum` | `raft::steps::is_majority`, `raft::proofs::refinement::theorem_majority_count_is_a_quorum`, `theorem_a_tally_fits_in_the_membership` | that the tally does not double-count a voter and the membership count is not stale — neither of which a step function can check, so both are named |
| CE1 | **The election record is the model.** `exec::ElectionCore` — a server's role and term, whom it voted for in that term, and the votes it has counted — takes the model's step at every method: `stand` is `tr_timeout` (the next term, a self-vote, a tally of one); a fresh `grant` is `tr_grant_vote`; counting a vote that makes a majority of voters who each voted is `tr_become_leader`; `step_down` is `tr_step_down`, and the vote and tally leave with the old term; `yield_to` is the role change `tr_append_entries` makes on a candidate. The relation (`stands_for`) is the cluster's role and term, **the vote** (the core's `voted_for` is exactly `has_voted(c, n, term)` — the equality `grant_vote_step`'s `already_voted` stands for), **the tally** (a subset of the voters for this candidacy — `has_quorum ⇒ won_election`), and that no vote by this server is ahead of its term | `raft::proofs::election_core::theorem_stand_is_tr_timeout`, `theorem_grant_is_tr_grant_vote`, `theorem_a_won_count_is_tr_become_leader`, `theorem_step_down_is_tr_step_down`, `theorem_yield_is_the_append_role_change`, `lemma_already_voted_is_has_voted` | `stands_for`; a counted ballot was a vote that was cast (receiving a `Granted` for this term supplies it); the candidate's log is up to date, supplied by the caller's comparison |
| CE2 | **A refused election step is one the model could not take.** A refused `stand`, `grant` or `step_down` is a step the model's transition is not enabled for, in any post-state (for a log that is behind, given that the caller's `up_to_date` is the model's `at_least_as_up_to_date`); a refusal changes neither the term, the vote nor the tally. A count that does not win is **not** claimed to be a step the model could not take: the tally is a subset of the voters and may undercount, so a not-yet-majority tally says nothing about `won_election`. The theorem covers the other direction — where the *model's* election is not won, `tr_become_leader` is disabled. The retransmission of a vote already given is the one answer that is outside the model's transition by design — a repeat of an earlier reply, the model's `votes` being a set. A refusal because the `u64` term ran out is the one the model does not have, and says so | `raft::proofs::election_core::theorem_refused_stand_is_disabled`, `theorem_refused_grant_is_disabled`, `theorem_refused_stale_log_is_disabled`, `theorem_a_lost_count_is_disabled`, `theorem_a_refused_step_down_is_disabled` | `stands_for` |
| C12 | **Elections do not touch logs, and neither does committing.** Standing, voting, winning and standing down change who a server thinks it is; advancing the commit point is a claim about how much of the log is decided, not a change to it | `raft::proofs::log::theorem_elections_do_not_touch_logs`, `theorem_committing_does_not_touch_the_log` | none |
| C13 | **Leader Append-Only.** A server that is a leader before and after a step has only gained entries — everything it had, it still has, in the same places. This is where Election Safety buys something concrete: the only transition that shortens a log makes its receiver a follower, so a server that is a leader on both sides was not the receiver | `raft::proofs::log::theorem_leader_append_only` | none |
| C14 | **A client command is stamped with the term of the leader that accepted it**, and appended at the end. The term on an entry names the leader that made it, because Election Safety says there was only one leader of that term | `raft::proofs::log::theorem_client_request_stamps_the_leaders_term` | none |
| C15 | **A follower agrees before it accepts** — the consistency check, named: it takes an entry at `prefix` only if it already holds an entry at `prefix - 1` of the leader's term, and drops everything beyond | `raft::proofs::log::theorem_a_follower_agrees_before_it_accepts` | none |
| C16 | **Entries are never invented.** A follower's new entry is the leader's entry at the same index — copied, not constructed | `raft::proofs::log::theorem_replication_copies_the_leaders_entry` | none |
| C17 | **Commitment needs a majority *and* the entry has to be of the committing leader's own term** — figure 8 of the Raft paper. A majority *holding* an entry is not a majority having *voted* on it, and committing on replica count alone lets a later leader overwrite it | `raft::proofs::log::theorem_commit_needs_a_majority_of_its_own_term` | none |
| C18 | **Two commits of the same length share a holder.** As far as quorum intersection reaches without Log Matching: it produces a server holding both prefixes, which is the first line of a Leader Completeness proof and not a substitute for one | `raft::proofs::log::theorem_two_commits_share_a_holder` | none |
| C19 | **One log is extended per term**, because the leader of a term is unique. A corollary of C1, stated because it is the shape every later log argument leans on | `raft::proofs::log::theorem_one_log_is_extended_per_term` | the Raft invariant |
| C20 | **An append makes its receiver a follower, and the executable step computes that** — the role change at an *equal* term, which `tr_step_down` cannot reach and which figure 2 gives candidates. The refusal side is stated asymmetrically on purpose: a leader at an equal term is the state Election Safety rules out, and a step that fired on it would let any peer depose a leader by naming its term | `raft::proofs::refinement::theorem_an_append_makes_its_receiver_a_follower`, `theorem_follow_step_agrees_with_tr_append_entries`, `theorem_follow_step_refuses_exactly_when_disabled` | none |
| C21 | **The ghost history neither enables nor disables anything.** For *any* history whatsoever — not the one the run produced, any at all — every step still fires from the same real state and lands in the same real state. This is the soundness condition for an auxiliary variable, and it is what makes `Cluster::created` and `Cluster::led` a record rather than an assumption: no guard reads them | `raft::proofs::history::theorem_history_does_not_gate_the_protocol`, `theorem_history_is_monotone` | none |
| C22 | **At most one server *ever* leads a term** — across the whole run, not merely at one instant. Strictly stronger than C1, which compares two servers that are leaders *now*: a leader that stepped down an hour ago is outside C1 and its entries are still in logs. The sentence the log argument needs, and it cannot be stated without history | `raft::proofs::history::theorem_at_most_one_server_ever_leads_a_term`, `..._reachable` | the history invariant |
| C23 | **Having led a term, you are still leading it or you have moved past it.** The load-bearing history invariant. The ways to stop leading either raise the term or cannot fire: a leader of `t` is refused a vote in `t` because it spent that vote on itself, and an append demoting it at an equal term would be two leaders in one term | `raft::proofs::history::inv_led_means_at_or_past`, with `inv_standing_implies_voted`, `inv_leader_is_led`, `inv_led_implies_won` | the Raft invariant (Election Safety) |
| C24 | **A leader of a term holds everything created at that term** — the freshness clause. A leader appends at the end of its own log, and this says every slot already written at its term is inside that log, so the slot it is about to write is not one of them. At `tr_become_leader` it holds because a term being won *now* has never been led, which is C22 | `raft::proofs::history::inv_creator_holds`, `lemma_become_leader_finds_its_term_unwritten`, `lemma_client_request_writes_a_fresh_slot` | the history invariant |
| C25 | **The consistency check is exactly the guard that keeps the creation record true.** A follower taking the leader's entry at `prefix` records a predecessor that is now *its own* entry at `prefix - 1`, not the leader's — and those agree precisely because `tr_append_entries` will not fire unless they do | `raft::proofs::history::lemma_the_consistency_check_preserves_the_record` | the history invariant |
| C26 | **Log Matching — two logs that agree on an entry's term at an index agree on every entry at and below it.** The headline of the log half. One slot gives one recorded value and one recorded predecessor, so agreement at an index is agreement one index down, and repeating reaches zero | `raft::proofs::history::theorem_log_matching`, `theorem_log_matching_prefixes`, `theorem_log_matching_values`, `theorem_log_matching_reachable` | `inv_logs_follow_created`, discharged for reachable states by `theorem_reachable_hist_inv` |
| C27 | **Recovery is exact.** The in-memory log equals `replay` of the device before and after every operation — append, truncate, *and* crash-recovery. The recovery case is trivial, and that is the design working: the device **is** the log, not a journal of intentions about it, so recovery reconciles nothing | `raft::proofs::store::theorem_recovery_is_exact`, `theorem_the_store_always_agrees`, `theorem_a_fresh_store_agrees` | none |
| C28 | **A crash can only rewind.** `replay` is total on every sequence of records, so there is no prefix a crash can leave that recovery cannot read, and what comes back is a log the store had rather than one no sequence of writes could produce. Records that reached the device are unchanged and at the same indices | `raft::proofs::store::theorem_a_crash_can_only_rewind`, `theorem_a_crash_keeps_what_reached_the_device` | that a crash keeps a **prefix** — the property an append-only device gives you, and what pmemlog's write restriction enforces |
| C29 | **Accepting a replicated entry costs at most two records**, and `appended_log` is what they replay to — so figure 2's rule 3, which deletes a suffix, is implementable on a device that deletes nothing. **Three costs, and which one you pay says what just happened**: *nothing* when the entry is already there, so a duplicate `AppendEntries` never reaches the device; *one record* when extending, since the marker would be `Truncate { len: log.len() }` and writing the identity would double the cost of the steady state; *two* on a genuine conflict, however long the tail it deletes. The zero-cost branch is C25's conditional again, as an operational fact | `raft::proofs::store::theorem_accepting_an_entry_is_at_most_two_records`, `theorem_extending_the_log_costs_one_record`, `theorem_a_follower_accepts_with_at_most_two_writes` | the store invariant (C27) |
| C30 | **The device is append-only.** No operation moves its tail back: the records that were there are still there, in order, at the same indices. A `Record::Truncate` shortens the *log* and lengthens the device. This is the property that lets the whole store sit on `vendor/verified-storage/pmemlog`, whose abstract state has `append` and `advance_head` and nothing that shortens a tail | `raft::proofs::store::theorem_the_device_is_append_only` | none |
| C31 | **Compaction is sound**, costs one record per entry, and leaves no truncation behind — so a store can rewrite itself as pure appends. It is also **scheduled**: `worth_compacting` fires at `records > 2 * (entries + 1)`, which is amortised O(1) per operation, and the bound is asserted every round over sixty rounds of the worst shape. This row read *"soundness only: nothing schedules it"* for three PRs after the policy landed — the code and the claim drifted apart in the direction that understates the code, which is rarer and no better | `raft::proofs::store::theorem_compaction_replays_the_same`, `theorem_compaction_is_one_record_per_entry`, `theorem_compaction_leaves_no_truncations` | none |
| C32 | **Cut the bytes anywhere and a record prefix comes back** — for *every* `k`, not for multiples of seventeen. The tear can land in the middle of a `u64` and the theorem still holds, because fixed width means no byte of a half-written record can be mistaken for the start of a whole one. This is what C28 needs and cannot state for itself: `store_recover` is written over a *record* prefix, and a device gives back a *byte* prefix | `raft::proofs::wire::theorem_a_torn_tail_is_a_record_prefix`, `theorem_recovery_from_a_torn_device` | every record fits in 64 bits (`records_fit`) |
| C33 | **What was written is what is read**, and the encoding is exactly seventeen bytes per record — which is what makes `bytes.len() / 17` the record count and the parser's stopping condition an observation rather than an argument | `raft::proofs::wire::theorem_parse_of_encode`, `theorem_the_encoding_is_fixed_width`, `lemma_a_record_round_trips`, `lemma_a_record_is_seventeen_bytes` | `records_fit` |
| C34 | Eight bytes, least significant first, and back again | `raft::proofs::wire::lemma_le_round_trip` (by `bit_vector`) | none |
| C35 | **Nothing reported durable is ever lost, by any transition, ever.** The line does not retreat *and* everything below it is unchanged record for record — a store that kept the right *number* of records while rewriting one would satisfy the first clause and fail the second. Stated per step, across a whole run with any number of crashes, and finally as the sentence Raft needs: **a follower that answers `Accepted` has written the entry down**, so a leader counting that answer toward a majority is counting something that cannot be taken back | `raft::proofs::store::theorem_durability_never_retreats`, `theorem_a_durable_record_is_durable_for_ever`, `theorem_a_follower_that_answers_accepted_has_written_it_down`, `theorem_a_crash_keeps_everything_reported_durable` | that a crash keeps a **prefix** of the records, and that a `LogStore` method is durable before it returns — the latter discharged by `theorem_an_append_is_a_write_then_a_sync` |
| C36 | **A staged compaction is inert until the old generation is reclaimed, and the batch has no middle.** Compaction on an append-only device is two steps and a crash can land between them; writing `compacted(log)` alone would leave `old ++ compacted(log)`, which replays to **`log + log`**. The leading `Truncate { len: 0 }` makes the staged generation self-sufficient, so the device means the same log with the old records there and once they are gone — which turns the reclaim into a no-op rather than a change. And the batch is written by one `store_write_batch`, so no recovery the model permits can observe it part-way | `raft::proofs::store::theorem_a_staged_compaction_is_inert`, `theorem_after_compaction_the_old_records_are_dead`, `theorem_an_atomic_batch_has_no_middle`, `lemma_a_compacted_log_appends_itself` | that the batch lands atomically — one pmemlog `append`, whose crash view is the log before it or after it and nothing between. The **one** property of the device this design asks for and cannot itself check |
| C36b | **A batch written a record at a time rewinds the log**, exactly — a crash after `k` of its entries recovers exactly `k`. The reason C36 needs atomicity rather than merely preferring it: the marker has already cleared everything, so a partial batch is the compaction of a *shorter* log. Proved as an equality, not a possibility | `raft::proofs::store::theorem_a_partial_batch_can_rewind`, `lemma_compacted_take_is_take_compacted` | none |
| C37 | **Every reachable store is encodable, so the two halves compose.** `records_fit` is a guard on the write transitions and a clause of `store_inv`, not a precondition that filters which theorems may be *invoked* — stated only on the theorems, an unencodable state stays reachable and the encoding theorems quietly stop applying exactly where they are needed. This is the theorem that spends it: any store satisfying the invariant round-trips through the encoding *and* survives a tear at any byte | `raft::proofs::wire::theorem_a_reachable_store_is_encodable`, `theorem_no_reachable_store_is_unwritable`, with `lemma_pushing_a_fitting_record_fits`, `lemma_a_prefix_of_a_fitting_sequence_fits` | none |
| C38 | **The commit point never outruns the log**, and **retreats only when a truncation cuts below it**. Raft's commit index is supposed to be monotone; `accepted_commit`'s clamp to the log length gives that up in exactly one case, because a truncation below the commit point forces a choice between a commit index naming absent entries and one that goes backwards. This model retreats — a broken promise is readable, a commit point past the end of the log is not — and these say precisely when. Commit **is** monotone whenever the truncation is at or above it, which is every step of a healthy cluster; and when it retreats, the leader deleted an entry the follower had *committed* | `raft::proofs::log::theorem_the_commit_point_never_outruns_the_log`, `theorem_the_commit_point_does_not_retreat_above_a_truncation`, `theorem_the_commit_point_retreats_only_below_a_truncation`, `theorem_a_commit_retreat_means_a_committed_entry_was_deleted` | none — and the condition on monotonicity is exactly what **Leader Completeness** would discharge, so when that lands the hypothesis becomes vacuous and monotonicity becomes unconditional |
| C39 | **A log's terms never decrease, and none exceeds its holder's own term.** Two facts proved together, because they hold for one reason: a leader stamps a new entry with its own term, and that term bounds everything already in the log, so the new entry is the largest *because* it is bounded. The replication case is the **consistency check** paying for itself a third time — a follower accepting at `prefix` keeps `follower.take(prefix)` and adds the leader's entry, and the terms of that are sorted only because the two logs *agree* at `prefix - 1` | `raft::proofs::terms::inv_log_shape`, `theorem_reachable_term_inv`, `lemma_accepting_keeps_shape`, `lemma_push_keeps_shape` | none |
| C40 | **The last term is the largest**, so the up-to-date comparison — which reads only a log's final entry — says something about every entry in it. One line from C39, and the line the election restriction is stated over | `raft::proofs::terms::lemma_the_last_term_is_the_largest` | none |
| C41 | **A follower that already agrees with the leader at an index keeps its entry there.** The payoff of C25's conditional truncation, and the reason it is load-bearing rather than merely faithful to figure 2. If `prefix <= i`, Log Matching says the two logs agree at `prefix` as well, so the guard fires and the follower's log is **not touched at all**; if `prefix > i`, the truncation is above `i`. Under an *unconditional* truncation the first case is false — a duplicate `AppendEntries` for an early index would delete an entry the follower already agreed on — and the induction Leader Completeness needs would have no base | `raft::proofs::terms::theorem_a_follower_that_agrees_keeps_the_entry` | Log Matching (C26) |
| C42 | **An entry leaves a log only to a leader that disagrees with it there.** C41 lifted from one transition to the whole relation, which is the shape the missing induction consumes: it has to rule out an entry vanishing from a voter's log between the moment a quorum stored it and the moment that voter cast its next vote, and this says the only step that can is an `AppendEntries` from a leader whose own log differs at that index | `raft::proofs::terms::theorem_an_agreed_entry_survives_any_step` | Log Matching (C26) |
| C43 | **A candidate behind on terms is refused, and cannot collect that vote.** A voter holding *any* entry of term `T` refuses every candidate whose last term is below `T` — so `tr_grant_vote` cannot fire, stated over the transition relation rather than over the guard. An empty log is the special case that makes C39's *lower* bound worth having: `last_term` of an empty log is 0, no entry is ever at term 0, so an empty log is strictly behind every non-empty one rather than incomparable with it | `raft::proofs::terms::theorem_a_candidate_missing_a_term_is_refused`, `theorem_a_stale_candidate_cannot_collect_that_vote`, `theorem_an_empty_log_cannot_win_a_vote`, `theorem_a_stale_candidate_cannot_collect_that_vote_reachable` | none |
| C44 | **Every committed entry matches the creation record of its slot**, and its own term is at least 1 and no later than the term of the leader that committed it. The bridge from the new `committed` ghost record to the `created` record Log Matching is stated over. It survives `tr_client_request` — the one transition that *inserts* into `created`, where an insert at a slot already written would silently replace a record a committed entry is matched against — because C22's `inv_creator_holds` puts every slot already created at a leader's term *inside* that leader's log, and the slot being written is one past its end | `raft::proofs::commit::inv_committed_is_created`, `inv_committed_within_its_term`, `theorem_reachable_commit_inv` | none |
| C45 | **At the moment of commitment a majority held that entry at that index** — entry for entry, not "a prefix of that length". The difference is the whole point: quorum intersection hands the induction a voter, and what it needs from that voter is the entry in its log, not a count. Stated over the transition, because it is the one fact about commitment that is about a moment rather than a state | `raft::proofs::commit::theorem_a_commit_was_on_a_quorum` | none |
| C46 | **Two commits at one index whose entries carry the same term are the same entry** — so **State Machine Safety holds with exactly one hypothesis added**, that the two commits agree on the entry's term. The value half is free: one `(term, index)` names one act of creation by one leader, which Election Safety and the `created` record give unconditionally. Nothing about values, quorums or counting is missing. What is missing is the answer to one question — can two leaders commit entries of *different terms* at one index? — and that question is Leader Completeness | `raft::proofs::commit::theorem_two_commits_at_one_slot_agree`, `theorem_state_machine_safety_at_agreeing_terms` | that the two commits agree on the entry's term, which is precisely Leader Completeness |
| C47 | **A commit is a commit for ever**, across a whole run, and the ghost record covers the real count at the moment it is written. The first is what makes the record usable where `Server::commit` is not — a count on one server that C38 proves *retreats*. The second is what stops it becoming a second bookkeeping scheme that drifts from the first, a hazard this repository was already bitten by once in `records_fit` (C37) | `raft::proofs::commit::theorem_a_commit_is_a_commit_for_ever`, `theorem_the_record_covers_the_count`, `raft::proofs::history::theorem_history_is_monotone` | none |
| C48 | **An entry persists across a run whenever every leader replicating to its holder already agrees with it there.** The run-level form of C42, and it exists because the *prose* around C42 was wrong in a way the theorem never was: this document said the persistence step was already a theorem, when C42 carries a hypothesis — the replicating leader must already agree at that index — whose discharge for every intervening leader **is** Leader Completeness at the intervening terms. The condition now lives in a signature, quantified over the steps between the two states. **Sufficient, not necessary**: a replication at a `prefix` below the index, where the logs happen to agree at `prefix`, leaves the follower's log untouched and the entry survives whatever the leader holds above it. Sufficiency is all the induction needs. This is the lemma it calls at its inductive step, with the induction hypothesis discharging the quantifier | `raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`, `replication_agrees_at`, `lemma_a_labelled_execution_is_an_execution` | the quantifier in its own statement, which is exactly the induction hypothesis |
| C49 | **Every vote has its judgement on the record, and every recorded vote went to a candidate at least as up to date as the voter's log at that moment.** `tr_grant_vote`'s guard compares against a log *at an instant*; by the time any later theorem asks what the comparison was, the voter has extended, truncated or replaced that log. `Cluster::voted_with` records both sides — the voter's log as it stood and the candidate summary it was weighed against — because storing one side would leave the other to be reconstructed from a state that no longer holds it. The completeness clause matters as much as the judgement clause: a record written in some arms and not others would be silently partial, and a theorem quantified over it would say nothing about the votes it had missed. That is why `tr_timeout`'s self-vote is recorded even though it constrains nothing | `raft::proofs::votes::inv_every_vote_has_its_log`, `inv_a_vote_was_up_to_date`, `inv_a_recorded_log_is_shaped`, `theorem_reachable_vote_inv` | none |
| C50 | **A candidate that won a vote was at least as late, in terms, as every entry in that voter's log** — C43 read off the record rather than off a live state, which is the whole reason the record exists. And **quorum intersection with the judgement attached**: any quorum whatsoever meets the winner's voters in a server for which the record says what its log was when it voted, and that the winner's summary dominated it. Instantiate that quorum with the one C45 produces — the majority that held a committed entry — and the shared voter is a server that both held the entry and judged the winner at least as up to date as its own log. This is the induction's first and third steps joined at a single voter | `raft::proofs::votes::theorem_a_voter_saw_nothing_later_than_the_candidate`, `theorem_a_winner_shares_a_judged_voter_with_any_quorum`, `theorem_a_winner_shares_a_judged_voter_with_any_quorum_reachable` — the reachable wrapper **repeats** the existential rather than forwarding it, because a wrapper's contract is written and not inferred: a caller sees only what the wrapper's own `ensures` says, so forwarding a call does not forward its postconditions | none — but it is a statement about **one state**, and the induction needs the commit-time quorum carried *across the run* to the election, which is C48's conditional job |
| C51 | **A `RequestVote`'s summary is a snapshot of the log it summarises**, for as long as its sender is still a standing candidate of that term — and every judgement on the record quotes a `RequestVote` that is still on the wire. No fifth ghost record was needed for this — `Cluster` already carries four, and the reason is worth naming: **`Cluster::messages` never shrinks**, so the network is already a history variable. The third clause, that a `RequestVote` never names a term its sender has not reached, looks like bookkeeping and is what makes the second *inductive*: the awkward case is `tr_timeout` itself, where a server becoming a candidate of `t` makes every `RequestVote` for `(t, n)` on the wire suddenly have to summarise its new log. The one it just sent does; an **older** one would not, and would sink the invariant. There is no older one, because a server enters a term once — which is that third clause, machine-checked | `raft::proofs::summary::inv_a_recorded_summary_was_on_the_wire`, `inv_a_requestvote_is_not_ahead_of_its_sender`, `inv_a_requestvote_summarises_a_candidate`, `theorem_reachable_summary_inv` | none — and no other invariant bundle is carried either, which is unusual here: the argument is entirely about the network and one server's role |
| C52 | **At the instant it wins, a new leader's own log is at least as up to date as the log of a voter it shares with any quorum whatsoever** — and its last term dominates every entry that voter held. This is C50 with the winner's *log* in place of the pair of integers C50 actually produced. Read C50's conclusion again: `at_least_as_up_to_date(ct, ci, lg)`, where `ct` and `ci` are two numbers that arrived over the network, and nothing anywhere said they had anything to do with the winner's log. The induction's third step was therefore not available, and this document asserted it was. `tr_become_leader` is the right place to state it, because it is the last instant at which the winner is still a candidate and so the last instant at which its summary is its log — afterwards the log grows and the `RequestVote` is spent | `raft::proofs::summary::theorem_a_candidate_is_judged_on_its_own_log`, `theorem_a_candidate_dominates_its_judged_voter`, `theorem_a_candidates_log_is_the_latest_its_voters_saw`, `theorem_the_new_leaders_log_dominates_a_judged_voter`, `theorem_the_new_leaders_log_dominates_a_judged_voter_reachable` — the reachable wrapper repeats its existential, per the rule C50 learned | none |
| C53 | **Every member of a commit's quorum is already at the committing leader's term or past it — so only a leader at or past that term can ever write to it again.** Three lines and a guard: figure 8's restriction says the last entry of the committed prefix carries the leader's own term `T`, a quorum member holds that prefix so it holds an entry of term `T`, and `terms_within` says no entry's term exceeds its holder's own. Terms never fall across a run, so it stays true. And `tr_append_entries` — the only transition that can shorten a log — requires the leader's term to **equal** the follower's, so nothing below `T` can touch it. Note which guard is load-bearing: without figure 8, the committed prefix could end in an *old* term and this would be false. That restriction is usually explained as ruling out one counterexample; here it is what gives the whole argument its shape | `raft::proofs::persistence::theorem_a_term_never_falls_across_a_run`, `theorem_a_commit_quorum_is_at_or_past_its_term`, `theorem_a_replicating_leader_shares_the_followers_term` | none |
| C54 | **A member of the quorum that committed an entry still holds it at any later point, provided every leader from the commit's term onwards held it** — which is C48 with its hypothesis translated out of *steps* and into *leaders of terms*. That translation is the content. C48 quantifies over every step of the run; the induction hypothesis is a statement about leaders, so between the two sat a gap that the roadmap crossed **in prose** by saying C48's hypothesis "is the induction hypothesis at the intervening terms" — true, and not a translation. C53 is what performs it: the steps that could hurt are driven by leaders at one known term, the holder's. `replicators_hold` is the tight form — every standing leader that could reach the holder *right now* — and carries no term bound, because persistence needs none; `leaders_within_hold` is what the induction supplies, Leader Completeness over the **closed range** `[t0, t1]`. **Both bounds are load-bearing, and the upper one is there because `@codex` found the first version of this module without it**: strong induction on the election's term supplies Leader Completeness *below* that term, and an unbounded predicate demands it above as well. Such leaders exist — nothing here orders terms cluster-wide, so a far-higher-term leader can be running while a delayed campaign still collects votes — and they are harmless, since they cannot replicate to a voter at a lower term. The old predicate demanded they hold the entry anyway, so C54 could not have been discharged without assuming the conclusion at terms the induction had not reached | `raft::proofs::persistence::replicators_hold`, `leaders_within_hold`, `lemma_a_bounded_hypothesis_covers_the_replicators`, `theorem_an_entry_survives_leaders_that_could_reach_it`, `theorem_a_commit_quorum_still_holds_it` | the hypothesis in its own statement — now the induction hypothesis over a closed range, whose **upper endpoint the induction still owes**: a leader of `t1` can exist before this voter has voted in `t1`, because winning `t1` needs *a* quorum and not this one |
| I | The inductive invariant holds in every reachable state (`init ==> inv`, `inv /\ next ==> inv`) | `ownership::proofs::invariant::theorem_reachable_inv` | the model's transition relation |
| S | **The headline scenario**: `A` owns X@41, a transfer and a crash/recovery occur, `B` owns X@42, `A` returns still holding its epoch-41 token - and cannot perform an authoritative mutation. The postcondition exports the whole nine-step run, so the crash, the recovery and the outcome are the same execution — exported as separate existentials they need not have been, and an ordinary live handover could supply the outcome | `ownership::proofs::adversarial::scenario_stale_owner_returns` | `A != B` |
| S1 | A stale `Grant` cannot resurrect a superseded epoch | `ownership::proofs::adversarial::theorem_stale_grant_cannot_be_used` | none |
| S2 | Message duplication / reordering / delay cannot change ownership | `ownership::proofs::adversarial::theorem_network_steps_cannot_change_ownership` | none |
| S3 | Crash and stale-node recovery cannot change ownership | `ownership::proofs::adversarial::theorem_crash_recovery_cannot_change_ownership` | none |
| S4 | An interrupted transfer leaves nobody with authority and burns the epoch. A step property, not a constructed execution — hence `theorem_`, not `scenario_` | `ownership::proofs::adversarial::theorem_interrupted_transfer_burns_the_epoch` | `inv` holds before the step (and so, by `theorem_reachable_inv`, every reachable state) |
| S4a | **An interrupted transfer really happens**: the run is exported with its four labels, so the `AbortTransfer` at index 3 interrupts the very `BeginTransfer` at index 2 that opened the transfer, ending at `Unowned(43, A)` with nobody able to mutate at 41 or 42. Without it, S4 stays provable even if `AbortTransfer` were changed to be always false — a conditional lemma about an unreachable transition | `ownership::proofs::adversarial::scenario_interrupted_transfer` | `A != B` |
| S5 | **A fabricated `Released` is inert.** `HandleRevoke` lets any live node manufacture a `Released` from any `Revoke` ever sent, however old. `CompleteRelease` is the only step that consumes one, and it re-reads the actor's current state, so if it fires the actor is `Transferring` right now and the network holds the `Released` naming exactly that handover's `from` and `new_epoch` | `ownership::proofs::adversarial::theorem_complete_release_needs_the_matching_released` | none |
| S6 | **A fabricated `Released` cannot steer a handover.** The resulting epoch is read from the live `Transferring` record, not from the message | `ownership::proofs::adversarial::theorem_complete_release_outcome_is_fixed_by_state` | none |
| R1 | **Raymond: exactly one valid privilege** - now *structural*: `Raymond::privilege` is one node id, so uniqueness needs no invariant. It used to be inductive, and that was exactly what made a returning stale holder unrepresentable | `raymond::proofs::routing_layer::theorem_ray_exactly_one_token`, `theorem_ray_at_most_one_token`, preserved by `lemma_ray_step_preserves_inv` | Raymond invariant |
| R2 | **Raymond: holder/routing changes cannot manufacture ownership** | `raymond::proofs::routing_layer::theorem_routing_cannot_manufacture_ownership` | Raymond invariant, coupling |
| R3 | **Raymond: duplicate/reordered requests cannot create a second owner** | `raymond::proofs::routing_layer::theorem_duplicate_requests_are_safe` | Raymond invariant |
| R4 | **Raymond: token transfer preserves ownership safety** | `composed::proofs::coupling::lemma_composed_pass_token_preserves_inv` (and, as a layer-local lemma, `raymond::proofs::routing_layer::theorem_token_transfer_preserves_ownership_safety`) | none — in the composed machine the release-before-transfer condition is a *guard*, not an assumption |
| R5 | **Composed exclusivity**: in every reachable composed state at most one node may mutate the actor, and it is the node holding the token | `composed::proofs::coupling::theorem_composed_exclusivity` | composed reachability |
| C0 | **Non-degeneracy**: a composed state in which a node is *actually inside* the critical section is reachable from `composed_init`. The contract exports the run: three labels, `RequestCs` / `EnterCs` / `ExitCs`, with `using` false at indices 0, 1 and 3 and true at 2 — so the node inside got there by entering, and the exit leaves the state it entered | `composed::proofs::scenario::scenario_composed_critical_section` | `A != B` |
| C0a | (Step-level lemma backing C0) `EnterCs`/`ExitCs` are legal `ComposedStep::Ray` transitions and preserve the composed invariant | `composed::proofs::coupling::theorem_composed_admits_critical_section`, `..._exit` | composed invariant holds before the step |
| C1 | **Non-vacuity**: a complete *voluntary* handover driven through **both** layers is reachable. The contract exports the whole run: `labels == handover_labels(x, a, b)` — ten steps, `BeginTransfer` at 2, `CompleteRelease` at 4, `PassToken` at 8 — plus the `Transferring { a, b, 41, 42 }` state at index 3, since the labels carry no epochs. No other execution satisfies it: the substitutes that satisfied earlier versions were crash takeover, revoking a live `A`, and an unrelated 39 → 40 transfer | `composed::proofs::scenario::scenario_composed_handover` | `A != B` |
| C2 | **Crash-driven takeover is reachable in the composed machine**: `A` owns X@41 holding the token, crashes and takes no further step; the coordinator burns the epoch; the token is *seized*; `B` ends up owning X@42 and holding the token, with `A`'s epoch-41 token still issued and powerless. The postcondition exports the whole run — eight labels with `Crash(A)` at 2, `RevokeOwner` at 3 and `SeizeToken` at 4, and no `CompleteRelease` anywhere, so a voluntary release before the crash cannot stand in for the revocation | `composed::proofs::scenario::scenario_composed_crash_takeover` | `A != B` |
| C3 | Seizing the token preserves the coupling and leaves the target holding the one token — safety comes from the epoch being burned first, not from the holder agreeing to let go | `composed::proofs::coupling::lemma_composed_seize_preserves_inv`, `raymond::proofs::routing_layer::lemma_seize_preserves_inv` | composed invariant. **No liveness assumption**: the epoch was burned first, so this holds even when the seized node is healthy and was suspected wrongly — see below |
| C4 | **Privilege movement is partitioned by cooperation**: a holder that acts passes it on, a holder that does not has it taken, and no other composed step moves it at all. This used to be partitioned by *liveness*, which required a guard no coordinator can evaluate | `composed::proofs::coupling::theorem_token_movement_is_partitioned` | composed invariant |
| C5 | The two layers describe the **same cluster**: `ray.nodes == own.nodes` is part of `composed_inv` and `composed_init`. Without it a Raymond root could be a node the ownership layer never heard of, so `!own.live.contains(n)` would hold for it with no `Crash` having happened, and the seizure guard would be satisfied by unmodelled liveness rather than by a fail-stop | `composed::model::composed_inv`, preserved by `composed::proofs::coupling::theorem_composed_step_preserves_inv` | — |
| P10 | **The node population is constant** — `Crash` and `Recover` move nodes in and out of `live`, never out of `nodes` | `ownership::proofs::properties::theorem_node_domain_constant` | none |
| C6 | **A seized node cannot rejoin `live` while still seized** — `cs_own` refuses `Recover` for it, so the only way back is through `Reconcile`, which now carries the content the claim always asserted: it is where the stale belief is dropped, by the node that holds it. Backed by `composed_inv`'s "every stale holder owes a reconciliation", which is what makes `seized` mean somethint must perform a step an execution has to contain rather than an assumption | `composed::proofs::coupling::theorem_seized_node_cannot_recover` | — |
| C7 | Reconciliation is **not a dead end**: `A` can be told what happened and then rejoin, holding no token and no authority | `composed::proofs::scenario::scenario_composed_crash_takeover` (third witness) | `A != B` |
| C | The coupling is an **invariant** of the composed machine: `composed_init ==> composed_inv`, `composed_inv /\ composed_next ==> composed_inv`, hence `composed_reachable ==> composed_inv` | `composed::proofs::coupling::theorem_composed_reachable_inv`, `theorem_composed_step_preserves_inv` | the composed transition relation |
| R6 | A concrete routing execution: request `D → B → A → C[token]`, token `C → A → B → D`, then a twelfth step redelivering `D`'s original request after the token has finished moving. The contract exports the whole run — `tr[0] == routing_init_state(a, b, c, d)` and `labels == routing_labels(a, b, c, d)` — which pins the *path* and not just the endpoints: exactly one `RequestCs`, `D`'s, so each forward is caused by the receive before it. Pinning `r0` alone was not enough, because reachability still admitted `A`, `B` and `D` requesting independently and serving their own queue heads | `raymond::proofs::routing_run::scenario_request_and_token_routing` | four distinct nodes |
| R7 | A request outlives the topology it was routed against: after the token moves it is still in `requests` and still deliverable | `raymond::proofs::routing_layer::theorem_delayed_request_survives_token_move` | none |
| R8 | Delivering an arbitrarily delayed request preserves the Raymond invariant and leaves token possession completely unchanged | `raymond::proofs::routing_layer::theorem_delayed_request_delivery_is_safe` | Raymond invariant |

"Reachability" means the hypothesis `reachable(sys)`, i.e. some finite execution
starting from an `init` state ends in `sys`. It is discharged once and for all by
`theorem_reachable_inv`.

### Privilege movement is partitioned by cooperation

A holder that acts hands the privilege on (`ComposedStep::PassToken`, which
requires `pre.own.live.contains(n)` and `believes_holds`); a holder that does
not has it taken (`ComposedStep::SeizeToken`).
`composed::proofs::coupling::theorem_token_movement_is_partitioned` proves there is no
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
(`can_mutate(sys, ..)`), and nothing in `src/ownership/exec_v.rs` connects a guard to it.
What a guard buys is **node-local staleness rejection, not fencing**.

Real fencing has to happen where the effect lands, against authoritative state:
the storage layer refusing a write whose epoch is superseded, or a reply gate
that re-reads the ownership record after a write is durable and before
acknowledging it, refusing the acknowledgement if the record no longer names
this node at this epoch. That check is what turns exclusivity into a property an
outsider can rely on. It is not in this crate, and proving the protocol says
nothing about whether an implementation performs it.
