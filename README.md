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
and the `believes_holds` / `has_token` split in `src/raymond/model.rs`.

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
| 6 | **Token uniqueness (authority)** - at most one token confers authority per `(ActorId, Epoch)` | `ownership::proofs::tokens::theorem_valid_token_unique_per_actor_epoch` | none |
| 6a | **Token uniqueness (physical)** - at most one token is ever *issued* per `(ActorId, Epoch)` | `ownership::proofs::tokens::theorem_issued_token_unique_per_actor_epoch` | reachability |
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
| C1 | **Election Safety — at most one leader per term.** The headline. Three sentences: a leader won a majority; any two majorities share a member; a member votes once per term | `raft::proofs::election::theorem_election_safety`, `..._reachable` | the Raft invariant, discharged for reachable states by `theorem_reachable_raft_inv` |
| C2 | **Any two majorities of a cluster share a member.** The one piece of real mathematics, and the reason Raft needs no coordinator: two disjoint subsets whose sizes sum past the whole would make a union larger than a set containing it | `raft::proofs::election::lemma_quorums_intersect` | none |
| C3 | **A server votes at most once per term** — sentence three, and the clause `tr_grant_vote`'s guard exists to maintain | `raft::proofs::election::inv_votes_unique`, preserved by `lemma_raft_step_preserves_inv` | the Raft invariant |
| C4 | **A cast vote is never ahead of its voter's term.** Not in the headline argument and the clause without which it does not survive induction: it is what makes a fresh candidacy safe, because a server timing out into term `t + 1` can only be voting there for the first time | `raft::proofs::election::inv_vote_implies_term` | the Raft invariant |
| C5 | **The Raft invariant holds in every reachable state** (`raft_init ==> inv`, `inv /\ raft_next ==> inv`) | `raft::proofs::election::theorem_reachable_raft_inv` | the model's transition relation |
| C6 | **A majority, once won, stays won** — votes only accumulate and the cluster does not change size, so a leader elected at term 7 remains, as a matter of record, the winner of term 7 | `raft::proofs::election::lemma_quorum_survives` | none |
| C7 | **Terms never decrease, and votes are never retracted.** The Raft counterparts of epoch monotonicity (claim 5) and token permanence (P1) — and a vote is physical in the same sense a token is, which is exactly why a returning server must not vote again in a term it has already voted in | `raft::proofs::election::theorem_term_monotone_step`, `theorem_votes_monotone_step` | none |
| C8 | **A lone self-vote is not a majority** in a cluster of more than one. The check that the `>` in the quorum threshold is load-bearing rather than decorative: with `>=` a single server could elect itself | `raft::proofs::election::theorem_a_lone_vote_is_not_a_majority` | a cluster of at least two |
| C9 | **An election actually happens.** A concrete three-server cluster walked from initialisation through a real election, exported with every step named, so C1 is not a safety property of a protocol that never elects anybody | `raft::proofs::scenario::scenario_a_leader_is_elected` | none: the cluster is exhibited |
| C10 | **The election steps refine the model**, in both directions: each executable step fires exactly when the model's transition is enabled, and lands where the model lands | `raft::proofs::refinement::theorem_timeout_step_refines_tr_timeout`, `..._grant_vote_...`, `..._become_leader_...`, `..._step_down_...`, and the `..._refuses_exactly_when_disabled` for each | the couplings, tabulated in `raft::proofs::refinement`'s module docs |
| C11 | **The `u64` tally answers the model's question about the set.** `is_majority` computes `votes + votes > members` with no multiplication to overflow and no subtraction that can go below zero; this is what makes that the same question as `is_quorum` | `raft::steps::is_majority`, `raft::proofs::refinement::theorem_majority_count_is_a_quorum`, `theorem_a_tally_fits_in_the_membership` | that the tally does not double-count a voter and the membership count is not stale — neither of which a step function can check, so both are named |
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
| C30 | **The device is append-only.** No operation moves its tail back: the records that were there are still there, in order, at the same indices. A `Record::Truncate` shortens the *log* and lengthens the device. This is the property that lets the whole store sit on `vendor/pmemlog`, whose abstract state has `append` and `advance_head` and nothing that shortens a tail | `raft::proofs::store::theorem_the_device_is_append_only` | none |
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
| C48 | **An entry persists across a run whenever every leader replicating to its holder already agrees with it there.** The run-level form of C42, and it exists because the *prose* around C42 was wrong in a way the theorem never was: this README said the persistence step was already a theorem, when C42 carries a hypothesis — the replicating leader must already agree at that index — whose discharge for every intervening leader **is** Leader Completeness at the intervening terms. The condition now lives in a signature, quantified over the steps between the two states. **Sufficient, not necessary**: a replication at a `prefix` below the index, where the logs happen to agree at `prefix`, leaves the follower's log untouched and the entry survives whatever the leader holds above it. Sufficiency is all the induction needs. This is the lemma it calls at its inductive step, with the induction hypothesis discharging the quantifier | `raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`, `replication_agrees_at`, `lemma_a_labelled_execution_is_an_execution` | the quantifier in its own statement, which is exactly the induction hypothesis |
| C49 | **Every vote has its judgement on the record, and every recorded vote went to a candidate at least as up to date as the voter's log at that moment.** `tr_grant_vote`'s guard compares against a log *at an instant*; by the time any later theorem asks what the comparison was, the voter has extended, truncated or replaced that log. `Cluster::voted_with` records both sides — the voter's log as it stood and the candidate summary it was weighed against — because storing one side would leave the other to be reconstructed from a state that no longer holds it. The completeness clause matters as much as the judgement clause: a record written in some arms and not others would be silently partial, and a theorem quantified over it would say nothing about the votes it had missed. That is why `tr_timeout`'s self-vote is recorded even though it constrains nothing | `raft::proofs::votes::inv_every_vote_has_its_log`, `inv_a_vote_was_up_to_date`, `inv_a_recorded_log_is_shaped`, `theorem_reachable_vote_inv` | none |
| C50 | **A candidate that won a vote was at least as late, in terms, as every entry in that voter's log** — C43 read off the record rather than off a live state, which is the whole reason the record exists. And **quorum intersection with the judgement attached**: any quorum whatsoever meets the winner's voters in a server for which the record says what its log was when it voted, and that the winner's summary dominated it. Instantiate that quorum with the one C45 produces — the majority that held a committed entry — and the shared voter is a server that both held the entry and judged the winner at least as up to date as its own log. This is the induction's first and third steps joined at a single voter | `raft::proofs::votes::theorem_a_voter_saw_nothing_later_than_the_candidate`, `theorem_a_winner_shares_a_judged_voter_with_any_quorum`, `theorem_a_winner_shares_a_judged_voter_with_any_quorum_reachable` — the reachable wrapper **repeats** the existential rather than forwarding it, because a wrapper's contract is written and not inferred: a caller sees only what the wrapper's own `ensures` says, so forwarding a call does not forward its postconditions | none — but it is a statement about **one state**, and the induction needs the commit-time quorum carried *across the run* to the election, which is C48's conditional job |
| C51 | **A `RequestVote`'s summary is a snapshot of the log it summarises**, for as long as its sender is still a standing candidate of that term — and every judgement on the record quotes a `RequestVote` that is still on the wire. No fifth ghost record was needed for this — `Cluster` already carries four, and the reason is worth naming: **`Cluster::messages` never shrinks**, so the network is already a history variable. The third clause, that a `RequestVote` never names a term its sender has not reached, looks like bookkeeping and is what makes the second *inductive*: the awkward case is `tr_timeout` itself, where a server becoming a candidate of `t` makes every `RequestVote` for `(t, n)` on the wire suddenly have to summarise its new log. The one it just sent does; an **older** one would not, and would sink the invariant. There is no older one, because a server enters a term once — which is that third clause, machine-checked | `raft::proofs::summary::inv_a_recorded_summary_was_on_the_wire`, `inv_a_requestvote_is_not_ahead_of_its_sender`, `inv_a_requestvote_summarises_a_candidate`, `theorem_reachable_summary_inv` | none — and no other invariant bundle is carried either, which is unusual here: the argument is entirely about the network and one server's role |
| C52 | **At the instant it wins, a new leader's own log is at least as up to date as the log of a voter it shares with any quorum whatsoever** — and its last term dominates every entry that voter held. This is C50 with the winner's *log* in place of the pair of integers C50 actually produced. Read C50's conclusion again: `at_least_as_up_to_date(ct, ci, lg)`, where `ct` and `ci` are two numbers that arrived over the network, and nothing anywhere said they had anything to do with the winner's log. The induction's third step was therefore not available, and this README asserted it was. `tr_become_leader` is the right place to state it, because it is the last instant at which the winner is still a candidate and so the last instant at which its summary is its log — afterwards the log grows and the `RequestVote` is spent | `raft::proofs::summary::theorem_a_candidate_is_judged_on_its_own_log`, `theorem_a_candidate_dominates_its_judged_voter`, `theorem_a_candidates_log_is_the_latest_its_voters_saw`, `theorem_the_new_leaders_log_dominates_a_judged_voter`, `theorem_the_new_leaders_log_dominates_a_judged_voter_reachable` — the reachable wrapper repeats its existential, per the rule C50 learned | none |
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
(`can_mutate(sys, ..)`), and nothing in `src/ownership/exec.rs` connects a guard to it.
What a guard buys is **node-local staleness rejection, not fencing**.

Real fencing has to happen where the effect lands, against authoritative state:
the storage layer refusing a write whose epoch is superseded, or a reply gate
that re-reads the ownership record after a write is durable and before
acknowledging it, refusing the acknowledgement if the record no longer names
this node at this epoch. That check is what turns exclusivity into a property an
outsider can rely on. It is not in this crate, and proving the protocol says
nothing about whether an implementation performs it.

## The Raymond layer

`src/raymond/model.rs` models Raymond's distributed mutual-exclusion algorithm as a
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
moving out from under a node that still has authority. `src/composed/model.rs` closes
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

## Raft: the same statement, bought by counting

The failure-model table's first row is the strongest assumption this repository
makes — **ownership records are updated atomically** — and it says outright that
a real deployment has to buy that from consensus, or from a store with
compare-and-swap. `src/raft/` is the first half of buying it.

Raft's **Election Safety** is the exclusivity theorem with two words changed,
and it is bought a completely different way:

```text
ownership:  at most one authoritative owner per epoch, because a single
            atomic registry hands the epoch out
raft:       at most one leader per term, because any two quorums share a
            voter and a voter votes once per term
```

The difference is worth dwelling on, because it is the whole reason both are
here. `ownership::proofs::exclusivity` is **structural**: `may_mutate` is true in
exactly one shape, `Owned { owner, epoch }`, so two owners is not a state the
model can represent, and all the work is in showing the transitions never reach
a bad one. In `raft::model` nothing is structural. A `Cluster` can perfectly well
hold two servers both believing they lead term 7 — that state is representable,
and ruling it out is a **counting** argument over a set that no single
participant can see. Side by side, the two say what a coordinator costs.

The argument is three sentences (C1–C3), and the interesting clause is the one
that is *not* in it. `inv_vote_implies_term` (C4) says a cast vote is never
ahead of its voter's term, and without it the induction fails at the most
ordinary step in the protocol: a server timing out into term `t + 1` votes for
itself there, and only this clause rules out an earlier vote of its own already
sitting in that term.

### The log, and the line between modelled and proved

The model has a log. `tr_client_request` stamps an entry with its leader's term,
`tr_append_entries` carries one entry under the consistency check and truncates
whatever diverged, `tr_advance_commit` advances the commit point under figure
8's restriction, and `tr_grant_vote` carries the `lastLogIndex`/`lastLogTerm`
up-to-date comparison. All four are in `raft_next`, so every run of
`raft_reachable` may use them and every theorem above holds across them.

C12–C19 are what follows from a *single step* — a leader only appends, a follower
agrees before it accepts, an entry is copied rather than invented, a commit needs
a majority of the committing leader's own term. **Log Matching is proved too**
(C26), and getting there needed something the model did not have.

> Ruling out a second entry at the same `(index, term)` is a fact about the
> **run's history**, not about any one state. At `tr_client_request` the leader
> appends at the end of its own log, and nothing in the *state* says no leader of
> that term ever appended at that index before.

So `Cluster` carries ghost fields — four of them now, and each exists because
some question about the *run* has no answer in any single state. `led`, every
`(server, term)` ever led; `created`, every entry any leader ever made, keyed by
the slot naming it and recording its value **and the term of the entry before
it**; `committed` (C44–C47), every entry any leader ever committed, because
`Server::commit` is a count that *retreats*; and `voted_with` (C49–C50), every
vote together with the voter's log as it stood when the vote was cast, because
`tr_grant_vote`'s guard compares against a log that has since moved on.
`created`'s second component is what makes Log Matching an induction rather than
a wish. That second
component is what makes Log Matching an induction rather than a wish: two
servers whose entries at an index carry the same term are reading the same slot,
so they agree on the value *and* on the recorded predecessor, which is the same
question one index down. Repeat to zero.

**Two moments are worth pointing at.** At `tr_become_leader` the freshness clause
(C24) holds because a term being won now has never been led — that is C22, and
the middle of its chain is a fact about a server that may have stepped down long
ago, which is where the history earns its keep. And at `tr_append_entries` the
record survives because the follower's entry at `prefix - 1` has the same term as
the leader's: that is the **consistency check**, already in the protocol since
the log went in, and it turns out to be exactly the guard the proof wants rather
than something added for it (C25).

**The ghost state is not an escape hatch, and that is a theorem** (C21): for any
history whatsoever — all four records, not merely the two this section
introduces — every step still fires from the same real state and lands in the
same real state. A guard that read the history could not satisfy that. The fields
are written and never read, which is what makes them auxiliary variables in the
standard sense.

**Leader Completeness is still not proved**, and the sections that follow are the
six pushes that narrowed the gap rather than six restatements of it. Read them
in order: C39–C43 the ground it stands on, C44–C47 what was committed, C49–C50
what a vote was a judgement of, C51–C52 what the summary that vote judged was a
summary *of*, C53–C54 why the entry was still there to be judged. By the end,
**State Machine Safety holds with one hypothesis** (C46), all three of the
induction's steps are theorems about the same objects, and only the induction
that assembles them is missing.

The fourth record is the last one. C51 needed no fifth, because the thing it
wanted — the candidate's log at the moment it asked — is recoverable from a field
that was already there: `messages` never shrinks, so **the network is a history
variable too**, and the link could be proved instead of recorded.

A follower here will still truncate entries it had committed, which is faithful
Raft — the protection against that is supposed to come from the election
restriction, and the election restriction is now half a theorem (C43) rather than
an absence.

### The ground that induction has to stand on (C39–C43)

`src/raft/proofs/terms.rs` is not that induction. It is the part of it that can
be proved without any new ghost state, and each piece is a theorem rather than a
step of a larger argument that only makes sense once the argument exists.

**The one to read is C41.** A follower that already agrees with the leader at
index `i` keeps its entry at `i` — and the proof splits on where the leader is
writing. If the leader writes at or below `i`, Log Matching says the two logs
agree at *that* index too, so the conditional in `appended_log` fires and the
follower's log is not touched at all. If it writes above `i`, the truncation is
above `i`. Either way the entry stays.

That is the first commit on this branch earning something it was not made for.
The conditional truncation went in because an unconditional one described a step
the service would not take; it turns out to be what makes this theorem true, and
this theorem is what rules out a committed entry vanishing from a voter's log
between the commit and the next election. Under an unconditional truncation a
duplicate `AppendEntries` for an early index deletes the entry, and the
induction has no base.

**C43 is the other half that is provable now**: a voter holding any entry of term
`T` refuses every candidate whose last term is below `T`, so the vote cannot be
granted at all. With C40 that is one line, and it is exactly half of what Leader
Completeness needs — a candidate cannot win on a log that is *behind on terms*.

**What is still missing is the other case**, and it is worth being precise about
which one. When the candidate's last term is at or *above* the voter's, C43 says
nothing: the candidate is not refused, and the committed entry has to be shown
present in its log by a different argument — its own last entry was created by
some leader of a term between the commit's and this election's, and a strong
induction over terms says that leader already held the entry. Three things that
argument needs and this repository does not have:

* a **record of what was committed**. `commit` is a count per server and says
  nothing about which entry a quorum once held.
* a **record of the voter's log at the moment of the vote**, because
  `tr_grant_vote` compares against a log that has since moved on.
* the **strong induction over terms** itself — the part of Raft that took Verdi
  a person-scale Coq development.

C42 and C43 are the two lemmas that induction will call. The induction is not
written, and nothing here pretends otherwise.

### What was committed, as a fact that survives the state (C44–C47)

The first of those three missing pieces is now there. `Cluster` carries a third
ghost field, `committed`, written at `tr_advance_commit` and never removed from,
and `src/raft/proofs/commit.rs` is what it buys.

**Why the state could not say it.** `Server::commit` is a count on one server,
and two things are wrong with it as the subject of a safety property. It says
*how much* is committed, not *what* — and Leader Completeness is a claim about a
particular entry at a particular index. And **it retreats**: C38 proves exactly
when, and proves that when it does, a committed entry was deleted. After that
retreat nothing anywhere in the state records that the entry was ever committed,
so a theorem about committed entries has nothing left to quantify over in the one
state where it matters most.

**The ghost field is still not an escape hatch**, and still as a theorem rather
than a promise: C21's `theorem_history_does_not_gate_the_protocol` now quantifies
over all three histories, so for *any* `created`, `led` and `committed`
whatsoever every step is available from the same real state and lands in the same
real state.

**The record is a recursion, not a comprehension**, and the reason is worth
recording because it is not a matter of taste. In the pinned vstd, `Set` is the
**finite** set type — `ISet` is the unrestricted one — so `Set::new(|k| ..)`
returns `Option<Set<A>>`, `None` when the predicate picks out infinitely many
elements. The obvious comprehension would therefore have to discharge finiteness
at every use. Built up one index at a time, `committed_by` is finite
*structurally*, with nothing to discharge, and the price — membership is no
longer syntactic — is paid once by `lemma_committed_by_members`.

**C46 is the one to read**, and it is worth being exact about what it does and
does not say. State Machine Safety is *"if two servers apply the entry at index
`i`, they apply the same one"*. C46 is that sentence with **one hypothesis
added**: that the two commits agree on the entry's *term*. So the whole of the
remaining risk is concentrated into a single question — can two leaders commit
entries of different terms at one index? — and that question is Leader
Completeness.

See how little is left over. The value half is free: one `(term, index)` names
one act of creation by one leader, which Election Safety (C13) and the creation
record (C22) give unconditionally. Nothing about **values**, **quorums** or
**counting** is missing. What is missing is the argument that a later leader's log
cannot carry a different term at an index a quorum has already agreed on, and
that argument has three steps:

1. the leader of term `T'` won a quorum in `T'`, and that quorum meets the
   commit-time quorum of **C45** in some voter;
2. that voter still held the entry when it voted;
3. so the candidate's log was at least as up to date as a log holding that entry,
   and **C43** closes the case where its last term is *behind*.

**Step 2 is conditional, and its condition is the induction itself** — an
earlier version of this section said step 2 was already a theorem, citing C42,
and that was wrong in a way worth keeping on the record. C42 carries a
hypothesis: the replicating leader must *already agree* with the voter at that
index. Discharging that for every intervening leader **is** Leader Completeness
at the intervening terms. **C48** is the run-level form, and it puts the
condition in the signature rather than in a paragraph, so it cannot be read as
free-standing again.

So: step 1 is a theorem; step 2 is a theorem **with a hypothesis the induction
discharges**; step 3 is half a theorem, because the case where the candidate's
last term is at or above the voter's needs the induction hypothesis at the
intermediate term.

### All three records are now in place — and the induction still is not (C49–C50)

The third, `Cluster::voted_with`, records every vote with **the voter's log as it
stood when the vote was cast** and the candidate summary it was judged against.
`tr_grant_vote`'s guard is a comparison at an instant, and by the time anything
asks what it was, the voter's log has moved on.

C49 promotes that guard from a side-condition on one transition to a fact about
every reachable state, and adds the clause that makes quantifying over the record
mean anything: **every vote is on it**, self-votes included. C50 spends it —
quorum intersection that hands back not just a shared voter but *what that voter
saw*.

It is worth being exact about why this is not the induction. Every theorem here
is about **one state**. The induction relates a commit in term `T` to an election
in a later term `T'`, and it has to compare the quorum that held the entry at
commit time with the quorum that voted at election time **across the run between
them** — which is C48's job, and C48's hypothesis is discharged only by the
induction hypothesis at the intervening terms.

So the materials are all here and the argument that assembles them is not. That
is a smaller gap than it was three pushes ago, and it is still a gap.

### ~~So the materials are all here~~ — they were not, and C52 is the one that was missing

That sentence stood for one push, and it was wrong in a way worth keeping rather
than editing away, because it is the third time the same mistake has been made in
this README and the first time it was found by reading the *signatures* instead of
the prose.

C50 ends with `at_least_as_up_to_date(ct, ci, lg)`. Read it: `ct` and `ci` are
**two numbers**. They came off a `RequestVote`, and nothing in C50, or anywhere
before it, said they had anything to do with the winner's log. So the induction's
third step — *the winner's log dominates what the voter had* — was not a theorem
here; what was a theorem was *the winner's summary dominates what the voter had*,
and a summary is a pair of integers that arrived over the network. As far as the
machine-checked content went, a candidate could have been elected on a summary it
made up.

**C51 closes it without a fifth ghost record.** The first four exist because the
state throws information away. This one does not need to, because `messages`
never shrinks: the `RequestVote` the candidate sent is still there, carrying the
summary, so the link is provable. Both writing transitions make the first clause
true by construction — `tr_timeout` sends the message it records, and
`tr_grant_vote` is *guarded* by the message whose summary it copies — and the
second clause holds because nothing that can change a server's log leaves it a
candidate: `tr_append_entries` demotes its receiver and `tr_client_request` needs
a leader.

The clause that looks like bookkeeping is the one doing the work. *A `RequestVote`
never names a term its sender has not reached* is what makes the snapshot clause
inductive, and the case it settles is `tr_timeout` itself: a server stepping up to
`t` becomes a candidate of `t`, so every `RequestVote` for `(t, n)` on the wire
now has to summarise its new log. The one it just sent does. An **older** one
would not have to, and would sink the invariant — and there is none, because a
server enters a term once. That last sentence is the whole of the third clause.

**C52 is C50 restated about a log**, at `tr_become_leader` — the last instant at
which the winner is still a candidate, and so the last instant at which its
summary is its log. Afterwards the log grows and the `RequestVote` is spent, which
is faithful rather than a limitation.

What is *still* missing is the induction's second step, unchanged: the voter has
to have still held the entry when it voted, which is C48 and its hypothesis. The
difference C52 makes is that when that lands there is now something for it to
meet — a statement about the new leader's log rather than about two integers.

### The second step, and the difference between a translation and a paragraph (C53–C54)

The previous section ends "what is still missing is the induction's second step,
unchanged". That is what C53 and C54 close, and the way they close it is the part
worth reading.

**C48 was never wrong; it was in the wrong language.** It says an entry survives a
run whenever every leader replicating to its holder already agrees with it there,
and its hypothesis is a quantifier over *steps*. The induction hypothesis is a
statement about *leaders of terms*: every leader of a term between the commit and
the election holds the entry. Those are not the same sentence, and for two pushes
this README bridged them with the words "C48's hypothesis is discharged only by
the induction hypothesis at the intervening terms" — which is true, and is a
claim about a translation rather than a translation.

**C53 is the translation, and it turns on a guard.** `tr_append_entries` is the
only transition that can shorten a log, and it requires the leader's
`current_term` to *equal* the follower's. So if a server is known to be at term
`T` or beyond, only a leader at `T` or beyond can write to it. And a member of a
commit's quorum *is* at `T` or beyond, because figure 8's restriction says the
last entry of the committed prefix carries the committing leader's own term, the
quorum member holds that prefix, and no entry's term exceeds its holder's.

That is three short steps, and the middle one is where the figure-8 guard earns
something it is not usually credited with. It is normally explained as ruling out
a specific counterexample — a leader committing an old entry on a bare majority.
Here it is what makes "the quorum is at term `T`" true, and without that the
reduction from steps to leaders does not exist.

**C54 is C48 restated in the induction's own words.** `replicators_hold` is the
tight form — every standing leader that could replicate to the holder right now —
and it carries no term bound, because persistence does not need one;
`leaders_within_hold` is what the induction supplies, Leader Completeness over the
closed range `[t0, t1]`; and `theorem_a_commit_quorum_still_holds_it` composes
that with the commit-time quorum. The hypothesis is still a hypothesis — an
intervening leader that does *not* hold the entry will truncate it away, which is
faithful Raft — but it is now the induction hypothesis rather than something a
sentence asserts is equivalent to it.

**The upper bound is there because the first version did not have it.** `@codex`
found that, and the finding is the most interesting thing in the push. Strong
induction on the election's term `T` supplies Leader Completeness for terms
*below* `T`; a predicate reading "every standing leader of a term at or past `t0`"
demands it for terms **above** `T` too. Those leaders exist — nothing in this
model orders terms cluster-wide, since `tr_grant_vote` only requires the request's
term to be at least the voter's own, so a leader of a far higher term can be
running elsewhere while a delayed campaign at `T` is still collecting votes. They
are *harmless*, because `tr_append_entries` needs equal terms and so they cannot
reach a voter at a lower term. But the old predicate demanded they hold the entry
anyway, and C54 could not have been discharged from the induction hypothesis
without assuming Leader Completeness at terms the induction had not reached.

A hypothesis stronger than the argument needs is not a safe over-approximation
when the hypothesis is what somebody else has to supply. That is the general form
of the lesson, and it is the fourth time on this branch that the machine-checked
content was fine and the *claim about* it was not.

**Where the two bounds come from is asymmetric, and worth reading.** The lower one
is established at the window's start — C53 puts the quorum at `T` or beyond, and
terms never fall. The upper one is established at the window's **end**: in the use
the induction will make of this, the window closes when the voter grants its vote
in term `t1`, and `tr_grant_vote` requires the request's term to be at least the
voter's own, so the voter is at `t1` or below *then* — and monotonicity carries it
backwards over the whole window. The upper bound is not an extra assumption about
the run; it is the vote.

**And the `t1` endpoint is an open obligation**, stated in the theorem's own docs
rather than deferred to a paragraph: the range is closed, so the induction needs
its case at `t1` before it may use C54 at `t1`, and a leader of `t1` *can* exist
before this voter has voted in `t1`, because winning `t1` needs *a* quorum and not
this one. Either the induction establishes `t1` first, or it restricts the window
to end strictly before any leader of `t1` exists. This push does not settle which.

**So all three steps now speak about the same objects** — an entry, an index, a
term, a log:

1. a quorum held the entry at commit time (**C45**);
2. a member of that quorum still held it when it voted (**C54**, given Leader
   Completeness at the intervening terms);
3. the winner's own log dominates that voter's (**C52**).

What is left is a strong induction over terms and nothing else. That is a claim
about shape, and it is worth being explicit that it is not a claim that the
induction is proved. It is not. But the previous four sections each ended by
naming a missing *object* — a record, a link, a translation — and this one does
not: there is no missing object, only the argument.

**C38 is what that gap costs, stated concretely.** Because the model may not
assume that state unreachable, it has to handle it, and handling it means a
follower's commit index can retreat — one Raft property given up to keep
another. C38 confines the retreat to exactly the state Leader Completeness would
rule out, so the gap has a boundary and a name rather than being a general
caveat. Closing that proof closes this too.

**There is no reconfiguration**, deliberately: membership is fixed and no
transition changes it. Joint consensus is a separate protocol with its own
well-known unsafety, and modelling it half-way would be worse than not modelling
it.

### A log that truncates, on a device that cannot

Raft's log shrinks. Figure 2's rule 3 deletes a conflicting entry and everything
after it, and `appended_log` is that rule. Every durable log worth trusting
*grows*: `vendor/pmemlog`'s abstract state offers `append` and `advance_head` —
put bytes on the end, or forget bytes from the front — and nothing that takes
the tail back.

That is not a gap in the vendored crate. It is what makes a crash-consistent log
cheap: an append that either happened or did not is one write, while a tail that
moves backwards is a state the device has to be able to be caught in the middle
of.

`src/raft/store.rs` reconciles them in four lines of idea:

1. the device holds a sequence of `Record`s, and only ever grows;
2. a truncation is a *record*, `Record::Truncate { len }`, appended like any other;
3. the log is `replay` of the records, computed on recovery;
4. therefore the physical log is append-only and the logical log truncates.

C27–C31 are what that buys. The one to read first is **C27**, and it is worth
reading for how boring its proof is: the recovery case of "memory agrees with
the device" is discharged by the transition's own definition, because
`store_recover` *defines* the recovered log as `replay` of what survived. A
design where recovery has to reconcile two sources is a design where that proof
is the hard one. Here there is one source.

**C29 is where the protocol and the storage layer turn out to want the same
thing.** Accepting a replicated entry costs two records when the entry at
`prefix` conflicts, and **zero** when it does not — the no-conflict branch
writes nothing at all. That branch exists because of C25: the conditional
truncation is what keeps the creation record true, and it is what makes Log
Matching provable. It is also, it turns out, what makes the common case — a
duplicate or reordered `AppendEntries`, which under heartbeats is most of them —
a read and no write. The check that makes the protocol safe is the check that
makes the steady state free.

#### The commit point, and the one Raft property this model gives up

Raft's commit index is monotone. This model's is not, in exactly one case, and
the case is worth understanding because it is the shape of what is still
missing.

`accepted_commit` clamps the commit index to the length of the log. A follower
with `commit = 5` told to replace the entry at index 0 ends with a one-entry
log, and something has to give: either its commit point still says 5 — naming
four entries that no longer exist — or it retreats to 1. **This model
retreats.** A commit point past the end of the log is a state no later reader
can make sense of, since every query about what has been applied reads off the
end; a commit point that went backwards is a broken promise, but a readable one,
and the breach is visible rather than latent.

An earlier version of this comment claimed *both* "never backwards" and "never
past the end of the log", which cannot both hold. That was a review finding and
it was correct.

What replaced it is **C38**, which says precisely when the retreat happens:
commit is monotone whenever the truncation point is at or above it — every step
of a healthy cluster — and when it retreats, the leader asked the follower to
delete an entry it had **committed**. Not "commit might go backwards sometimes",
but *"commit goes backwards only in the state whose unreachability is the
missing theorem"*.

That missing theorem is Leader Completeness. When it lands, C38's hypothesis
becomes vacuous and monotonicity becomes unconditional. Until then the model may
not treat the case as unreachable — so it handles it, and says how.

#### The byte layer, and the theorem it exists for

C27–C31 are about *records*; pmemlog appends *bytes*. `src/raft/wire.rs` is the
layer between, and it exists to make one statement provable.

C28 says a crash leaves a prefix of the **records**. A device leaves a prefix of
the **bytes**, and a byte prefix can cut a record in half. Without a theorem
joining the two, C28's hypothesis is an assumption about how writes land wearing
the clothes of a definition.

**C32 is that theorem**: for every `k` at all — not multiples of seventeen —
`parse(encode(rs).take(k)) == rs.take(k / 17)`. The tear may land in the middle
of a `u64`. That is what the fixed width buys, and it is why the format is
seventeen flat bytes rather than a length prefix or a varint: a log whose
recovery depends on the parser being clever is a log whose recovery has a bug in
it. There is no checksum here either, because pmemlog CRCs what it stores and a
second one at this layer would add bytes and no guarantee.

The chain is then: a device keeps a byte prefix (C32) → that is a record prefix
(C28) → `replay` of a record prefix is a log the store had (C27). No step asks
the device for more than *"you keep a prefix of what I wrote"*.

#### The line a crash may not cross

C27 and C28 as first written said *"a crash keeps a prefix"* — which permits
the **empty** prefix. After any completed append, a restart could discard every
record the store had reported durable, including entries a leader committed on
the strength of that acknowledgement. That is strictly weaker than the device
underneath: pmemlog's append shows a crash either the log before it or the log
after it and nothing older. A layer whose whole job is to be no weaker than
pmemlog was weaker than pmemlog, and no test caught it because every crash the
suite simulates happens to be an honest one.

`Store` carries `durable`, and the model now separates **what the device
offers** — `store_write`, one record on the device with the line unmoved, and
`store_sync`, the only thing that moves it — from **what a caller gets**:
`store_append` and `store_truncate`, durable before they return, which is what
`LogStore` already promised in prose. `theorem_an_append_is_a_write_then_a_sync`
is the proof that the promise is kept by the two primitives and not by a third
thing the model invented.

**C35 is the theorem that buys.** Read the second clause: the line never
retreats *and* everything below it is unchanged record for record. A store that
kept the right *number* of records while rewriting one of them would satisfy the
first and fail the second. And read the third statement in it, which is where
this module meets Raft's commit rule — a follower that answers `Accepted` has
written the entry down, so a leader counting that answer toward a majority is
counting something that cannot be taken back. Remove the durability hypothesis
and the conclusion fails immediately; that is what it is there to show.

#### Compaction has a middle state

`theorem_compaction_replays_the_same` says `replay(compacted(log)) == log`,
which is true and licenses nothing. It covers the case where the rewrite has
**already** replaced what came before — the case that needs no proof. The
procedure is two steps on an append-only device, write the new generation and
then reclaim the old one, and a crash between them leaves
`old_records ++ compacted(log)`, which replays to `log + log`. Every entry
twice.

`compaction_batch` is a leading `Truncate { len: 0 }` and then the log, and that
marker is what makes the staged generation **self-sufficient**: it clears
whatever preceded it, so the device replays to `log` with the old records still
there and to `log` once they are gone. Both crash views agree, which is what
turns the reclaim from a change into a no-op (C36).

It has to land atomically, and that is not a preference. A crash *inside* the
batch leaves the marker — which has already cleared everything — plus a
*prefix* of the log, so recovery produces a shorter log than the store had.
**C36b proves the rewind is exact**: a crash after `k` of the batch's entries
recovers exactly `k`, because a partial batch is not arbitrary damage, it is the
compaction of a shorter log. Data loss on an operation whose entire purpose is
to change nothing.

So the batch is one `store_write_batch`: on pmemlog a single `append`, whose
crash view is the log before it or the log after it and nothing between. **That
is the one property of the device this design asks for and cannot itself
check**, and it is the property pmemlog was built to have. `RecordLogStore`
installs the batch in one step; `a_batch_written_one_record_at_a_time_would_rewind_the_log`
walks every cut inside it and checks the real `compact` produces none of them.

This was a review finding and it was a bug in the *code*, not the model: the
executable store appended the batch a record at a time under a doc comment
saying it must not. The model had no word for "atomically", which is why the
two could drift with nothing to catch it — `store_write_batch` is that word.

Two limitations, stated rather than assumed away:

* **The 64-bit boundary.** `Record`'s fields are `nat`, because the model's
  terms are unbounded and a model that caps them has an overflow bug the
  protocol does not. Bytes are not unbounded. `records_fit` is therefore a
  **guard on the write transitions and a clause of the store invariant**, not
  merely a precondition on C32 and C33 — stated only on the theorems it would
  filter which theorems may be *invoked* while leaving the unencodable state
  reachable, so the store half and the wire half could not be composed at all
  (C37). A cluster reaching term 2^64 now has a store that cannot advance,
  rather than one that silently writes the wrong record.
* ~~**The device grows even when the log does not**, because nothing schedules
  compaction~~ — **closed.** A follower thrashing between two leaders writes a
  record per round, and `worth_compacting` now fires at
  `records > 2 * (entries + 1)`: amortised O(1), with the bound asserted every
  round over sixty rounds of the worst shape. C31 says the rewrite is sound;
  `compact_if_worthwhile` is what makes it happen.
* **Nothing in `src/` depends on `vendor/pmemlog` yet**, and the reason is no
  longer "the executable layer does not exist" — `replay_exec`, `encode_exec`
  and `parse_exec` do. What is missing is a **device**, and the obstacle there is
  not an interface but a crash model: pmemlog's `persistence_chunk_size` is 8 and
  a write must be safe for *any subset* of 8-byte chunks having flushed, which
  **POSIX does not promise** for a write crossing a chunk. An `fsync`-per-write
  file would not satisfy it. That needs a target platform — real PM, `O_DIRECT`
  with aligned single-sector writes, or an explicitly weaker documented device.
  Until one exists, pmemlog's two corruption assumptions are not assumptions of
  anything proved here.

### The consensus service

`src/raft/service.rs` serves it: `request_vote` with the up-to-date comparison,
`append_entries` with the consistency check and the truncation, `heartbeat`,
`standing`. As in the ownership service, **no method takes a server number** —
the candidate asking for a vote is whoever opened the connection — and that
matters more here, because a protocol whose entire safety argument is "a server
votes once per term" is exactly the one you do not want taking the voter's or the
candidate's identity from a field. Standing for election, tallying, taking a
term, appending a command and advancing the commit point are inherent methods
rather than RPCs, for the reason `force` is inherent on the ownership registry: a
peer that could trigger them could keep the cluster in a permanent election, or
declare somebody's entry committed.

The log itself is a **trait**, `LogStore`, with `MemoryLogStore` as the mock the
tests run against. A real log is a file with a format, an fsync policy and a
truncation story, none of which belongs in the protocol; the protocol's own
behaviour is exactly what you want to exercise without a disk in the way.

**Replies are protocol steps too.** Raft's term rule is about *"RPC request or
response"*, and a `Ballot::Refused(2)` reaching a term-1 candidate carries the
same news as an inbound request would. `count_ballot`, `observe_standing` and
`observe_appended` are that side of it, and they take the reply itself rather
than a summary: there is no way into a candidate's tally except by handing over a
`Ballot::Granted` for the term being stood in. A method taking only `(peer,
term)` would let a caller count a peer that refused — a majority assembled out of
nothing, and a leader the model never elected.

**And the same durability finding, arrived at from the other end.** Raft's own
figure 2 requires `currentTerm` and `votedFor` on stable storage *before
responding to RPCs*. That is the requirement the ownership registry's epoch floor
turned out to have, and it is load-bearing for the same reason: a server that
grants a vote, replies, restarts having forgotten, and grants again has voted
twice in one term — two candidates can then each hold a majority, and Election
Safety is gone. Not because the proof is wrong, but because `already_voted` was
reported `false` when the model's `has_voted` was true. `tests/raft_election.rs`
runs that in both directions: a restarted voter that refuses the second request,
and a forgetful one that grants it and elects two leaders.

## Repository layout

```text
distributed-ownership/
├── Cargo.toml              one crate; the services are behind a non-default feature
├── rust-toolchain.toml
├── README.md
├── src/
│   ├── lib.rs
│   ├── ownership/          exclusive mutable ownership with epoch fencing
│   │   ├── model.rs        state space + transition relation (no specification)
│   │   ├── spec.rs         may_mutate, tokens, the system invariant
│   │   ├── fencing.rs      current_epoch, valid_fence, staleness
│   │   ├── transfer.rs     the multi-step handover and its lemmas
│   │   ├── steps.rs        the transitions as executable u64 functions
│   │   ├── exec.rs         the u64 fence check a node runs on its own belief
│   │   ├── service.rs      the protocol over Jetstream RPC   [feature = "service"]
│   │   └── proofs/
│   │       ├── invariant.rs    init ==> inv, inv /\ next ==> inv, reachable ==> inv
│   │       ├── properties.rs   structural, temporal and capability properties
│   │       ├── exclusivity.rs  claim 1
│   │       ├── fencing.rs      claims 2, 3, 5
│   │       ├── transfer.rs     claim 4
│   │       ├── tokens.rs       claim 6
│   │       ├── adversarial.rs  concrete adversarial executions
│   │       └── refinement.rs   steps.rs agrees with the model's tr_* transitions
│   ├── raymond/            Raymond's mutual-exclusion routing layer
│   │   ├── model.rs
│   │   └── proofs/{routing_layer.rs, routing_run.rs}
│   ├── composed/           ownership and Raymond as one machine
│   │   ├── model.rs        the coupling enforced by guards, not assumed
│   │   └── proofs/{coupling.rs, scenario.rs}
│   └── raft/               consensus: terms, votes, quorums, the log
│       ├── model.rs        state space + transition relation
│       ├── steps.rs        the election decisions as executable u64 functions
│       ├── store.rs        a log that truncates, on a device that cannot
│       ├── wire.rs         the record encoding, and what a torn write leaves
│       ├── service.rs      the protocol over Jetstream RPC   [feature = "service"]
│       └── proofs/
│           ├── election.rs     Election Safety, via quorum intersection
│           ├── history.rs      the ghost record, and Log Matching out of it
│           ├── log.rs          what one replication step gives you (and what it does not)
│           ├── terms.rs        term structure, entry durability, the election restriction
│           ├── commit.rs       what was committed, and State Machine Safety minus one hypothesis
│           ├── votes.rs        what a vote was a judgement of
│           ├── summary.rs      the summary a voter judged, tied back to the log it summarised
│           ├── persistence.rs  why the entry was still there when the voter judged it
│           ├── refinement.rs   steps.rs agrees with the model's tr_* transitions
│           ├── scenario.rs     a run in which an election actually happens
│           ├── store.rs        recovery is exact; a crash can only rewind
│           └── wire.rs         cut the bytes anywhere; a record prefix comes back
├── tests/
│   ├── scenario_body/mod.rs    the executable protocol + the runtime oracles
│   ├── turmoil_ownership.rs    named stories, each with an expected ending
│   ├── turmoil_scenarios.rs    the blind seed search + the regression replay
│   ├── protocol_lines.rs       the search over what arrives at the registry
│   ├── ownership_handover.rs   the service's headline story   [feature = "service"]
│   ├── ownership_durability.rs the restart that must not rewind [feature = "service"]
│   ├── raft_election.rs        a split vote elects one leader  [feature = "service"]
│   ├── raft_log.rs             the consistency check and figure 8 [feature = "service"]
│   ├── raft_wire.rs            the service over a simulated network [feature = "service"]
│   └── seeds/scenarios.txt     seeds that once broke something
├── vendor/
│   └── pmemlog/                Microsoft's verified persistent-memory log
│       ├── README.md           provenance, omissions, and its six assumptions
│       ├── LICENSE.txt         upstream's MIT licence, unaltered
│       └── src/                unmodified upstream source
└── .github/workflows/verify.yml
```

**One directory per algorithm, and each one holds the whole of that algorithm**
— its model, its proofs, its executable steps and its service. A protocol whose
proof lived in one crate and whose implementation lived in another is a protocol
where the two can drift without anything noticing; here they are compiled
together and the service calls the functions the proofs are about.

**The services are behind a feature that is off by default**, and that is what
makes one crate workable. `verus --crate-type=lib src/lib.rs` and `cargo verus
verify` both run with default features, so the verified build's dependency graph
is `vstd` and nothing else — no Jetstream, no async runtime for Verus to be
asked about, and no need for a single `#[verifier::external]` to keep service
code out of the proofs. Turn the feature on and the same modules compile against
the same verified step functions, under `cargo +stable`: `rust-toolchain.toml`
pins the Rust release the Verus build was made against so the **proofs** verify,
not so a service is stuck on it.

This differs from a plain `proofs/` directory at the repository root: Verus
verifies a *crate*, so every proof file has to be a module of that crate.
Keeping them under `src/{algorithm}/proofs/` is the ordinary Rust way to express
that; a top-level `proofs/` would need `#[path = "../proofs/..."]` attributes
for no benefit.

**Verified executable code** is in the `steps.rs` and `exec.rs` of each
algorithm: small `u64`-valued functions, each with a postcondition stated in
terms of that algorithm's model and a theorem in its `proofs/refinement.rs`
discharging it. **Unverified executable code** is in each algorithm's
`service.rs` and under `tests/`, and it is unverified in the plain sense that
Verus never compiles it — the feature is off when the proofs are checked — not
in the sense that an escape hatch waves it through. `exec` offers **queries
only**: a `FenceGuard` has private fields, a single
constructor and no setter, so its ghost view is fixed at construction. Were it
mutable — by a `bump` method or by assigning to a public field — its view could
drift from `Owned(A, e)` to `Owned(B, e + 1)`, exactly the atomic ownership
assignment this model refuses to admit. Observing a new generation means
constructing a new guard. Making a
guard follow the protocol needs a refinement of the *node* side; the registry
side is `src/ownership/steps.rs`.
Everything else in the crate is specification or proof.

Specification and proof code are kept apart from the model: `src/ownership/model.rs`
defines only the state space and the transition relation and does not import the
specification layer, so a specification cannot be quietly weakened to fit the
model.

## The protocol as a Jetstream service

Everything above is a model and a simulation of it. `src/ownership/service.rs` is the
protocol served over [Jetstream](https://github.com/sevki/jetstream) RPC — a
`#[service] trait Ownership` with `poll`, `acquire`, `write`, `begin_transfer`
and `release`, implemented by a `Registry` that performs the fence with
`ownership::exec::FenceGuard`.

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
`tests/ownership_durability.rs` runs the same handover against a floor
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
`distributed_ownership::ownership::steps`, and store what comes back; those
functions are
executable `u64` code with postconditions stated in terms of the model, and
`ownership::proofs::refinement` is where the postconditions are tied to `tr_acquire`,
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
module docs of `ownership::proofs::refinement` tabulate which part of the service
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
VERUS=0.2026.09.20.aef82ed
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
it does — which is exactly the gap `src/ownership/steps.rs` closes for the Jetstream
service in `src/ownership/service.rs`, and the reason the two coordinators are worth
keeping side by side.

**Would the oracles notice?** A suite that cannot fail is indistinguishable
from one that passes, so `oracles_catch_an_unfenced_coordinator` runs one story
twice with a single bit changed — the coordinator stops checking writes against
the registry — and requires the oracles to *reject* the second run. Same
actions, same seed, same network, same oracles; what separates them is exactly
the check `src/ownership/exec.rs` says has to happen where the effect lands.
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
precisely the asymmetry `src/ownership/exec.rs` documents.

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

**Machine-checked** (every `proof fn` in `src/{algorithm}/proofs/` is checked by Verus in
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
  holding the token;
* Raft: Election Safety (C1–C11), Log Matching (C26) and the single-step log
  properties (C12–C19);
* Raft's term structure and the election restriction: a log's terms never
  decrease and none exceeds its holder's own, so the last term is the largest;
  **a follower that already agrees with the leader at an index keeps its entry
  there**, which is what makes figure 2's *conditional* truncation load-bearing
  rather than merely faithful; and a candidate behind on terms cannot collect a
  vote at all (C39–C43);
* **State Machine Safety, with exactly one hypothesis** — that two commits at an
  index agree on the entry's *term* (C46). The value half is unconditional,
  because one `(term, index)` names one act of creation by one leader. Nothing
  about values, quorums or counting is missing;
* what a commit was: a majority held **that entry at that index**, entry for
  entry rather than as a prefix length, and the record of it never shrinks
  (C44–C47, C50, C52);
* what a vote was a **judgement of**: every vote is on the record with the
  voter's log as it stood, and every recorded vote went to a candidate at least
  as up to date as that log (C49) — and what the summary it was judged against
  was a summary *of*, so that a winner's own log, rather than a pair of integers
  off the network, is what dominates its voters' logs (C51–C52);
* why the entry was still there to be judged: a commit's quorum is already at the
  commit's term, so only a leader at or past it can ever overwrite them, and the
  entry survives for as long as those leaders hold it (C53–C54). The condition is
  the induction hypothesis, stated as one;
* the durable log: recovery is exact, a crash can only rewind, and a byte
  prefix of the device parses back to a record prefix — so figure 2's suffix
  deletion is implementable on a device that deletes nothing.

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

* **The durable log is not wired to a device**, and the reason has moved. The
  executable layer exists — `replay_exec`, `encode_exec` and `parse_exec` refine
  their spec counterparts, and verifying them found two bugs no test could have.
  What is missing is a device, and the obstacle is a **crash model**, not an
  interface: pmemlog's `persistence_chunk_size` is 8 and a write must be safe for
  *any subset* of 8-byte chunks having flushed, which POSIX does not promise for
  a write crossing a chunk. Until a device supplies it, pmemlog's two corruption
  assumptions are not assumptions of anything proved here.
* ~~**Compaction is proved sound and is not scheduled**~~ — **closed** by
  `worth_compacting` at `records > 2 * (entries + 1)`. Left struck through rather
  than deleted because it stood here for three PRs after the policy landed.

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
  handled, is `src/ownership/steps.rs` and `src/ownership/proofs/refinement.rs` — see rows E1 to E6.
  What remains unrefined is the *node* side: `src/ownership/exec.rs` still offers no way
  to advance a node's fence guard, only to consult it, so that no executable API
  can perform a handover the model does not;
* the actual actor runtime: networking, persistence, and the code that obeys the
  protocol. Verifying the protocol says nothing about whether an implementation
  follows it. `tests/` now exercises a hand-written one against the model's own
  theorems on a simulated network (see
  [Network resiliency](#network-resiliency-the-model-run-for-real)), which is
  evidence rather than proof: nothing machine-checks that the coordinator in
  `tests/` refines the transition relation in `src/`;
* **Raft's Leader Completeness**, and with it State Machine Safety
  unconditionally. This is now a *much* smaller gap than the sentence that used
  to sit here, and worth stating precisely rather than as a caveat.

  **State Machine Safety already holds with one hypothesis** (C46): that two
  commits at an index agree on the entry's *term*. So the whole of the remaining
  risk is one question — *can two leaders commit entries of different terms at
  one index?* — and that question is Leader Completeness.

  **All three ghost records the induction needs are in place**: what was
  committed (C44–C47), the voter's log as it stood at the vote (C49–C50), and the
  creation/leadership history Log Matching is built on (C20–C26). No fifth was
  needed for the summary that vote was judged against, because `messages` never
  shrinks (C51). So are the theorems the induction will call:

  * **C45** — a majority held the entry at commit time, entry for entry;
  * **C54** — that voter still held it when it voted. Still *conditional*, and
    the condition is the induction hypothesis over the **closed range** of terms
    from the commit's to the election's: a quantifier over the leaders of those
    terms, rather than C48's quantifier over steps with a paragraph claiming the
    two are the same thing. C53 performs the translation. **The upper endpoint is
    an obligation, not a formality** — a leader of the election's term can exist
    before this voter has voted in it — so the induction must settle its own case
    at that term before using C54 there, or close the window earlier;
  * **C50/C52** — the winner's voters meet any quorum, with the judgement
    attached, and the judgement is about the winner's **own log**. C50 alone was
    not enough for this step and the earlier version of this list said it was:
    its conclusion is about the pair of integers a `RequestVote` carried, and C52
    is what ties those to the log;
  * **C43** — a candidate *behind* on terms is refused.

  What is missing is the **strong induction over terms** that assembles them.
  Every theorem above is about one state or one step; the induction relates a
  commit in term `T` to an election in a later `T'` and has to carry the
  commit-time quorum *across the run between them*, which is exactly what C48's
  hypothesis is. Until it lands, the registry's contents agree *where servers
  overlap* but are not yet guaranteed to survive a leader change — the half of
  the atomicity assumption that is load-bearing for `System::actors`;
* **reconfiguration.** Membership is fixed. Joint consensus is a real and
  well-known source of Raft unsafety and is not attempted here.

### The holder graph is a tree, and now says so

`ray_unique_token` and `ray_token_exists` together say there is exactly one
root. That is not the same as the holder graph being a tree: nothing stopped a
set of non-root nodes from pointing at each other in a cycle, off to one side of
the real root. `ray_init` permitted it too — it forbids only a non-root pointing
at *itself*, so `A → B`, `B → A` beside a root `C → C` satisfied it.

The consequence was visible in `src/raymond/model.rs`'s own opening comment: "requests
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

The proofs in `src/` use no `assume`, `admit`, `external_body`, `axiom`, or any
other way of asserting something Verus did not check. CI enforces it by grep on
every pull request.

### `bit_vector` and `nonlinear_arith` are not escape hatches

`raft::proofs::wire` uses both: `by(bit_vector)` for the little-endian round
trip, `by(nonlinear_arith)` for the division bookkeeping in C32. Neither asserts
anything. They hand the goal to a *different decision procedure* — bit-blasting
for the first, a nonlinear arithmetic solver for the second — because the
default encoding is poor at bits and at multiplication. The obligation is
discharged, not waived: a false goal fails under either.

They are named here because "no escape hatches" should mean something precise,
and a reader who greps for `assume` should also know what `by(...)` does.

### The one exception, and it is not in `src/`

`vendor/pmemlog` is [Microsoft's verified persistent-memory
log](https://github.com/microsoft/verified-storage), vendored unmodified, and it
has six. Three are I/O primitives and a CRC computation — the code that actually
touches the device, with nothing beneath it to verify against. **Two are
assumptions about the physical world**, and anything this repository ever proves
on top of that log is conditional on them:

* `axiom_bytes_uncorrupted`: if `y` is the CRC of `x`, and a read gives back
  `x_c` and `y_c` with `y_c` the CRC of `x_c`, then `x_c == x`. This says a CRC
  detects the corruptions the device actually produces. It is not provable and
  it is not free: a device whose corruptions are CRC-preserving violates it, and
  every guarantee resting on it.
* `axiom_corruption_detecting_boolean`: the two flag values `CRC(b"0")` and
  `CRC(b"1")` are far enough apart that corruption cannot turn one into the
  other.

These are stated here rather than buried because the repository's rule is that
an assumption may be *an explicit documented part of the system model* and may
not be a way of making verification pass. These are the former; they are
enumerated one by one in `vendor/pmemlog/README.md`; and the CI grep covers
`src/` and not `vendor/` for exactly this reason, with the reason written into
the workflow.

Nothing in `src/` depends on `vendor/pmemlog` yet. When something does, this
section is where the conditional lives.

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

That grep now runs over a `src/` that also holds two Jetstream services, and it
still means what it said. The services are behind a feature that is off when the
proofs are checked, so Verus never compiles them and none of them needs a
`#[verifier::external]` to be kept out — which is why the feature exists rather
than being a packaging preference. If a service ever did need one, this grep
would fail the build, and that is the right outcome: an unverified module inside
a verified crate should be excluded by the build, not waved through by an
attribute.
