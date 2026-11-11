# QuePaxa: consensus without timeouts

[QuePaxa](../quepaxa.md) (Tennage, Băsescu, Kokoris-Kogias, Syta, Jovanovic, Estrada-Galiñanes
and Ford, SOSP 2023) is a consensus protocol whose liveness does not rest on timeouts. This
page is what is claimed about the part that is built, and what is not.

What is built is **the paper's abstract algorithm over an ideal threshold broadcast, with
its safety proved; the recorder's register in constant space and the packing of a proposal,
verified; and the concrete protocol (proposer, recorder, a Jetstream service) as plain Rust
that is tested, not proved.** Nothing connects the concrete protocol to the abstract model
by proof, so every safety row below is *conditional on the broadcast's two guarantees*, and
the concrete protocol is covered only by Q12. `src/quepaxa/model_t.rs` is the abstract
model, `src/quepaxa/isr_t.rs` the register's specification, `src/quepaxa/isr_v.rs` the
register, `src/quepaxa/proposal_v.rs` the packing, `src/quepaxa/proofs/` the theorems and
`src/quepaxa/service/` the concrete protocol.

## What is proved

The rows in the first group are about the abstract algorithm. Its two assumptions are the
two guarantees `tcast` gives (`quepaxa::model::round_ok`): every live replica hears from a
majority of the live replicas in each of three steps, and the set relayed in `tcast 2`
(`tcast 3`) is inside every live replica's existent (common) set. The paper (section 4.1.1)
states the second as: `B_i` "is the proposal set input `P_j` of some replica `j`, not
necessarily the same as `i`, such that for all replicas `k`, `P_j ⊆ R_k`", for each
receiver `i`; `round_ok` asks that of every live replica's relay. And fewer than half of
the replicas have crashed.

| ID | Claim | Theorem | Assumes |
| --- | --- | --- | --- |
| Q1 | **Agreement.** In every reachable state, no two replicas have decided differently. The chain `U_i ⊆ C_j ⊆ E_k` for all `i`, `j`, `k` makes a deciding replica's best proposal the best of *every* replica's common set, so every live replica prefers that value next, and no later round proposes another | `quepaxa::proofs::agreement::theorem_agreement` | `round_ok` for every round; fewer than half crashed |
| Q2 | **A decision is everyone's best common proposal.** If replica `i` decides, then for every live replica `j` the best proposal of `C_j` is the one `i` decided on. The heart of Q1 | `quepaxa::proofs::agreement::lemma_a_decision_is_everyones_best_common` | `round_ok`, the invariant (so the sets are non-empty), and that `i` decides |
| Q3 | **Validity.** At every point of every execution, whatever a replica has decided is a value some replica began with | `quepaxa::proofs::agreement::theorem_validity` | none beyond Q1's |
| Q4 | **A decision is locked in.** Once any replica has decided, every replica that has not crashed prefers the decided value, so no later round proposes another | `quepaxa::proofs::agreement::theorem_a_decision_is_locked_in` | none beyond Q1's |
| Q5 | **The invariant is inductive.** Every step, a crash or a round, preserves it, and the initial states satisfy it, so every reachable state does. Q1, Q3 and Q4 are consequences | `quepaxa::proofs::agreement::lemma_step_preserves_inv`, `lemma_init_satisfies_inv`, `theorem_every_reachable_state_satisfies_the_invariant` | none beyond Q1's |
| Q6 | **The model is not vacuous.** The initial states exist, and from any state the invariant allows there *exists* a round, the one in which every replica hears from every live replica, in which every live replica decides. The safety proof is not holding because nothing can ever decide. It is one witness: it does not show a round in which some replica does not decide, or a crash step | `quepaxa::proofs::scenario::lemma_the_initial_states_exist`, `theorem_a_round_with_full_information_decides` | the invariant |
| Q7 | **The abstract model is a `Protocol`** whose `next` is the model's `qp_next` | `protocol_agreement::lemma_quepaxa_next_agrees` | none |

The remaining rows are about the recorder's register.

| ID | Claim | Theorem | Assumes |
| --- | --- | --- | --- |
| Q8 | **The constant-space register is the specified one.** `Isr::record`, four integers, leaves the register standing for the history the specification (the paper's Algorithm 2, one entry per step ever seen) would produce, and answers exactly what the specification answers, **for any history the register stands for**. Discarding old steps loses nothing a reply depends on | `quepaxa::isr::Isr::record`, `Isr::new` (their contracts) | the register stands for the history, which `new` establishes and `record` preserves |
| Q9 | **The step never goes backward**, and **a step the register has left behind is frozen**: recording anything at any step leaves the first value and the aggregate of every step below the current one as they were, so a later request cannot change what an earlier reply was built from | `quepaxa::proofs::isr::theorem_the_step_never_decreases`, `theorem_a_step_left_behind_is_frozen` | the step in question is below the current one (for the frozen row) |
| Q10 | **An aggregate only grows**, and **a value recorded at the current step is in its aggregate**, so the best value a recorder has been given at a step is never missing from, or lowered in, what it reports for it | `quepaxa::proofs::isr::theorem_an_aggregate_never_shrinks`, `theorem_a_recorded_value_is_in_the_aggregate` | the step recorded at is not below the current one (for the second row). Both rows are about the **specification**, and reach the four-integer register only through Q8's relation |

The last two rows are about the concrete protocol.

| ID | Claim | Evidence | Assumes |
| --- | --- | --- | --- |
| Q11 | **A proposal packs into one integer in which larger is better.** `pack` puts priority, proposer and value into a `u128`; comparing packed integers is comparing `(priority, proposer, value)` lexicographically, `unpack` inverts `pack`, and the leader's priority outranks every random one. This is what lets a register that only keeps a `max` aggregate proposals | `quepaxa::proposal::lemma_pack_order`, `lemma_split_is_inverse`, `lemma_the_leader_outranks` (verified) | none |
| Q12 | **The concrete protocol decides one value per slot, in the runs tried.** Proposers run the paper's Algorithm 4 (propose, spread, decide, adopt, catch up) against recorders; the shared contract in [C1](consensus.md) holds of a `QuePaxaLog` under lost calls, crashed minorities and five proposers at once, and on a simulated network. **Tested, not proved:** no theorem connects it to Q1 to Q6, and Appendix B's argument that it provides `tcast` is not formalised | `tests/consensus_contract.rs`, `tests/quepaxa_proposer.rs`, `tests/quepaxa_turmoil.rs` | the failure model below; **a proposer index proposes one value per slot, one slot at a time**, which `Proposer` enforces and a test (`a_proposer_puts_one_value_in_a_slot`) guards, found when two values at one slot decided differently |

## What is not claimed

* **That the concrete protocol provides `tcast`, by proof.** This is the claim that matters
  and the one that is not here. The paper's concrete protocol (its Algorithm 4) is built in
  `src/quepaxa/service/`, but it is plain Rust, and the argument in the paper's Appendix B
  that it gives each replica the three `tcast` outputs with the two guarantees is not
  formalised. **Q1 to Q6 say the idea is sound; Q12 says the implementation behaved in the
  runs tried.** Q8 to Q10 are what a recorder does, and they are the part of that argument
  a recorder's behaviour supplies.
* **Termination, in any form but one.** The paper's liveness is that the protocol decides
  with probability one, under an adversarial scheduler, in under two rounds in
  expectation. This model has no probability. Q6 is only that a round with full
  information decides, which shows the safety proof is not vacuous and is not the paper's
  liveness theorem.
* **Priorities are the label's data.** Any assignment is a step, so every refinement
  chooses correctly. That priorities are random, drawn independently and from a large
  enough range that a tie is negligible, is what makes termination likely and is not
  modelled. Ties here are broken by the proposer's id.
* **The leader fast path and the hedging schedule, in the model.** The designated leader's
  one-round-trip decision and the hedge delay exist in the concrete protocol and are
  exercised by the tests; neither is modelled, and the multi-armed-bandit choice of leader
  is not built.
* **State machine replication, beyond a log of slots.** `QuePaxaLog` runs one instance per
  slot and exposes them as a [`ReplicatedLog`](consensus.md). Batching, pipelining,
  garbage collection of old slots (a recorder's registers are capped, not collected) and
  state transfer are not built.
* **The failure model beyond crashes.** Replicas crash and never return, fewer than half of
  them. A replica that crashes in the middle of a `tcast` is the same as one that crashes
  after it, because a replica heard from by only some is just a replica some majorities
  contain. Byzantine replicas, reconfiguration and recovery are out of scope.
* **Identity beyond the connection's address.** A recorder accepts a call from an address
  on its roster and refuses any other; the roster is an assumption, as Raft's is. Nothing
  authenticates the address.
* **A consumer.** Nothing but the tests uses `QuePaxaLog`. It is not connected to
  [ownership](ownership.md)'s registry.
