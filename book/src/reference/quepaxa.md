# QuePaxa: consensus without timeouts

[QuePaxa](../quepaxa.md) (Tennage, Băsescu, Kokoris-Kogias, Syta, Jovanovic, Estrada-Galiñanes
and Ford, SOSP 2023) is a consensus protocol whose liveness does not rest on timeouts. This
page is what is claimed about the part that is built, and what is not.

What is built is **the paper's abstract algorithm over an ideal threshold broadcast, with
its safety proved, and the recorder's register in constant space, verified against its
specification.** What is **not** built is the concrete protocol that is supposed to provide
that broadcast, so every safety row below is *conditional on the broadcast's two
guarantees*. `src/quepaxa/model_t.rs` is the abstract model, `src/quepaxa/isr_t.rs` the
register's specification, `src/quepaxa/isr_v.rs` the register, and
`src/quepaxa/proofs/` the theorems.

## What is proved

The rows in the first group are about the abstract algorithm. Its two assumptions are the
two guarantees `tcast` gives (`quepaxa::model::round_ok`): every live replica hears from a
majority of the live replicas in each of three steps, and the set relayed in `tcast 2`
(`tcast 3`) is inside every live replica's existent (common) set. And fewer than half of
the replicas have crashed.

| ID | Claim | Theorem | Assumes |
| --- | --- | --- | --- |
| Q1 | **Agreement.** In every reachable state, no two replicas have decided differently. The chain `U_i ⊆ C_j ⊆ E_k` for all `i`, `j`, `k` makes a deciding replica's best proposal the best of *every* replica's common set, so every live replica prefers that value next, and no later round proposes another | `quepaxa::proofs::agreement::theorem_agreement` | `round_ok` for every round; fewer than half crashed |
| Q2 | **A decision is everyone's best common proposal.** If replica `i` decides, then for every live replica `j` the best proposal of `C_j` is the one `i` decided on. The heart of Q1 | `quepaxa::proofs::agreement::lemma_a_decision_is_everyones_best_common` | `round_ok` |
| Q3 | **Validity.** At every point of every execution, whatever a replica has decided is a value some replica began with | `quepaxa::proofs::agreement::theorem_validity` | none beyond Q1's |
| Q4 | **A decision is locked in.** Once any replica has decided, every replica that has not crashed prefers the decided value, so no later round proposes another | `quepaxa::proofs::agreement::theorem_a_decision_is_locked_in` | none beyond Q1's |
| Q5 | **The invariant is inductive.** Every step, a crash or a round, preserves it, and the initial states satisfy it, so every reachable state does. Q1, Q3 and Q4 are consequences | `quepaxa::proofs::agreement::lemma_step_preserves_inv`, `lemma_init_satisfies_inv`, `theorem_every_reachable_state_satisfies_the_invariant` | none beyond Q1's |
| Q6 | **The model is not vacuous.** From any state the invariant allows there is a step, and in a round where every replica hears from every live replica *every live replica decides*. The safety proof is not holding because nothing can ever decide | `quepaxa::proofs::scenario::theorem_a_round_with_full_information_decides` | the invariant |
| Q7 | **The abstract model is a `Protocol`** whose `next` is the model's `qp_next` | `protocol_agreement::lemma_quepaxa_next_agrees` | none |

The remaining rows are about the recorder's register.

| ID | Claim | Theorem | Assumes |
| --- | --- | --- | --- |
| Q8 | **The constant-space register is the specified one.** `Isr::record`, four integers, leaves the register standing for the history the specification (the paper's Algorithm 2, one entry per step ever seen) would produce, and answers exactly what the specification answers, **for any history the register stands for**. Discarding old steps loses nothing a reply depends on | `quepaxa::isr::Isr::record`, `Isr::new` (their contracts) | the register stands for the history, which `new` establishes and `record` preserves |
| Q9 | **The step never goes backward**, and **a step the register has left behind is frozen**: recording anything at any step leaves the first value and the aggregate of every step below the current one as they were, so a later request cannot change what an earlier reply was built from | `quepaxa::proofs::isr::theorem_the_step_never_decreases`, `theorem_a_step_left_behind_is_frozen` | none |
| Q10 | **An aggregate only grows**, and **a value recorded at the current step is in its aggregate**, so the best value a recorder has been given at a step is never missing from, or lowered in, what it reports for it | `quepaxa::proofs::isr::theorem_an_aggregate_never_shrinks`, `theorem_a_recorded_value_is_in_the_aggregate` | none |

## What is not claimed

* **That the concrete protocol provides `tcast`.** This is the claim that matters and the
  one that is not here. The paper's concrete protocol (its Algorithm 4: proposers that
  spread proposals to recorders, read back summaries, and catch up when a recorder is
  ahead) is supposed to give each replica the three `tcast` outputs with the two
  guarantees. The paper argues that in its Appendix B. Nothing here models proposers or
  asynchronous messages, so **Q1 to Q6 say the idea is sound, not that any
  implementation of it is.** Q8 to Q10 are what a recorder does, and they are the part
  of that argument a recorder's behaviour supplies.
* **Termination, in any form but one.** The paper's liveness is that the protocol decides
  with probability one, under an adversarial scheduler, in under two rounds in
  expectation. This model has no probability. Q6 is only that a round with full
  information decides, which shows the safety proof is not vacuous and is not the paper's
  liveness theorem.
* **Priorities are the label's data.** Any assignment is a step, so every refinement
  chooses correctly. That priorities are random, drawn independently and from a large
  enough range that a tie is negligible, is what makes termination likely and is not
  modelled. Ties here are broken by the proposer's id.
* **The leader fast path and the hedging schedule.** The designated leader's one-round-trip
  decision, the delays that let later proposers wait, and the multi-armed-bandit choice of
  leader are optimisations of when things happen. None of it is modelled.
* **State machine replication.** This is one decision for one slot. The log of slots, batching,
  pipelining and what a submitter sees are not built.
* **The failure model beyond crashes.** Replicas crash and never return, fewer than half of
  them. A replica that crashes in the middle of a `tcast` is the same as one that crashes
  after it, because a replica heard from by only some is just a replica some majorities
  contain. Byzantine replicas, reconfiguration and recovery are out of scope.
* **The packing of a proposal.** The register aggregates `u128` values with `max`. The
  concrete protocol packs a proposal's priority, proposer and value into one so that the
  larger integer is the better proposal; that packing is not here.
* **Any service, or a consumer.** Nothing outside `src/quepaxa/` uses it, and there is no
  Jetstream service. It is not connected to [ownership](ownership.md)'s registry.
