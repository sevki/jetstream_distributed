# Protocol: the shape every model has

Every model in this crate is a labelled-step state machine: a state, a label for each
kind of step, an initial predicate, and a relation saying which labelled steps are
allowed. Each module spelled that differently (`init`/`next`, `raft_init`/`raft_next`,
`ray_init`/`ray_next`, `swim_init`, `actor_init`, `mb_init`, `composed_init`), so
nothing in the types said what a protocol is.

`protocol::Protocol` (`src/protocol_t.rs`, trusted) is that shape, written once: an
associated `Config`, `State` and `Step`, an `init`, a `step`, and a provided
`next` that is "some step". Each model implements it at the bottom of its own
`model_t.rs`. The agreement lemmas (`src/protocol_v.rs`, verified) pin each instance
to the model it describes.

## What is proved

| ID | Claim | Theorem | Assumes |
| --- | --- | --- | --- |
| P1 | **Each instance's `next` is its model's `next`**, in both directions, for ownership, Raft, Raymond, SWIM, the actor, the mailbox and the composed machine. A theorem about a model and the same theorem about its `Protocol` are the same theorem | `protocol_agreement::lemma_ownership_next_agrees`, `lemma_raft_next_agrees`, `lemma_raymond_next_agrees`, `lemma_swim_next_agrees`, `lemma_actor_next_agrees`, `lemma_mailbox_next_agrees`, `lemma_composed_next_agrees` | none |
| P2 | **The instances' `init` is the model's `init`**, at the configuration the model has (Raymond's root; `()` elsewhere). By definition today, stated so that a later change to an instance cannot drift from the model | `protocol_agreement::lemma_init_agrees` | none |
| P3 | **A mailbox run in the crate's existing sense is a run of the mailbox `Protocol`**, so `protocol::runs_of` and the statement the mailbox's liveness proof is built on are the same notion | `protocol_agreement::lemma_mailbox_run_is_a_run_of_the_protocol` | `mb_run(ex)` |

## What this does not say

* **It is a shape, not a relationship.** No theorem here relates two protocols. In
  particular the composed machine's `Protocol` instance is written by hand; it is
  *not* derived from the ownership and Raymond instances. Deriving it is the generic
  composition tracked in [#67](https://github.com/sevki/jetstream_distributed/issues/67).
* **There is no observable view.** What a consumer of a protocol may read (a
  membership protocol's peers, a log's committed prefix) is defined alongside the
  first property that reads it, in the membership contract ([#65](https://github.com/sevki/jetstream_distributed/issues/65)).
* **No liveness for the other protocols.** `runs_of` exists, but only the mailbox
  states a liveness theorem against it (P3). Giving the others one is separate work
  per protocol, and each needs its own fairness assumption.
* **Nothing about the services.** The `service` code is plain Rust and does not
  implement `Protocol`; it calls the verified step functions, which the refinement
  rows in the per-protocol chapters tie to the models.

## Composition

`compose::Product<A, B, K>` (`src/compose_t.rs`, trusted) is two protocols and the way
they meet. Its state is both parts' states and the coupling's own (the *glue*); its
steps are `A` moving alone, `B` moving alone, or a **joint** step that belongs to
neither, defined by the coupling `K: Coupling<A, B>`. The coupling is the only place the
two meet: a guard on a part's step may read the other part and the glue, and the glue
may change when a part moves, but a part never moves the other.

| ID | Claim | Theorem | Assumes |
| --- | --- | --- | --- |
| P4 | **Safety composes.** If `A` and `B` are `Safe` (an invariant their initial states satisfy and their steps keep) and `K` is a `SafeCoupling` (its own invariant `coupled` holds initially, and is kept by every step of the product, given both parts' invariants; and a joint step also keeps both parts'), then every initial state of the product satisfies `A::inv /\ B::inv /\ coupled`, and every step keeps all three. The product is itself `Safe`, so it can be a part of a larger one | `compose_safety::theorem_a_composition_starts_safe`, `theorem_a_composition_stays_safe` | the coupling's two obligations, `coupled_at_init` and `coupled_after` |
| P5 | **Ownership and Raymond are `Safe`**, by the theorems they already had: ownership's `inv` is established by `lemma_init_inv` and kept by `lemma_step_preserves_inv`; Raymond's `ray_inv` by `theorem_ray_init_inv` and `lemma_ray_step_preserves_inv` | `ownership::proofs::safe`, `raymond::proofs::safe` (instances; the lemmas they call are the ones named) | none |
| P6 | **The composed machine is the product of ownership and Raymond**: `composed_step` is the product's step under a label, and every product step is a `composed_step`, so `composed_next` is the product's `next`. `Own`, `AcquireUnderToken` are `Left`; `Ray`, `PassToken` are `Right` (`PassToken` is Raymond's `AssignPrivilege`); `SeizeToken`, `Reconcile` are `Joint`, the coordinator's steps that edit Raymond's state without being a Raymond step | `composed::proofs::product::lemma_composed_step_is_a_product_step`, `lemma_product_step_is_a_composed_step`, `theorem_composed_next_is_the_product_next` | none |
| P7 | **The composed machine's initial states are the product's**, at some Raymond root | `composed::proofs::product::theorem_composed_init_is_the_product_init` | none |
| P8 | **The ownership/Raymond coupling is a `SafeCoupling`.** Its `coupled` is what `composed_inv` says beyond each layer's own invariant (the actor exists, `couples`, the two layers share their nodes, every stale holder owes a reconciliation), and both obligations are discharged by the composed machine's own theorems (the C-rows) through P6 | `composed::proofs::product` (the `SafeCoupling` instance), from `composed::proofs::coupling::lemma_composed_init_inv`, `theorem_composed_step_preserves_inv` | the C-rows |

## What composition does not say

* **The coupling may be wrong.** A coupling too strong to be useful is safe vacuously.
  P4 is why a composition needs only its coupling proved; it is not a check that the
  coupling lets the interesting things happen. For the composed machine that check is
  its scenarios (`composed::proofs::scenario`). A new composition needs its own.
* **One instance so far.** `Coupling` was written against the one composition the crate
  has, and it fits that one exactly (P6). Whether it fits the next (Raft with
  ownership, the mailbox with `Host`) is what building them will show; nothing here
  claims it already does.
* **The composed model is not rewritten.** It stays hand-written and every theorem in
  its chapter stays stated against it. P6 is the bridge, not a replacement.
* **No liveness.** Fairness does not compose by this argument; each composition that
  wants a liveness theorem states its own.
* **No services.** This is the machine. How a composed *service* is assembled from two
  services is a separate question: the `#[service]` macro takes a trait, not a pair of
  them, so the composed service's trait is still written out.
