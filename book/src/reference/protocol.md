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
