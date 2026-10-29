# Repository layout

```text
jetstream_distributed/
├── Cargo.toml              one crate (plus the vendored pmemlog); the services are behind the `service` feature (on by default; the proofs build without it)
├── rust-toolchain.toml
├── README.md
├── fuzz/                   the coverage-guided front end to the protocol-line search (its own workspace, nightly)
├── src/
│   ├── lib.rs
│   ├── identity/           who is calling: the Identity every service asks, and Roster, a table from address to node   [feature = "service"]
│   │   └── mod.rs
│   ├── protocol_t.rs       the Protocol trait: the labelled-step shape every model has
│   ├── protocol_v.rs       each model's instance is its model (next, init); the mailbox run is a run of the protocol
│   ├── temporal_t.rs       leads-to, weak fairness and WF1: what a liveness proof is stated in
│   ├── ownership/          exclusive mutable ownership with epoch fencing
│   │   ├── model_t.rs      state space + transition relation (no specification)
│   │   ├── spec_t.rs       may_mutate, tokens, the system invariant
│   │   ├── fencing_t.rs    current_epoch, valid_fence, staleness
│   │   ├── transfer_v.rs   the multi-step handover and its lemmas
│   │   ├── steps_v.rs      the transitions as executable u64 functions
│   │   ├── exec_v.rs       the u64 fence check a node runs on its own belief
│   │   ├── registry_v.rs   RegistryCore: the record, the grants published, the writes; one method per step
│   │   ├── service.rs      the protocol over Jetstream RPC   [feature = "service"]
│   │   └── proofs/
│   │       ├── invariant_v.rs    init ==> inv, inv /\ next ==> inv, reachable ==> inv
│   │       ├── properties_v.rs   structural, temporal and capability properties
│   │       ├── exclusivity_v.rs  claim 1
│   │       ├── fencing_v.rs      claims 2, 3, 5
│   │       ├── transfer_v.rs     claim 4
│   │       ├── tokens_v.rs       claim 6
│   │       ├── adversarial_v.rs  concrete adversarial executions
│   │       ├── refinement_v.rs   steps_v.rs agrees with the model's tr_* transitions
│   │       └── registry_v.rs     the registry's record, grants included, takes the model's steps
│   ├── raymond/            Raymond's mutual-exclusion routing layer
│   │   ├── model_t.rs
│   │   ├── steps_v.rs      the routing decisions as executable u64 functions
│   │   ├── exec_v.rs       RayTable: the routing record as verified code, one method per step
│   │   ├── service/        the protocol over Jetstream RPC   [feature = "service"]
│   │   │   ├── mod.rs      the Routing trait and what a node can see of itself
│   │   │   ├── router.rs   the whole routing record, behind one lock
│   │   │   └── refusal.rs  the refusals, in the line protocol's alphabet
│   │   └── proofs/{routing_layer_v.rs, routing_run_v.rs, refinement_v.rs}
│   ├── composed/           ownership and Raymond as one machine
│   │   ├── model_t.rs      the coupling enforced by guards, not assumed
│   │   ├── steps_v.rs      the coupling guards as executable functions
│   │   ├── exec_v.rs       the four coupled steps over the layers' records, and the debts
│   │   ├── service/        the two layers behind one coordinator [feature = "service"]
│   │   │   ├── mod.rs      the Composed trait: ownership + routing + the coupling
│   │   │   ├── command.rs  the coupling's four steps as data, and `apply`, the dispatch to the verified steps
│   │   │   ├── coordinator.rs  both layers, and the gate that serialises them
│   │   │   └── refusal.rs  the refusals, in the line protocol's alphabet
│   │   └── proofs/{coupling_v.rs, couples_v.rs, epoch_v.rs, scenario_v.rs, refinement_v.rs, exec_v.rs}
│   ├── actor/              a distributed actor: a journal fenced by ownership
│   │   ├── model_t.rs      envelopes, the journal, send / accept, the fold that is the state
│   │   ├── steps_v.rs      accept, send and the behaviour as executable u64 functions
│   │   ├── mailbox/        the queue in front of the actor, and its wakeup protocol
│   │   │   ├── model_t.rs  the three flags, six steps, and the step boundaries between them
│   │   │   ├── exec_v.rs   MailboxCore: the protocol as verified code, one method per step
│   │   │   └── proofs/
│   │   │       ├── invariant_v.rs  the six-clause invariant, and that every step preserves it
│   │   │       ├── safety_v.rs     nothing lost or repeated; per-sender order; no gaps
│   │   │       ├── liveness_v.rs   a message enqueued is a message processed, under fairness
│   │   │       ├── refinement_v.rs the executable core takes the model's steps, and refuses where it cannot
│   │   │       └── scenario_v.rs   a fair run that delivers; an unfair one that does not
│   │   ├── service/        the actor over Jetstream RPC   [feature = "service"]
│   │   │   ├── mod.rs      the Actor trait and what goes on the wire
│   │   │   ├── host.rs     the journal, the sent set, and the registry that fences them
│   │   │   ├── transport.rs Host::serve and Connection::new over any byte stream; Host::pipe in memory
│   │   │   ├── mailbox.rs  the mailbox protocol on real threads: Mailbox, Permit, Capacity, Round
│   │   │   ├── session.rs  Session (a ClientTransport over a mailbox) and serve (the drain)
│   │   │   └── refusal.rs  the refusals, in the line protocol's alphabet
│   │   ├── examples/
│   │   │   └── basic.rs    two actors, each behind its own mailbox, one calling the other
│   │   └── proofs/
│   │       ├── journal_v.rs      counting and folding over push and take
│   │       ├── invariant_v.rs    the six-clause invariant, and that every step preserves it
│   │       ├── exclusive_v.rs    one host at a time; nothing written under a superseded epoch
│   │       ├── delivery_v.rs     each message once, in order, none invented
│   │       ├── state_v.rs        append-only; the state is a fold and survives a handover
│   │       ├── refinement_v.rs   steps_v.rs agrees with the model's transitions
│   │       └── scenario_v.rs     a run through a whole handover, and the refusals at its end
│   ├── raft/               consensus: terms, votes, quorums, the log
│   │   ├── model_t.rs      state space + transition relation
│   │   ├── steps_v.rs      the election decisions as executable u64 functions
│   │   ├── exec_v.rs       ElectionCore: role, term, vote and tally as verified code, one method per step
│   │   ├── store_v.rs      a log that truncates, on a device that cannot
│   │   ├── wire_v.rs       the record encoding, and what a torn write leaves
│   │   ├── service.rs      the protocol over Jetstream RPC   [feature = "service"]
│   │   └── proofs/
│   │       ├── election_v.rs     Election Safety, via quorum intersection
│   │       ├── election_core_v.rs the election record takes the model's steps, vote and tally included
│   │       ├── history_v.rs      the ghost record, and Log Matching out of it
│   │       ├── log_v.rs          what one replication step gives you (and what it does not)
│   │       ├── terms_v.rs        term structure, entry durability, the election restriction
│   │       ├── commit_v.rs       what was committed, and State Machine Safety minus one hypothesis
│   │       ├── votes_v.rs        what a vote was a judgement of
│   │       ├── summary_v.rs      the summary a voter judged, tied back to the log it summarised
│   │       ├── persistence_v.rs  why the entry was still there when the voter judged it
│   │       ├── refinement_v.rs   steps_v.rs agrees with the model's tr_* transitions
│   │       ├── scenario_v.rs     a run in which an election actually happens
│   │       ├── store_v.rs        recovery is exact; a crash can only rewind
│   │       └── wire_v.rs         cut the bytes anywhere; a record prefix comes back
│   ├── hyparview/          membership by two small views: one node, so far
│   │   ├── model_t.rs      the views, the four handlers, the messages they send
│   │   ├── exec_v.rs       HvTable: the views as verified code; each handler is a step of the model
│   │   └── proofs/invariant_v.rs   the views stay bounded, disjoint, free of the node itself
│   └── swim/               gossip membership: merge, not majority
│       ├── model_t.rs      the record, the merge rule, one transition
│       ├── steps_v.rs      the merge and the refutation as executable u64 functions
│       ├── exec_v.rs       SwimTable: the node's table as verified code, learn and hear
│       ├── service/        the protocol over Jetstream RPC   [feature = "service"]
│       │   ├── mod.rs          the Membership trait and what goes on the wire
│       │   ├── node.rs         the table, and the merge into it
│       │   └── refusal.rs      the refusals, in the line protocol's alphabet
│       └── proofs/
│           ├── merge_v.rs      idempotent, absorbs a repeat, never regresses, commutative, associative
│           ├── monotone_v.rs   lifted through a step and then through a run
│           ├── refinement_v.rs steps_v.rs agrees with the model's tr_gossip
│           └── table_v.rs      the table learns by tr_gossip; a refutation is a second one
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
│   ├── actor_journal.rs        the guarantees over a Jetstream session, and every refusal [feature = "service"]
│   ├── actor_turmoil.rs        an actor changes hands across hosts, nothing lost or repeated [feature = "service"]
│   ├── actor_mailbox.rs        A calls B through a mailbox, backpressure, abort and close [feature = "service"]
│   ├── raymond_routing.rs      the textbook request path, and every refusal [feature = "service"]
│   ├── raymond_turmoil.rs      the same path across hosts, on a simulated network [feature = "service"]
│   ├── identity.rs             services ask an Identity, not a table; a composition shares one [feature = "service"]
│   ├── composed_handover.rs    the coupling: no move while held, no acquire without it [feature = "service"]
│   ├── composed_turmoil.rs     the privilege moves only after the release, across hosts [feature = "service"]
│   ├── swim_membership.rs      the merge rule in every order, and the refutation [feature = "service"]
│   ├── swim_turmoil.rs         a suspicion crosses a healed partition and is refuted [feature = "service"]
│   └── seeds/scenarios.txt     seeds that once broke something
├── vendor/
│   ├── README.md               provenance, what is built, and pmemlog's six assumptions
│   ├── verified-storage/       Microsoft's verified-storage, whole and verbatim (CI diffs it)
│   │   ├── pmemlog/            the verified persistent-memory log [verified by CI]
│   │   ├── multilog/           logs with atomic appends across them [not yet built]
│   │   ├── capybaraKV/         a persistent-memory key-value store [not yet built]
│   │   └── ...                 capybaraNS, soundness_proofs, unverified, LICENSE.txt
│   └── kverus/                 the KVerus agent skills, verbatim (CI diffs it)
│       ├── README.md           provenance, and which skills edit code
│       └── skills/             kverus-review, kverus-eval, ... : what AGENTS.md's reviews follow
├── AGENTS.md                   build and verify commands, the rules, and how to review a change
└── .github/workflows/verify.yml
```

**One directory per algorithm, and each one holds the whole of that algorithm**
— its model, its proofs, its executable steps and its service. A protocol whose
proof lived in one crate and whose implementation lived in another is a protocol
where the two can drift without anything noticing; here they are compiled
together and the service calls the functions the proofs are about.

**The services are behind a `service` feature**, which is on by default so that
depending on the crate gives you them, and that feature is what makes one crate
workable. `verus --crate-type=lib src/lib.rs` does not read features, and `cargo
verus verify --no-default-features` turns it off, so the verified build's
dependency graph is `vstd` and nothing else — no Jetstream, no async runtime for
Verus to be asked about, and no need for a single `#[verifier::external]` to keep
service code out of the proofs. With the feature on, the same modules compile
against the same verified step functions, under `cargo +stable`: `rust-toolchain.toml`
pins the Rust release the Verus build was made against so the **proofs** verify,
not so a service is stuck on it.

This differs from a plain `proofs/` directory at the repository root: Verus
verifies a *crate*, so every proof file has to be a module of that crate.
Keeping them under `src/{algorithm}/proofs/` is the ordinary Rust way to express
that; a top-level `proofs/` would need `#[path = "../proofs/..."]` attributes
for no benefit.

**File names follow the verified-storage convention** the vendored code uses: a
`_t.rs` file is **trusted** — the model, the specification, the definitions a
claim is stated in, which a reader has to audit because no proof checks them
against anything — and a `_v.rs` file is **verified**: executable code and proofs,
which Verus checks. `service/` is plain Rust that Verus never sees and carries no
suffix. The suffix is on the *file*; the module keeps its plain name
(`#[path = "model_t.rs"] pub mod model;`), so `crate::raft::model::tr_timeout` is
still where it was.

**Verified executable code** is in the `steps_v.rs`, `exec_v.rs` and, where an
algorithm keeps state, `registry_v.rs`-style files of each algorithm: small
`u64`-valued functions and the records they act on, each with a postcondition
stated in terms of that algorithm's model and a theorem in its
`proofs/refinement_v.rs` (or the proof file named for the record) discharging it. **Unverified executable code** is in each algorithm's
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
side is `src/ownership/steps_v.rs`.
Everything else in the crate is specification or proof.

Specification and proof code are kept apart from the model: `src/ownership/model_t.rs`
defines only the state space and the transition relation and does not import the
specification layer, so a specification cannot be quietly weakened to fit the
model.
