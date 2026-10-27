# Status: proven, modelled, future work

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
  `(actor, Epoch)`" and the stronger "at most one token is ever issued per
  `(actor, Epoch)`";
* stale tokens surviving crash, partition and recovery confer no authority;
* the ownership registry's record, grants included: each of its methods takes the
  model's step and publishes the grant the model's transition publishes, and a
  refusal is a step the model could not take (E8–E9);
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
  deletion is implementable on a device that deletes nothing;
* SWIM's merge rule: idempotent, absorbs a repeated message, never accepts a
  record that does not out-rank the local one, is commutative and associative
  — and, lifted through every step of a run, no node's record about any peer
  ever moves backward (S1–S6); the executable merge is that rule, and a
  refutation out-ranks the accusation it answers and is itself a gossip step
  (S7–S9); and the node's table is checked to learn by the model's `tr_gossip`, a
  refutation being a second one (S10–S12);
* the Raymond routing steps and the composed machine's coupling guards agree
  with their models in both directions — each fires exactly when the model's
  transition is enabled — and a step a layer already proved is carried by the
  composed machine without a second proof (R15, C8–C9); and the routing record the
  service keeps is checked to take the model's steps and to refuse where it cannot
  (R16–R17), and the composed coupling's four steps over both layers' records and
  the reconciliation debts are the composed model's (CX1–CX2);
* the distributed actor: at most one host appends, now and across handovers (one
  host per epoch; nothing written under a superseded epoch); each message once, in
  the order sent, none invented; the journal is append-only and the state is a fold
  that a handover preserves; and the executable steps agree with the model (A1–A15);
* the actor's mailbox: nothing lost, repeated or reordered; each sender's messages
  numbered without gaps, in the very form the actor's accept guard counts; and —
  the first liveness theorem here — **every enqueued message is eventually
  processed under weak fairness of the drain's and each sender's steps**, with the
  fairness rules proved in `temporal` and both the fair run that satisfies the
  assumption and the unfair one that shows it is needed exhibited (MB1–MB9); and the
  executable mailbox core, whose every step is checked to be the model's (MB10–MB11).

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

* **SWIM has no probe scheduler, no indirect-ping fallback and no
  dissemination piggyback budget.** `swim::model` is the merge rule and one
  transition, and `swim::service` is a table that obeys it; a real
  deployment's failure detection and gossip *timing* — how often, and by
  piggybacking on what — is not modelled at all, so nothing here says gossip
  eventually arrives, only that whatever arrives cannot move a view of the
  world backward (S5). See
  [SWIM](swim.md#swim-gossip-membership-bought-by-merge-rather-than-majority) for
  which half of the convergence argument that is.

* **The actor's journal is assumed durable and linear, and the service's is in
  memory.** The model has no crash that loses an accepted entry; the service's
  journal dies with its process, so the guarantees hold for the lifetime of the
  process and not across its death. Durability is the next layer.

* **The actor proves safety; the mailbox proves delivery, but `Host` does not sit
  behind the mailbox.** The actor's own model says nothing about a message ever being
  offered to its host, and an out-of-order arrival is refused, not buffered.
  `actor::mailbox` proves that a queue in front of it delivers every enqueued
  message, in order, under a stated fairness assumption. `service::Mailbox`,
  `Session` and `serve` run that protocol and deliver to any generated service, but
  only the queue-and-flags core under their lock is a verified refinement (the lock,
  capacity and wakeups are not), `serve` does not yet check the
  ownership epoch around each call, and `Host` still keeps the actor's sent set and
  relies on its caller to call `accept`. Subscriptions are not served through the
  mailbox, and the reply path is not bounded. The actor's behaviour is a pure fold, so what a message *does* beyond
  changing the state — an effect, a reply — is not modelled, and neither is what
  an effect does if its host is fenced halfway through.

* **The actor service refines the crash-free executions only**, for the reason the
  composed service does.

* **The Raymond and composed services host the global record in one process.**
  `raymond::service::Router` holds every node's entries under one lock because
  the model's `Raymond` is one struct, and the composed `Coordinator` serialises
  both layers behind a gate because the coupling reads both. They check
  Raymond's rules; they do not distribute them. A deployment where each node
  keeps only its own entries is a different system, and nothing here says it is
  refined by this one.

* **The composed service refines the crash-free executions only.** The composed
  model guards some steps on `own.live`, which is ground truth and not something
  a process can evaluate; the service has no `Crash` or `Recover`, and C8 states
  liveness as a hypothesis. Seizing from a holder that is merely unreachable is
  inside the fragment, because `SeizeToken` has no liveness guard on the node it
  takes the privilege from.

* **SWIM's `Left` is simpler than memberlist's `StateLeft`.** memberlist gives a
  graceful departure its own precedence and rejoin rules. `swim::model::Status`
  has `Left`, ranked above `Dead` so that a failure verdict cannot undo a
  departure (S13, S14), but a rejoining node is an ordinary node that hears it is
  gone and refutes with a higher incarnation, exactly as after `Dead`. There is
  no separate rejoin handshake. Members are never forgotten, so a departed
  member's record stays and counts against the bound of `MAX_UPDATES` members.

**Future work** (deliberately out of scope):

* **liveness** of either layer - progress, fairness, termination of a handover,
  and Raymond's "every request is eventually served". These need assumptions
  (reliable FIFO links, eventual failure detection) that this model does not
  make.
* **done, for the registry's transitions**: the refinement from the `nat`-valued
  model to an executable `u64` implementation, with the epoch-exhaustion case
  handled, is `src/ownership/steps_v.rs` and `src/ownership/proofs/refinement_v.rs` — see rows E1 to E6.
  What remains unrefined is the *node* side: `src/ownership/exec_v.rs` still offers no way
  to advance a node's fence guard, only to consult it, so that no executable API
  can perform a handover the model does not;
* the actual actor runtime: networking, persistence, and the code that obeys the
  protocol. Verifying the protocol says nothing about whether an implementation
  follows it. `tests/` now exercises a hand-written one against the model's own
  theorems on a simulated network (see
  [Network resiliency](simulation.md#network-resiliency-the-model-run-for-real)), which is
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
* **the rest of SWIM.** The probe timer and its schedule, the indirect-ping
  fallback a probe target's neighbours run when a direct probe times out, and
  the piggyback selection that decides which records ride on which probe. The
  merge core, its executable steps and the `Membership` service are done; what
  is left is the part with a clock in it. The [SWIM](swim.md#swim-gossip-membership-bought-by-merge-rather-than-majority)
  section above says what is and is not claimed.

## The holder graph is a tree, and now says so

`ray_unique_token` and `ray_token_exists` together say there is exactly one
root. That is not the same as the holder graph being a tree: nothing stopped a
set of non-root nodes from pointing at each other in a cycle, off to one side of
the real root. `ray_init` permitted it too — it forbids only a non-root pointing
at *itself*, so `A → B`, `B → A` beside a root `C → C` satisfied it.

The consequence was visible in `src/raymond/model_t.rs`'s own opening comment: "requests
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

## Scenarios export labelled runs, not endpoints

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
