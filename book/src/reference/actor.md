# Actor: a journal fenced by ownership

An actor in a single process is single-threaded by construction, so it never has
to say what it guarantees. Spread over machines it does, and the guarantees are
exactly the ones a single process gets for free: **one thing at a time**, **each
message once**, **in the order sent**, and **state that survives** moving.

`src/actor/` proves those four, and it does so by one decision: **the actor's
state is not held by its host.** It is a *journal* — the ordered sequence of
messages the actor has accepted — and the state is a fold over it
(`actor::model::state_of`). Appending to the journal is the one thing a host does
that matters, and it is **fenced by the ownership protocol**: `as_accept` requires
`ownership::spec::can_mutate` at the epoch the host presents, which is
`Owned { host, epoch }` and nothing else. A host that is not the owner, or owns a
generation that has been superseded, cannot append. Nothing about the actor needs
a second fence; the journal write *is* the mutation the ownership protocol fences.

Everything else follows from three facts: only the owner at the current epoch can
append (the ownership layer's exclusivity and fencing, used as-is); an append is
accepted only if the message's sequence number is **exactly** the number already
accepted from its sender (so a duplicate and a message ahead of its turn are the
same refusal); and the journal is only ever extended.

The network may delay, duplicate and reorder — `ActorSystem::sent` never shrinks,
so a message can be offered to the host any number of times, in any order. None of
that is a separate failure mode: it is what `as_accept` is already quantified over.

| # | claim | theorem | assumes |
| --- | --- | --- | --- |
| A1 | **At most one host can accept at any instant**, and at only one epoch — in *no* state at all do two different hosts both satisfy the authority guard | `actor::proofs::exclusive::theorem_at_most_one_host_can_accept` | none |
| A2 | **A superseded host cannot accept.** Present any epoch behind the actor's current one and no post-state, whatever the message, satisfies `as_accept` — a returning stale owner's first append is refused | `actor::proofs::exclusive::theorem_a_superseded_host_cannot_accept` | none |
| A3 | **Nobody accepts between owners.** While the actor is `Transferring` or `Unowned` there is no host to append — in particular not the outgoing owner, whose epoch was burned the moment the transfer began | `actor::proofs::exclusive::theorem_nobody_accepts_between_owners` | none |
| A4 | **Only the owner accepts, and only at the current epoch** | `actor::proofs::exclusive::theorem_only_the_owner_accepts` | none |
| A5 | **One host per epoch.** Across the whole life of the actor, two entries written at the same epoch were written by the same host. This is not A1 restated: A1 says two hosts cannot append *at once*; this says they cannot append *under one generation*, however far apart in time | `actor::proofs::exclusive::theorem_one_host_per_epoch` | reachability |
| A6 | **Epochs never fall along the journal.** Nobody writes behind a newer host | `actor::proofs::exclusive::theorem_epochs_never_fall_along_the_journal` | reachability |
| A7 | **Nothing is written under an epoch the actor has already left.** From any point of an execution on, every entry appended afterwards carries an epoch at least the actor's epoch at that point. Fencing as a fact about the *log* rather than about one request: A2 says a superseded host's attempt is refused, this says none of its writes can be found afterwards | `actor::proofs::exclusive::theorem_nothing_is_written_under_a_superseded_epoch` | an execution |
| A8 | **Nothing is invented.** Every message in the journal was sent | `actor::proofs::delivery::theorem_only_sent_messages_are_accepted` | reachability |
| A9 | **The nth message accepted from a sender is numbered n**, and **one sender's messages are accepted in the order sent** — the journal holds each sender's messages as 0, 1, 2, ...: none out of place, none repeated, none skipped | `actor::proofs::delivery::theorem_the_nth_message_from_a_sender_is_numbered_n`, `theorem_one_senders_messages_are_accepted_in_order` | reachability |
| A10 | **A message is accepted at most once**, however many times the network delivers it | `actor::proofs::delivery::theorem_a_message_is_accepted_at_most_once` | reachability |
| A11 | **A redelivered message is refused**, by the current host at the current epoch — the one pair otherwise allowed to append — and **a message ahead of its turn is refused** until the ones before it arrive. The first needs only the invariant, so a service holding a journal can use it to classify an arrival | `actor::proofs::delivery::theorem_a_redelivered_message_is_refused`, `theorem_a_message_ahead_of_its_turn_is_refused` | `actor_inv` |
| A12 | **The journal is append-only.** Along any execution an earlier journal is a prefix of every later one: what the actor accepted, it keeps, in the order it accepted it — including across a handover | `actor::proofs::state::theorem_the_journal_is_append_only` | an execution |
| A13 | **State survives.** An append is exactly one application of the behaviour; a handover changes neither the journal nor the state; and a run continues the state rather than restarting it — between two points of an execution, the later state is the earlier one with the intervening entries replayed on top. The new owner does not receive the state from the old one; it reads the same journal and recomputes it | `actor::proofs::state::theorem_accepting_applies_the_behaviour`, `theorem_a_handover_preserves_the_state`, `theorem_the_state_continues_across_a_run` | an execution |
| A14 | **The executable steps agree with the model, in both directions**: when `accept_step` fires the model's `Accept` fires to exactly the state computed, and when it refuses the model's transition is not enabled in any post-state; when `send_step` fires it hands out exactly the model's number and leaves the model's counter, and it refuses only at `u64::MAX`, where the model's `Send` is disabled too (`as_send` requires the sender's counter below `u64::MAX`), so the sender's refusal is not a narrowing; `accept_step` is the one place the executable does less than the model allows, refusing an enabled `Accept` only with its count at `u64::MAX` (the model's count is a `nat`), and it refuses rather than wraps; the host's count stays right across an append; and the fence answer the step is handed *is* the model's `can_mutate` | `actor::proofs::refinement::theorem_accept_step_refines`, `theorem_accept_step_refuses_exactly_when_disabled`, `theorem_send_step_refines`, `theorem_send_step_refuses_only_at_exhaustion`, `theorem_accept_step_refuses_an_enabled_append_only_at_exhaustion`, `theorem_accepting_advances_the_count_by_one`, `theorem_the_fence_answer_is_the_models_authority` | the couplings in the module's table |
| A15 | **The guarantees are not vacuous.** One concrete run, through the ownership protocol's real transitions: `A` takes the actor and accepts a message, it is handed to `B` through grant, acquire, begin-transfer, revoke, release and acquire, and `B` accepts the next. It ends with two hosts and two epochs in one journal, and the old host and a redelivery are both refused | `actor::proofs::scenario::scenario_the_run_is_an_execution`, `scenario_the_run_ends_with_both_hosts_in_the_journal`, `scenario_the_old_host_is_refused`, `scenario_a_redelivery_is_refused` | none: the run is exhibited |

All of A5–A13 rest on one inductive invariant (`actor::proofs::invariant::actor_inv`)
whose six clauses are the inductive forms of the guarantees: nothing invented,
sequence numbers equal prior counts, epochs bounded by the actor's current one,
epochs ordered along the journal, one host per epoch, and — the clause that makes
the last one provable — an entry written at the actor's *current* epoch was
written by its *current* owner. `lemma_step_preserves_inv` shows every step
preserves it, and `theorem_reachable_inv` that it holds in every reachable state.

**What this is not.** It is a set of *safety* properties. Nothing says a message is
ever delivered, or that a sender retries. An out-of-order arrival is *refused*, not
buffered, so the sender (or a mailbox in front of the host) must retry in order for
anything to make progress — the same line the other protocols here draw between
safety and liveness. And the journal is assumed **durable and linear**: the model
has no crash that loses an accepted entry, which is the actor's counterpart of the
atomic-registry assumption the ownership layer makes, and the service keeps the
journal in memory (see [The actor](services.md#the-actor)). Delivery to the host is the next
section's subject.

## The mailbox, and the first liveness theorem

The paragraph above says the actor proves nothing about a message ever being
*offered* to its host. `src/actor/mailbox/` is the queue that would offer it, and
it is where the lost-wakeup problem lives: a drain that is scheduled rather than
polling must be woken by the sender that finds it asleep, and every sender checks,
then acts, with other senders and the drain acting in between.

The machine is the protocol of Apple's swift-distributed-actors mailbox, which
keeps it as a PlusCal/TLA+ model
([`Models/mailbox.tla`](https://github.com/apple/swift-distributed-actors/blob/main/Models/mailbox.tla)),
with the same three flags (`has`, `processing`, `scheduled`) and the same step
boundaries. A sender takes three steps — enqueue; read-and-set `has`; schedule if
`has` was clear and the drain is not running — and the drain takes three — claim
(clear `has`, mark running); take the queue; finish (stay scheduled exactly when
`has` was set meanwhile). The TLA+ model fixes two senders, five messages each, and
a drain that stops after ten, so a model checker can exhaust it. Here a sender is
an *operation* tracked in `Mailbox::ops` rather than a process, so any number of
senders each sending any number of messages are covered at once; the bound is what
the proof removes.

Safety is a corollary of one invariant. **Liveness is a different kind of claim**,
and the proof says so: it is a statement about the infinite run, it is false of
the bare machine (a run in which the drain is never given a turn processes
nothing), and so it is stated under a fairness assumption written down as a
definition (`mailbox_fair`) rather than left implicit. The temporal logic it uses
is `src/temporal_t.rs`, in the idiom of
[verus-tla](https://github.com/anvil-verifier/verus-tla) (Anvil's embedding of TLA
in Verus) — executions as functions from step number to state, `leads_to`, weak
fairness, and the WF1 rule — rebuilt in-crate rather than depended on, because
`verus --crate-type=lib src/lib.rs` links `vstd` and nothing else. Every rule is
proved, not assumed.

| # | claim | theorem | assumes |
| --- | --- | --- | --- |
| MB1 | **The mailbox invariant holds at every step of every run**: the `processing` flag says whether the drain runs; messages are numbered by the count before them; each sender's next number is its count; a sender mid-operation is on a message the mailbox holds; and the two clauses that *are* the protocol — a set `has` with no wakeup pending is accounted for by a sender that has set it and not yet scheduled, and a queued message with `has` clear is accounted for by a sender that has enqueued it and not yet set `has` | `actor::mailbox::proofs::invariant::mb_inv`, `lemma_step_preserves_inv`, `theorem_run_inv` | a run |
| MB2 | **Nothing is lost or reordered.** What the mailbox had taken in at one step is the beginning of what it has taken in at any later one, and the same of what it has processed | `actor::mailbox::proofs::safety::theorem_nothing_is_lost_or_reordered` | a run |
| MB3 | **Each message is taken in once** — no message appears twice among those queued or processed | `actor::mailbox::proofs::safety::theorem_a_message_is_taken_in_once` | `mb_inv` |
| MB4 | **One sender's messages keep their order**, and **nothing is skipped**: a message's number is the count of its sender's messages before it | `actor::mailbox::proofs::safety::theorem_one_senders_messages_keep_their_order`, `theorem_a_senders_messages_are_numbered_without_gaps` | `mb_inv` |
| MB5 | **The drain never presents a message ahead of its turn.** The `i`th message processed is numbered the count of its sender's messages among the `i` before it — word for word the guard of the actor's accept (`env.seq == accepted_from(journal, sender)`), so a host accepting in this order is never refused for being early. And the processed messages are the front of what the mailbox holds | `actor::mailbox::proofs::safety::theorem_the_drain_never_presents_a_message_ahead_of_its_turn`, `theorem_the_drain_takes_the_front_of_the_queue` | `mb_inv` |
| MB6 | **A message enqueued is a message processed.** In every run in which the drain's three steps and each sender's two remaining ones are not starved, a message on the queue is later in `processed`. The proof is the lost-wakeup argument: where the drain is decides the next stage, and when it is asleep with nothing scheduled the invariant says some sender is on its way to waking it, and fairness says it gets there. Senders are *not* required to send — `enqueue` is not on the fairness list | `actor::mailbox::proofs::liveness::theorem_every_enqueued_message_is_processed` | `mailbox_fair` |
| MB7 | **The fairness rules are theorems**: WF1 (a step enabled while `p` holds, and the only way out of `p`, gives `p ~> q` under weak fairness of that step), transitivity, and case-splitting | `temporal::lemma_wf1`, `lemma_leads_to_trans`, `lemma_leads_to_cases`, `lemma_leads_to_implies` | none |
| MB8 | **The liveness theorem is not vacuous.** A run of the machine that satisfies `mailbox_fair` and does work: one message is queued and processed, and a second that arrives *after* the drain took the queue is queued and processed, woken by the drain's last step seeing `has` — and the theorem applies to it | `actor::mailbox::proofs::scenario::scenario_a_fair_run_delivers_two_messages`, `scenario_the_theorem_applies_to_it` | none: the run is exhibited |
| MB9 | **The fairness assumption is necessary.** A run of the machine in which a message is enqueued and never processed, and which is not fair: its sender's own `set_state` step stays possible forever and is never taken | `actor::mailbox::proofs::scenario::scenario_without_fairness_a_message_waits_forever` | none: the run is exhibited |
| MB10 | **The executable core is the model.** `exec::MailboxCore` — the queue and flags the runtime keeps behind its lock — has one method per step, and each method's contract is the model's step: a fresh core is `mb_init`; `enqueue`, `set_state`, `schedule`, `claim`, `take` and `finish` each take the model to a state the core still stands for (`refines`), `take` handing out exactly what the model adds to `processed`; `set_state` returns what the sender's operation records | `actor::mailbox::proofs::refinement::theorem_new_refines_init`, `theorem_enqueue_refines`, `theorem_set_state_refines`, `theorem_schedule_refines`, `theorem_claim_refines`, `theorem_take_refines`, `theorem_finish_refines` | the sender's protocol: the item stands for the envelope the model numbers next, `set_state` is called for a `Marked` operation, `schedule` for a `Scheduling` one with the `had` it recorded; for `enqueue`, also that the sender's number is below `u64::MAX` (`mb_seq(m, sender) < u64::MAX`), because the model's `mb_enqueue` is disabled there and the core's counter is a `u64` |
| MB11 | **A refused step is one the model could not take.** `claim` refuses exactly when the model's guard is false (so no second drain can claim while one runs), and `take` and `finish` out of phase change nothing — the model's stutter — and the model has no enabled `mb_drain` or `mb_finish` there | `actor::mailbox::proofs::refinement::theorem_claim_refuses_exactly_when_disabled`, `theorem_take_refuses_exactly_when_disabled`, `theorem_finish_refuses_exactly_when_disabled`, `theorem_a_stutter_refines` | `refines` |

**What this does not do.** The model's proofs are about the model, and MB10–MB11
connect the *core* to it. The protocol *is* run now —
`service::Mailbox` wraps that core in a lock, and
[The mailbox as a transport](services.md#the-mailbox-as-a-transport) says how it is used — but
the lock, the capacity and permits, the wakers and the notification are plain Rust
the tests exercise, and so is `requeue`, which puts back what a dropped round never
handed out and is not a model step. Nothing checks that callers follow the sender's
three steps; MB10 takes it as a hypothesis. And `Host`
does not sit behind it yet: `Host` keeps the sent set of the actor's model and the
owning node calls `accept`. The fairness assumption is *weak*
fairness of those steps and nothing stronger, and it is an assumption about the
scheduler, not something the protocol can enforce — a drain that is never run
delivers nothing, which MB9 exhibits. And the mailbox hands the actor an *ordered*
stream; the ownership fence that decides whether the actor may append it is the
previous section's, unchanged.
