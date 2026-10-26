# Network resiliency: the model, run for real

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

## The search over what arrives, not over what a correct node sends

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
it does — which is exactly the gap `src/ownership/steps_v.rs` closes for the Jetstream
service in `src/ownership/service.rs`, and the reason the two coordinators are worth
keeping side by side.

**Would the oracles notice?** A suite that cannot fail is indistinguishable
from one that passes, so `oracles_catch_an_unfenced_coordinator` runs one story
twice with a single bit changed — the coordinator stops checking writes against
the registry — and requires the oracles to *reject* the second run. Same
actions, same seed, same network, same oracles; what separates them is exactly
the check `src/ownership/exec_v.rs` says has to happen where the effect lands.
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
precisely the asymmetry `src/ownership/exec_v.rs` documents.

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
