# Raft: the same statement, bought by counting

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

## The log, and the line between modelled and proved

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

## The ground that induction has to stand on (C39–C43)

`src/raft/proofs/terms_v.rs` is not that induction. It is the part of it that can
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

## What was committed, as a fact that survives the state (C44–C47)

The first of those three missing pieces is now there. `Cluster` carries a third
ghost field, `committed`, written at `tr_advance_commit` and never removed from,
and `src/raft/proofs/commit_v.rs` is what it buys.

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

## All three records are now in place — and the induction still is not (C49–C50)

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

## ~~So the materials are all here~~ — they were not, and C52 is the one that was missing

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

## The second step, and the difference between a translation and a paragraph (C53–C54)

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

## A log that truncates, on a device that cannot

Raft's log shrinks. Figure 2's rule 3 deletes a conflicting entry and everything
after it, and `appended_log` is that rule. Every durable log worth trusting
*grows*: `vendor/verified-storage/pmemlog`'s abstract state offers `append` and `advance_head` —
put bytes on the end, or forget bytes from the front — and nothing that takes
the tail back.

That is not a gap in the vendored crate. It is what makes a crash-consistent log
cheap: an append that either happened or did not is one write, while a tail that
moves backwards is a state the device has to be able to be caught in the middle
of.

`src/raft/store_v.rs` reconciles them in four lines of idea:

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

### The commit point, and the one Raft property this model gives up

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

### The byte layer, and the theorem it exists for

C27–C31 are about *records*; pmemlog appends *bytes*. `src/raft/wire_v.rs` is the
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

### The line a crash may not cross

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

### Compaction has a middle state

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
* **Nothing in `src/` depends on `vendor/verified-storage/pmemlog` yet**, and the reason is no
  longer "the executable layer does not exist" — `replay_exec`, `encode_exec`
  and `parse_exec` do. What is missing is a **device**, and the obstacle there is
  not an interface but a crash model: pmemlog's `persistence_chunk_size` is 8 and
  a write must be safe for *any subset* of 8-byte chunks having flushed, which
  **POSIX does not promise** for a write crossing a chunk. An `fsync`-per-write
  file would not satisfy it. That needs a target platform — real PM, `O_DIRECT`
  with aligned single-sector writes, or an explicitly weaker documented device.
  Until one exists, pmemlog's two corruption assumptions are not assumptions of
  anything proved here.

## The consensus service

**The election record is verified code; the log, the commit point and the shell
are not (CE1–CE2).** `Peer` keeps an `exec::ElectionCore` behind its lock — role,
term, whom it voted for, and the votes it has counted — and `stand_for_election`,
the vote handling in `request_vote`, `step_down_to`, `yield_at` and the tally in
`count_ballot` all go through it, so each is the model's step by contract and each
refusal a step the model could not take. What is not proved: the log and the
up-to-date comparison (an argument to the core), the commit point and replication
progress (`record_match` and the figure-8 rule are plain Rust), the roster, the
lock, the audit log, and the durable store — the core calls `persist` with the term
and vote before it moves, and that order is the code's, not a theorem.

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
