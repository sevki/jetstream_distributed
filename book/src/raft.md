# Raft: buying the atomic registry

[Ownership](ownership.md)'s strongest assumption is that the owner record is updated
atomically, so that two coordinators cannot both read `Owned { A, 41 }` and allocate
epoch 42 for different successors. A real deployment has to buy that from consensus,
or from a store with compare-and-swap. Raft is the first half of buying it.

> **Status: not connected.** Nothing outside `src/raft/` imports Raft. The registry
> the ownership service runs is a process-local record with a durable epoch floor.
> This chapter is about what Raft proves and where the connection would go, not about
> a connection that exists.

## The same statement, bought differently

Raft's Election Safety is the exclusivity theorem with two words changed:

```text
ownership:  at most one authoritative owner per epoch, because a single
            atomic registry hands the epoch out
raft:       at most one leader per term, because any two quorums share a
            voter and a voter votes once per term
```

The difference is why both are here. Ownership's exclusivity is **structural**: two
owners is not a state. In Raft nothing is structural. A cluster can perfectly well hold
two servers who both believe they lead term 7. Ruling that out is a **counting**
argument over a set that no single participant can see. Side by side, the two say what a
coordinator costs.

The argument is three sentences, and the interesting clause is the one not in them:
a cast vote is never ahead of its voter's term. Without it the induction fails at the
most ordinary step in the protocol, a server timing out into term `t + 1` and voting for
itself there.

## The log

The model has a log. A client request stamps an entry with its leader's term; append
carries one entry under the consistency check and truncates whatever diverged; commit
advances under figure 8's restriction; a vote carries the up-to-date comparison.

What follows from a *single step* (a leader only appends, a follower agrees before it
accepts, an entry is copied and not invented, a commit needs a majority of the
committing leader's own term) is the easy part. **Log Matching is proved too**, and it
needed something the model did not have:

> Ruling out a second entry at the same `(index, term)` is a fact about the **run's
> history**, not about any one state. Nothing in the *state* says no leader of that
> term ever appended at that index before.

So the cluster carries **ghost fields**, each added because some question about the run
has no answer in a single state: every `(server, term)` ever led; every entry any leader
ever created, with the term of the entry before it; every entry any leader ever
committed (the commit counter *retreats*, so a count cannot record it); and every vote
together with the voter's log as it stood when the vote was cast.

## State Machine Safety, with one hypothesis

State Machine Safety is proved with **exactly one hypothesis**: that two commits at an
index agree on the entry's *term*. The value half is unconditional, because one
`(term, index)` names one act of creation by one leader. Nothing about values, quorums
or counting is missing; what remains is the induction hypothesis over leaders of terms,
stated as one and with its upper endpoint still owed.

## The durable log

The log's storage is verified at the encoding level: recovery is exact, a crash can only
rewind, and a byte prefix of the device parses back to a record prefix, so figure 2's
suffix deletion is implementable on a device that deletes nothing.

It is **not wired to a device**, and the obstacle is a crash model, not an interface:
the persistent-memory log's chunk size is 8 and a write must be safe for *any subset* of
8-byte chunks having flushed, which POSIX does not promise for a write crossing a chunk.
Until a device supplies that, the vendored log's two corruption assumptions are not
assumptions of anything proved here.

## Where the connection would go

Said as a design direction, not a plan: the registry's record is the state a replicated
log would carry, and the epoch-advancing transitions are the entries. Three things stand
between here and there, and none is built:

1. A state machine on top of the log. The model's server has a log and a commit count
   and no applied state: it proves the log, not what is applied from it.
2. The ownership registry reading and writing through it, instead of through a lock.
3. A device for the log, for the crash-model reason above.

Until then, the honest statement is that ownership's atomicity is assumed and Raft's
consensus is proved, and the two do not yet touch.

The Raft rows (C1 onward) are in the README's
[Raft section](https://github.com/sevki/jetstream_distributed/blob/main/README.md#raft-the-same-statement-bought-by-counting).

Next: [SWIM](swim.md), which does not try to agree on anything.
