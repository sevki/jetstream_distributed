# Ownership: epochs and fencing

Ownership is the base. Everything else in this book either uses it (the actor),
is tied to it (Raymond, through Composed), or is a way to satisfy its assumptions
(Raft).

## The state machine

An actor is, at any moment, in one of three states:

```text
Owned        { owner, epoch }
Transferring { from, to, old_epoch, new_epoch }
Unowned      { epoch, intended_owner }
```

Ownership never moves atomically. A handover is four transitions:

```text
Owned(A, 41)
      |  BeginTransfer(A -> B)         epoch 42 is allocated here
Transferring(A, B, 41, 42)
      |  CompleteRelease
Unowned(42, B)
      |  Acquire(B)
Owned(B, 42)
```

Two choices carry the whole design:

- **The epoch advances at the start of a handover, not the end.** From the moment `A`
  agrees to transfer, the current epoch is 42, so `A`'s epoch-41 authority is already
  fenced out. `A` does not need to be reachable, or alive, for that to take effect.
- **Nobody has authority during the middle two stages.** The design gives up
  availability during a handover so that double ownership is not representable.
  Neither node having authority is acceptable; both having it is not.

## Who may mutate

Authority is one predicate, true in exactly one shape:

```text
may_mutate(s, node, epoch) =
    s is Owned { owner, epoch: e }  and  node == owner  and  epoch == e
```

That is why exclusivity is **structural** here: two owners is not a state the model
can represent, so the work is in showing that no transition reaches a bad state.
Compare [Raft](raft.md), where nothing is structural and exclusivity is a counting
argument over a set that no participant can see.

A server checks an incoming request with `valid_fence(s, e) = e >= current_epoch(s)`.
While `Transferring`, the current epoch is the *new* one, which is what makes the
outgoing owner stale immediately.

## Tokens are physical; authority is not

A `Token { actor, epoch, holder }` can be copied, survives a crash, and can be held by
a node that was partitioned away for an hour. The model says so: the set of issued
tokens only grows. Whether a token confers authority is a separate question, answered
by the actor's *current* state. Stale tokens exist and are inert.

## What the proofs assume

The failure model is part of the system, not a side condition. The ones that matter
for how the layers fit together:

| Assumption | Why it matters elsewhere |
| --- | --- |
| **The owner record is updated atomically.** The strongest assumption in the model | This is the edge [Raft](raft.md) could satisfy, and does not yet |
| The network may duplicate, reorder, delay and lose messages | No later layer needs to add anything for these; the actor's delivery claims are quantified over them |
| Failure detection is unreliable | A revoke may fire at a healthy node. Safety comes from the epoch bump. This is why [SWIM](swim.md) can only be a hint |
| A handover may be interrupted at any point | An abort burns another epoch, so a grant for the abandoned epoch is already stale on arrival |
| Nodes are not Byzantine | No transition mints a token or forges a state |

**Not claimed: liveness.** Nothing says a transfer completes or that an actor ever
becomes owned again. Safety survives every case in the table; progress does not.

The full table, and every theorem with the name of its proof and what it assumes, is
in the README: [failure model](https://github.com/sevki/jetstream_distributed/blob/main/README.md#failure-model)
and [claimed invariants](https://github.com/sevki/jetstream_distributed/blob/main/README.md#claimed-invariants-and-the-proofs-that-establish-them).

## Prior art: Chubby

The fencing mechanism is Chubby's. A Chubby *sequencer* carries the lock name, mode
and **lock generation number**, and the resource server is expected to reject a stale
one. That is `Token` plus `valid_fence`, and the generation number is the model's
`Epoch`. What this repository adds is the proof, and the precision a proof forces:
who may mutate is one predicate, and "a node cannot fence itself" cannot stay implicit.
The README's [Relation to Chubby](https://github.com/sevki/jetstream_distributed/blob/main/README.md#relation-to-chubby)
is the careful version, including the three deliberate differences (no timing,
consensus assumed, peer-to-peer routing).

## The service

The ownership service is the model run over Jetstream. Three things about it matter
to the other chapters:

- **Identity comes from the connection, never from an argument.** No method takes a
  node number; the caller is the transport's `Context`. Today that is an address
  against a roster fixed at construction, and **an address is not a credential**: it
  is as good as one in the simulated network and worth little on a real one.
- **`force` is not on the wire.** It is the coordinator's own transition (revoking
  an owner), so a node-facing service does not offer it.
- **The registry survives restarts.** A process-local lock buys atomicity and none of
  survival, and a registry that forgets can move epochs backwards, which every fencing
  theorem forbids. So the starting epoch is read from a durable, monotone `EpochFloor`,
  and every burn is written down before the state that depends on it is visible. A
  registry that dies between the two skips an epoch, which is the safe direction to fail.

Next: [Raymond](raymond.md), which routes the privilege and is tied to this.
