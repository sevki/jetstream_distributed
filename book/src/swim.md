# SWIM: membership by merge

[Ownership](ownership.md) and [Raft](raft.md) both spend a majority round trip to get
one authoritative answer. SWIM does not try to agree on anything. Every node keeps its
own view of who else is alive, the views disagree constantly, and the only promise is
that disagreements **resolve rather than compound**.

That is a different kind of promise, bought a different way: by an algebraic property
of a merge rule, not by quorum intersection and not by structure.

## The record and the rule

A member record is an **incarnation number** and a **status**: `Alive`, `Suspect` or
`Dead`. Two records are compared by a key: a higher incarnation always wins, and at
equal incarnations the more-dead status wins. `merge` keeps whichever side has the
larger key. That is the entire rule.

A probe timeout or a self-refutation is not a different rule. Each is only a different
choice of *which record arrived*:

- A probe that times out makes the node believe the peer `Suspect`, at the incarnation it
  had recorded **when the probe began**. The incarnation is an argument and is not re-read,
  because a probe is slow and a refutation can land while it is in flight. A suspicion at
  the old incarnation then loses to the refutation and changes nothing.
- A node that hears it is accused answers with a record **one incarnation higher**. Alive
  at a higher incarnation beats suspect and dead at the accusation's.

## What is proved

The claims are S1 to S12 in the Reference. In words:

| | claim |
| --- | --- |
| S1–S4, S6 | merge is idempotent, absorbs a repeat, never accepts a record that does not out-rank the local one, and is commutative and associative |
| S5 | across a whole run, **no node's record about any peer ever moves backward**: the actual convergence argument |
| S7–S9 | the executable merge is the model's; a refutation is a gossip step and out-ranks what it answers |
| S10–S12 | the node's table learns by the model's gossip step, and never believes less than it did |

Idempotence and absorbing a repeat are what let gossip's real delivery model, at least
once and arbitrarily duplicated, survive contact with `merge` at all. Commutativity and
associativity are what make order not matter. S5 is what those add up to once lifted
through every step of an execution: not that gossip arrives in order, or even that it
arrives, only that whatever arrives never makes a view *less accurate* than it was.

## What is not modelled

- **No probe scheduler, no indirect-ping fallback, no dissemination budget.** The model is
  the merge rule and one transition. How often to probe, and what to piggyback, is not
  modelled, so nothing here says gossip *eventually arrives*.
- **No voluntary leave.** A graceful departure and a failure-detected one have different
  precedence and rejoin rules in memberlist. Here the status covers failure detection
  only, so a node that leaves on purpose is not representable, rather than
  misrepresented as a failure.
- **A node writes nothing down.** Incarnations are self-correcting: a restarted node
  begins at 0, and the first peer to tell it what the cluster believes about it out-ranks
  its record and is answered with a higher incarnation. A restart costs a round trip, not
  correctness.

## The service

`Node` is the shell around a verified table: the roster, the lock, the audit log, the
batch limit and the order a batch is applied in are plain Rust that the tests exercise.
Suspecting a peer, declaring it dead and refuting an accusation are **not on the wire**.
They are things a node does about its own view, and putting them on the wire would let
any caller make this node believe anything. A node suspects a peer because *its own*
probe failed.

## How it relates to the rest

SWIM is independent of the other protocols in the proofs. It is related to them in one
direction, and only as a **hint**:

- Ownership assumes failure detection is unreliable, and survives a revoke of a healthy
  node. SWIM's `Suspect` and `Dead` are exactly that kind of signal.
- The [actor system](actor-system.md) reads a SWIM view to decide where *not* to place
  new work and which addresses to stop returning. It never uses it to decide an actor has
  moved. That is the ownership epoch's job.

The SWIM rows are in the Reference's
[SWIM section](reference/swim.md#swim-gossip-membership-bought-by-merge-rather-than-majority).

Next: [the actor](actor.md), which sits on ownership.
