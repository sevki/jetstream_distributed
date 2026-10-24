# How the algorithms relate

One page. Every later chapter is a closer look at one box.

## The picture

```text
   Raft                                   SWIM
   consensus                              membership by merge
   · · · · · · · · ·                      · · · · · · · · · ·
   :  could buy    :                      :  a hint to      :
   :  the atomic   :                      :  placement      :
   :  registry     :                      :  (QUIC system)  :
   ▼ · · · · · · · ·                      ▼ · · · · · · · · ·
 ┌───────────────────────┐   couples   ┌───────────────────┐
 │ Ownership             │◄────────────│ Raymond           │
 │ epochs, fencing       │             │ routes the        │
 │ "who may mutate"      │             │ privilege         │
 └───────────────────────┘             └───────────────────┘
      ▲            ▲                           ▲
      │ fences     └────────────┬──────────────┘
      │ the journal             │ guards tie the two
      │                    ┌────┴─────────────────┐
 ┌────┴─────────────┐      │ Composed             │
 │ Actor            │      │ one machine, both    │
 │ a journal, and   │      │ layers               │
 │ the state it     │      └──────────────────────┘
 │ folds to         │
 └────▲─────────────┘
      │ delivers to
 ┌────┴─────────────┐
 │ Mailbox          │
 │ the queue in     │
 │ front of it      │
 └──────────────────┘
```

Solid lines are relationships the code builds: one module imports or enforces the
other. Dotted lines are relationships that are *intended* or are a hint only. The
difference matters, and the rest of this page is mostly about it.

| Relationship | Built? |
| --- | --- |
| Raymond is tied to ownership by `couples`, and the two are one machine in Composed | Yes. `composed` imports both, and the coupling is a guard, not an assumption |
| The actor's journal is fenced by ownership | Yes. `as_accept` requires the ownership layer's `can_mutate` at the epoch the host presents |
| The mailbox sits in front of the actor | In the model, yes. `Host`, the journal service, is not behind it yet; see [the mailbox](mailbox.md) |
| Raft buys the atomic registry | **No.** Nothing outside `src/raft/` imports Raft. The registry is a process-local record |
| SWIM drives placement | A hint only, and only in the QUIC system. Nothing in the protocols depends on it |

## Three ways of getting one answer

The protocols do not agree on how to get a single authoritative answer in a system
where nobody can see everything. They buy it three different ways, and the
difference is the reason they are all here.

| | What it promises | How it is bought | What it assumes |
| --- | --- | --- | --- |
| **Ownership** | at most one authoritative owner per epoch | **structurally**: `may_mutate` is true in exactly one shape, so two owners is not a representable state | the owner record is updated *atomically* |
| **Raft** | at most one leader per term | **by counting**: any two quorums share a voter, and a voter votes once per term | nothing, for safety. Progress needs a reachable majority and is not claimed |
| **SWIM** | views converge and never get less accurate | **by merge**: an idempotent, commutative, associative rule, so order and duplication do not matter | nothing about timing or arrival; it does not claim gossip arrives |

Ownership is the one that depends on the others. Its strongest assumption is a
single atomic, durable registry. Raft is the standard way to make a record like
that fault-tolerant, which is why it is in the repository, and SWIM is the standard
way to *notice* that a node has gone, which ownership treats as unreliable by
construction (below).

## The relationships, one by one

### Ownership ← Raymond: routing never grants authority

Raymond routes a single *privilege* between peers. The ownership model says who may
mutate. The glue is one predicate:

```text
couples(r, s) = every node that may mutate in s holds the privilege in r
```

The direction is the point. Routing only *constrains* who could have authority; it
never creates it. So a duplicated or reordered request cannot manufacture an owner.
That is [Raymond](raymond.md)'s chapter.

### Composed: the guards are the relationship

On its own `couples` is only a predicate, and nothing stops a token moving out from
under an owner. [Composed](composed.md) defines one state machine over both layers
and turns the synchronisation into **guards**: the privilege may pass only once the
actor is `Unowned`, and a node may acquire only if it holds the privilege. Crash
takeover is a separate step (`SeizeToken`), so the safety claim is not restricted
to executions where the privilege always moves voluntarily.

### Ownership ← Actor: the journal write *is* the fenced mutation

An actor's state is not held by its host. It is a *journal* of accepted messages,
and the state is a fold over it. Appending is the one thing a host does that
matters, and the ownership layer fences it. So the actor's exclusivity theorems are
the ownership layer's, used as they are, and a handover moves no state: the new
owner reads the same journal and recomputes. See [the actor](actor.md).

### Actor ← Mailbox: refusing out of order needs something that retries in order

The actor refuses a message that arrives ahead of its turn rather than buffering it.
That is safe and also useless on its own, because nothing makes a refused message
arrive again. The mailbox is the queue that does, and it is where the first liveness
theorem lives, under a stated fairness assumption. See [the mailbox](mailbox.md).

### Ownership ⇢ Raft: the strongest assumption, and the one unbuilt edge

Ownership's first assumption is that the owner record is updated atomically, which
in a real deployment must be bought from consensus. Today the ownership service
buys *atomicity* from a process-local lock and *survival* from a durable, monotone
epoch floor, so a restarted registry cannot move epochs backwards. It does **not**
replicate. Raft proves Election Safety, Log Matching and State Machine Safety (with
one stated hypothesis), but nothing connects it to the registry. [Raft](raft.md)
says where the missing connection would go.

### SWIM ⇢ everything else: an unreliable detector, by design

Ownership does not trust failure detection. Its model lets the coordinator revoke a
perfectly healthy node, and safety has to survive that: it comes from the epoch bump,
not from the detector being right. SWIM's `Suspect` and `Dead` are exactly that kind
of signal, which is why using them as a **hint** is consistent with the proofs. In
the QUIC system a suspect host is not placed on and a dead one is not found, and
nothing moves an actor. See [SWIM](swim.md) and
[the actor system](actor-system.md).

## A pattern that repeats: belief versus authority

Three layers separate what a node *believes* from what is *so*, and the same
discipline keeps each safe:

| Layer | Belief | Authority | What stands between them |
| --- | --- | --- | --- |
| Ownership | a node's own view of its epoch | the registry's record | the fence is checked **where the effect lands**, not by the node about itself |
| Raymond | `believes_holds` | `has_token` | `is_stale_holder` is the gap, and seizure needs no cooperation from the stale holder |
| SWIM | a node's view of the others | what is actually up | views are only ever merged upward, and never trusted to decide ownership |

A node cannot fence itself. A partitioned owner accepts its own stale epoch, and the
rejection that matters happens at the resource. Every chapter that follows leans on
this.

## What is not related yet

Said plainly, because a map that implies edges that do not exist is worse than none:

- **Raft and ownership are not connected.** Nothing runs the registry on a replicated log.
- **Raymond and the composed services keep the global record in one process.** They
  check the rules; they do not distribute them.
- **`Host`, the journal service, does not sit behind the mailbox**, though the mailbox
  is proved in front of the model.
- **Nothing here proves liveness of a handover.** Safety survives every failure the
  model admits; progress does not.
- **No automatic failover.** Membership can say a host left. Nothing yet decides to
  move its actors, and doing so from a partition starts a second copy that only the
  ownership epoch keeps harmless.
