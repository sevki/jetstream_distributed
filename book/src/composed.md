# Composed: the two as one machine

[Ownership](ownership.md) says who may mutate. [Raymond](raymond.md) routes a
privilege. Composed is the only place the two meet, and it meets them with
**guards**, not assumptions.

## Why a predicate is not enough

`couples(r, s)` says every node that may mutate holds the privilege. Stated as a
predicate it is a hypothetical: the routing layer never sees the ownership state, so
a routing step that moves the token has no way to know a node still has authority.
The question "does token transfer preserve ownership safety?" has no answer until
there is one machine in which both kinds of step happen.

## The synchronisation is a guard

Composed defines one state machine over both layers. The steps that touch both are
guarded:

| Step | Guard | Why |
| --- | --- | --- |
| `PassToken` | the actor is `Unowned` | Ownership must be genuinely released before the privilege may move. `Transferring` is also "not owned", so guarding on that weaker condition would let the token move while the outgoing owner had not acknowledged the revoke |
| `AcquireUnderToken` | the node *holds* the token | Authority cannot be taken by a node routing has not elected |
| `SeizeToken` | none on the holder | Re-establishes the token at another node **without the holder acting**: crash takeover |

Two carrier steps pass everything else through: `Ray` carries every Raymond step that
does not move the token (request routing, entering and leaving the critical section),
and `Own` carries every ownership transition that does not create authority over the
actor.

`Ray` is guarded on "preserves the token", deliberately wider than "is a routing
step". Had it admitted only routing, no execution could enter a critical section, every
reachable state would keep `using` false, and the theorems would cover a degenerate
fragment. A scenario that builds an execution from the initial state to one with a
node inside the critical section rules that out the only way that counts: by
exhibiting it.

## What is then provable

`couples` becomes an **invariant of the machine** rather than a side condition: in
every reachable composed state the only node that may mutate the actor is the node
holding the token. Because the guards are what enforce it, "token transfer preserves
ownership safety" is a claim about the system and not a hypothetical.

`SeizeToken` matters for the same reason. Without it the only token movement was a
voluntary pass, so the invariant was quantified over executions where the token always
moves politely. Crash-driven takeover, which is the case epochs exist for, was not among
them. A scenario exhibits the crash takeover as a reachable execution.

A seizure leaves the old holder believing it still holds the privilege. The composed
steps keep **reconciliation debts**: the nodes that owe a reconciliation after being
seized from. That is the executable form of "a stale holder whose belief nobody could
correct", and `reconcile` is what clears it.

## The executable side

The composed steps over both layers' records (`pass_token`, `seize_token`,
`acquire_under_token`, `reconcile`) are verified code whose contracts are the composed
model's steps. The coupling guards agree with the model in both directions, and a step
a layer already proved is carried without a second proof.

## What is not claimed

- **The composed service refines the crash-free executions only.** The composed model
  guards some steps on `own.live`, which is ground truth and not something a process
  can evaluate. The service has no `Crash` or `Recover`, so liveness of a node is a
  hypothesis for the steps that name a node that is not the caller. Seizing from a holder
  that is merely unreachable is inside the fragment, because `SeizeToken` has no liveness
  guard on the node it takes the privilege from.
- **Both layers live behind one gate in one process.** The `Coordinator` serialises
  them because the coupling reads both. It checks the rules; it does not distribute them.
- **The nodes involved must be live for a recipient or a seizure target.** The service's
  identity lookup speaks only for the *caller*, and a recipient of a passed privilege is
  not a caller, so nothing in the service establishes that for them.

The rows are CX1 and CX2 and the composed rows in the README's
[claims table](https://github.com/sevki/jetstream_distributed/blob/main/README.md#claimed-invariants-and-the-proofs-that-establish-them).

Next: [Raft](raft.md), which is about the assumption this chapter, like the last one,
leaned on.
