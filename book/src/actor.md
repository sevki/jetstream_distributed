# The actor: a journal fenced by ownership

A single-process actor is single-threaded by construction, so it never has to say what
it guarantees. Spread over machines it does. The guarantees are the ones a single
process gets for free: **one thing at a time**, **each message once**, **in the order
sent**, and **state that survives** moving.

## One decision

The actor's state is **not held by its host**. It is a *journal*, the ordered sequence of
messages the actor has accepted, and the state is a fold over it. Appending to the
journal is the one thing a host does that matters, and it is fenced by
[ownership](ownership.md):

```text
as_accept(host, epoch, message) requires  can_mutate(ownership, host, epoch)
```

`can_mutate` is `Owned { host, epoch }` and nothing else. A host that is not the owner,
or owns a superseded generation, cannot append. The actor needs no second fence of its
own: the journal write *is* the mutation the ownership protocol fences.

This is the actor's relationship to ownership in one line, and it is why the actor's
exclusivity theorems are ownership's, used as they are.

## Everything else follows from three facts

1. Only the owner at the current epoch can append (ownership's exclusivity and
   fencing).
2. An append is accepted only if the message's sequence number is **exactly** the number
   already accepted from its sender. A duplicate and a message ahead of its turn are the
   same refusal.
3. The journal is only ever extended.

The network may delay, duplicate and reorder. The set of sent messages never shrinks, so
a message can be offered to the host any number of times in any order. That is not a
separate failure mode: it is what the accept guard is already quantified over.

## What a handover does to the actor

Nothing, to the state. The new owner does not receive the state from the old one. It
reads the same journal and recomputes. The journal records which host accepted each entry
and under which epoch, but neither is needed to *compute* the state.

That is why the claims split cleanly:

| Group | Says | Rows |
| --- | --- | --- |
| Exclusive | at most one host can accept at any instant; a superseded host cannot; nobody accepts between owners; nothing is written under an epoch the actor has left | A1–A7 |
| Delivery | nothing is invented; the *n*th message from a sender is numbered *n*; a message is accepted at most once; a redelivery and an early arrival are both refused | A8–A11 |
| State | the journal is append-only; the state is a fold and survives a handover | A12–A13 |
| Executable | the steps agree with the model in both directions | A14 |
| Not vacuous | one concrete run through a whole handover, ending with two hosts in one journal | A15 |

## The message

A message is an envelope: who sent it, the sender's number for it, and a body of bytes.
The actor's behaviour folds over the body's bytes, because a call to another actor is a
request encoded for it. The sender's counter is a `u64`, so `Send` is enabled only while
it is below `u64::MAX`: the model's numbers are the machine's, and a sender that has used
them all is refused rather than wrapped, because a wrapped counter would repeat a number
and the accept guard would take the repeat for a duplicate.

**The caller numbers its own messages.** A retry after a lost reply is therefore the
same `(sender, seq)` and not a second message. The host refuses an envelope naming anyone
but the connection's caller, a reused number with a different body, a number out of turn,
and a body over the wire's limit.

> **Direction, not built.** The settled direction is that an envelope carries the
> **receiver's** id as well as the sender's, so that one connection can carry several
> actors. Today the envelope has no receiver, and the other calls (`poll`, `acquire`,
> `accept`, `state`, `journal`) name no actor either. Numbering would then be per
> (sender, receiver) pair. See [the actor system](actor-system.md).

## What is not claimed

- **Safety only.** Nothing says a message is ever delivered, or that a sender retries. An
  out-of-order arrival is *refused*, not buffered, so something must retry in order for
  anything to progress. That something is [the mailbox](mailbox.md).
- **The journal is assumed durable and linear.** The model has no crash that loses an
  accepted entry, and the service's journal is in memory: the guarantees hold for the life
  of the process and not across its death.
- **The service refines crash-free executions only**, for the reason the composed service
  does.
- **The behaviour is a pure fold.** What a message *does* beyond changing the state, an
  effect or a reply, is not modelled, and neither is what an effect does if its host is
  fenced halfway through.

The proof files are `exclusive`, `delivery`, `state`, `refinement` and `scenario` under
`src/actor/proofs/`, all resting on one inductive invariant of six clauses. The rows are
in the Reference's
[actor section](reference/actor.md#actor-a-journal-fenced-by-ownership).

Next: [the mailbox](mailbox.md).
