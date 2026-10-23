# The mailbox: getting messages to the actor

[The actor](actor.md) proves nothing about a message ever being *offered* to its host.
The mailbox is the queue that would offer it, and it is where the **lost-wakeup
problem** lives.

## The problem

A drain that is scheduled rather than polling must be woken by the sender that finds it
asleep. Every sender checks, then acts, with other senders and the drain acting in
between. Get the interleaving wrong and a message sits in the queue with nobody coming to
take it.

## The machine

The protocol is the one in Apple's swift-distributed-actors mailbox, which keeps it as a
PlusCal/TLA+ model, with the same three flags (`has`, `processing`, `scheduled`) and the
same step boundaries:

- A **sender** takes three steps: enqueue; read-and-set `has`; schedule, if `has` was
  clear and the drain is not running.
- The **drain** takes three: claim (clear `has`, mark running); take the queue; finish
  (stay scheduled exactly when `has` was set meanwhile).

The TLA+ model fixes two senders, five messages each, and a drain that stops after ten,
so a model checker can exhaust it. Here a sender is an *operation* tracked in the
mailbox's state rather than a process, so any number of senders each sending any number
of messages are covered at once. The bound is what the proof removes.

## Two kinds of claim

**Safety** is a corollary of one invariant: nothing is lost or reordered, each message is
taken in once, one sender's messages keep their order with no gaps, and the drain never
presents a message ahead of its turn (MB1–MB5).

The last of those is the link to the actor. The *i*th message processed is numbered the
count of its sender's messages among the *i* before it, **word for word the guard of the
actor's accept**. So a host accepting in this order is never refused for being early. The
mailbox hands the actor an *ordered* stream, and the ownership fence that decides whether
the actor may append it is [the actor's](actor.md), unchanged.

**Liveness** is a different kind of claim, and the proof says so. It is a statement about
the infinite run, it is false of the bare machine (a run in which the drain is never given
a turn processes nothing), and so it is stated under a fairness assumption written down
as a definition, not left implicit:

> In every run in which the drain's three steps and each sender's two remaining ones are
> not starved, a message on the queue is later processed. (MB6)

Senders are not required to send. The fairness is *weak* fairness and nothing stronger,
and it is an assumption about the scheduler that the protocol cannot enforce. Two runs
keep the theorem honest: a fair run that does work and satisfies the theorem (MB8), and
an unfair run in which a message is enqueued and never processed (MB9), which shows the
assumption is necessary.

The temporal logic the liveness proof is stated in (leads-to, weak fairness, the WF1
rule) is rebuilt in the crate, not depended on, because the verified build links `vstd`
and nothing else. Every rule is proved, not assumed (MB7).

## What runs

The queue and flags the runtime keeps behind its lock are a verified core
(`MailboxCore`), with one method per step and each method's contract the model's step
(MB10, MB11). Everything around it is plain Rust that the tests exercise:

- the lock, the capacity and permits, the wakers and the notification;
- `requeue`, which puts back what a dropped round never handed out, and is not a model
  step;
- the claim that callers follow the sender's three steps, which MB10 takes as a
  hypothesis and nothing checks.

## Where it is, and is not, in front of an actor

The mailbox is proved in front of the *model*. In the running system:

- `Host`, the journal service, is **not** behind it. The owning node calls `accept`.
- A hosted service **is**: the supervisor puts a mailbox in front of any service it runs
  and serves it one request at a time, in each sender's order. That is
  [the services chapter](services.md).
- Subscriptions are not served through the mailbox, and the reply path is not bounded.

Next: [Services over Jetstream](services.md).
