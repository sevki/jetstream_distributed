//! The mailbox in front of an actor: a queue, and the protocol that wakes
//! whoever drains it.
//!
//! This defines only the machine. It makes no claims about it; those are in
//! [`crate::actor::mailbox::proofs`].
//!
//! # Why a mailbox needs a protocol at all
//!
//! The actor's own model ([`crate::actor::model`]) treats the network as a set of
//! messages that may be offered to the host any number of times, and says
//! nothing about how a host comes to *look*. A real mailbox is a queue, and a
//! queue has a cost the set hides: the thing that drains it must be running when
//! a message arrives, and must not be running when none does, or it burns a
//! thread to watch an empty queue. So the drain is **scheduled** — woken by the
//! sender that finds it asleep — and the question is whether a message can be
//! enqueued and the wakeup lost. Every sender checks, then acts, then someone
//! else acts between the two.
//!
//! The machine is the protocol that Apple's swift-distributed-actors keeps as a
//! PlusCal/TLA+ model (`Models/mailbox.tla`), with the same three flags and the
//! same step boundaries:
//!
//! * `has` — *messages have been enqueued since the drain last looked*;
//! * `processing` — *the drain is running*;
//! * `scheduled` — *the drain has been asked to run*.
//!
//! A sender does three things, **each its own step**, because the bug the
//! protocol exists to avoid lives between them:
//!
//! 1. [`mb_enqueue`] — put the message on the queue;
//! 2. [`mb_set_state`] — read `has` into `had`, then set it;
//! 3. [`mb_schedule`] — if `had` was clear and the drain is not running, ask it
//!    to run.
//!
//! The drain does three:
//!
//! 1. [`mb_claim`] — once scheduled: mark `processing`, clear `has` so a message
//!    that arrives from now on is noticed;
//! 2. [`mb_drain`] — take everything in the queue and process it;
//! 3. [`mb_finish`] — if `has` was set meanwhile, stay scheduled; otherwise go
//!    back to sleep.
//!
//! # What differs from the TLA+ model
//!
//! The TLA+ model has two senders that each send five messages and a drain that
//! stops after ten, so that a model checker can exhaust it. Here a sender is not
//! a process but an *operation*: [`mb_enqueue`] starts one and its own
//! `set_state` and `schedule` steps finish it, tracked in [`Mailbox::ops`]. A
//! sender that enqueues again is a new operation, so any number of senders, each
//! sending any number of messages, are covered at once; the bound is what the
//! proofs remove.
//!
//! Messages are the actor's [`Envelope`]s, and a sender numbers them from zero
//! at [`mb_enqueue`] — the same numbering the actor's accept guard counts.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::model::Envelope;
use crate::id::Id;

verus! {

/// Where the drain is in its loop.
pub enum Dq {
    /// Asleep, or waiting to be scheduled.
    Await,
    /// Scheduled, and has marked itself `processing`.
    Claimed,
    /// Has taken the queue; has not yet decided whether to sleep.
    Drained,
}

/// How far a sender's operation has got after its message is on the queue.
pub enum Stage {
    /// Enqueued; has not yet touched the flags.
    Marked,
    /// Has set `has`, remembering what it was.
    Scheduling { had: bool },
}

/// The mailbox.
pub struct Mailbox {
    /// Messages waiting to be drained, oldest first.
    pub queue: Seq<Envelope>,
    /// Messages the drain has taken, in the order it took them.
    pub processed: Seq<Envelope>,
    /// Messages have been enqueued since the drain last looked.
    pub has: bool,
    /// The drain is running.
    pub processing: bool,
    /// The drain has been asked to run.
    pub scheduled: bool,
    /// Where the drain is.
    pub dq: Dq,
    /// Senders that have enqueued and have not finished, by message.
    pub ops: Map<Envelope, Stage>,
    /// Each sender's next sequence number. A sender absent from the map is at 0.
    pub next_seq: Map<Id, nat>,
}

/// The sequence number `sender`'s next message carries.
pub open spec fn mb_seq(m: Mailbox, sender: Id) -> nat {
    if m.next_seq.contains_key(sender) { m.next_seq[sender] } else { 0 }
}

/// Where everything starts: nothing queued, nothing flagged, the drain asleep.
pub open spec fn mb_init(m: Mailbox) -> bool {
    &&& m.queue =~= Seq::<Envelope>::empty()
    &&& m.processed =~= Seq::<Envelope>::empty()
    &&& !m.has
    &&& !m.processing
    &&& !m.scheduled
    &&& m.dq is Await
    &&& m.ops =~= Map::<Envelope, Stage>::empty()
    &&& m.next_seq =~= Map::<Id, nat>::empty()
}

/// A sender puts a message on the queue, numbered after its last.
pub open spec fn mb_enqueue(pre: Mailbox, post: Mailbox, sender: Id, body: nat) -> bool {
    let env = Envelope { sender, seq: mb_seq(pre, sender), body };
    post == Mailbox {
        queue: pre.queue.push(env),
        ops: pre.ops.insert(env, Stage::Marked),
        next_seq: pre.next_seq.insert(sender, env.seq + 1),
        ..pre
    }
}

/// What a sender saw when it set `has`; `false` for one that has not yet.
pub open spec fn stage_had(s: Stage) -> bool {
    match s {
        Stage::Scheduling { had } => had,
        Stage::Marked => false,
    }
}

/// The sender's operation for `env` is `Marked`.
pub open spec fn marked(m: Mailbox, env: Envelope) -> bool {
    m.ops.contains_key(env) && m.ops[env] is Marked
}

/// The sender's operation for `env` has set `has`, and saw `had`.
pub open spec fn scheduling(m: Mailbox, env: Envelope, had: bool) -> bool {
    m.ops.contains_key(env) && m.ops[env] == (Stage::Scheduling { had })
}

/// The sender's operation for `env` has set `has`.
pub open spec fn is_scheduling(m: Mailbox, env: Envelope) -> bool {
    m.ops.contains_key(env) && m.ops[env] is Scheduling
}

/// The sender reads `has` and sets it.
pub open spec fn mb_set_state(pre: Mailbox, post: Mailbox, env: Envelope) -> bool {
    &&& marked(pre, env)
    &&& post == Mailbox {
        has: true,
        ops: pre.ops.insert(env, Stage::Scheduling { had: pre.has }),
        ..pre
    }
}

/// The sender asks the drain to run — **if** `has` was clear when it set it, and
/// the drain is not already running.
///
/// Both halves matter. A sender that finds `has` already set leaves the wakeup to
/// whoever set it; a sender that finds the drain running leaves it to the drain's
/// last step, which looks at `has` again.
pub open spec fn mb_schedule(pre: Mailbox, post: Mailbox, env: Envelope) -> bool {
    &&& is_scheduling(pre, env)
    &&& post == Mailbox {
        ops: pre.ops.remove(env),
        scheduled: pre.scheduled || (!stage_had(pre.ops[env]) && !pre.processing),
        ..pre
    }
}

/// The drain wakes: marks itself running, and clears `has` so that anything
/// enqueued from now on is seen by its last step.
pub open spec fn mb_claim(pre: Mailbox, post: Mailbox) -> bool {
    &&& pre.dq is Await
    &&& pre.scheduled
    &&& post == Mailbox { processing: true, has: false, dq: Dq::Claimed, ..pre }
}

/// The drain takes everything in the queue and processes it, in order.
pub open spec fn mb_drain(pre: Mailbox, post: Mailbox) -> bool {
    &&& pre.dq is Claimed
    &&& post == Mailbox {
        processed: pre.processed + pre.queue,
        queue: Seq::empty(),
        dq: Dq::Drained,
        ..pre
    }
}

/// The drain decides whether to sleep: it stays scheduled exactly when `has` was
/// set while it was running.
pub open spec fn mb_finish(pre: Mailbox, post: Mailbox) -> bool {
    &&& pre.dq is Drained
    &&& post == Mailbox { scheduled: pre.has, processing: false, dq: Dq::Await, ..pre }
}

/// Nothing happens. Without it a run in which nothing is enabled would not be a
/// run, and "the drain stays asleep" could not be said.
pub open spec fn mb_stutter(pre: Mailbox, post: Mailbox) -> bool {
    post == pre
}

/// Every kind of step.
pub enum MbStep {
    Enqueue { sender: Id, body: nat },
    SetState { env: Envelope },
    Schedule { env: Envelope },
    Claim,
    Drain,
    Finish,
    Stutter,
}

/// One step of the machine.
pub open spec fn mb_step(step: MbStep, pre: Mailbox, post: Mailbox) -> bool {
    match step {
        MbStep::Enqueue { sender, body } => mb_enqueue(pre, post, sender, body),
        MbStep::SetState { env } => mb_set_state(pre, post, env),
        MbStep::Schedule { env } => mb_schedule(pre, post, env),
        MbStep::Claim => mb_claim(pre, post),
        MbStep::Drain => mb_drain(pre, post),
        MbStep::Finish => mb_finish(pre, post),
        MbStep::Stutter => mb_stutter(pre, post),
    }
}

/// The transition relation: some step.
pub open spec fn mb_next(pre: Mailbox, post: Mailbox) -> bool {
    exists|step: MbStep| #[trigger] mb_step(step, pre, post)
}

} // verus!
