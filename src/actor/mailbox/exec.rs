//! The mailbox's protocol, executable and verified.
//!
//! [`crate::actor::mailbox::model`] is the protocol as a transition relation, and
//! [`crate::actor::mailbox::proofs`] proves what it keeps true. This is the
//! protocol as code: a [`MailboxCore`] that owns the queue and the three flags,
//! with one method per step, each of whose contract is the model's step.
//!
//! It is the counterpart of [`crate::actor::steps`] for the part of the mailbox
//! that has state. The runtime ([`crate::actor::service::Mailbox`]) wraps it in a
//! lock and adds what the model does not have — a capacity, slots reserved
//! against it, tasks waiting for one, a notification — and every step of the
//! protocol itself goes through this type, so the lock-protected thing is the
//! thing Verus checked.
//!
//! # What is verified here
//!
//! Each method's postcondition is a `core_*` relation, and
//! [`crate::actor::mailbox::proofs::refinement`] proves that relation is the
//! model's step: given a model state the core refines, a step of the core is a
//! step of the model to a state it still refines. A step that is refused is
//! refused where the model's is not enabled.
//!
//! The methods are **total**. Called out of order — `take` when the drain has not
//! claimed, `finish` when it has not taken — a method changes nothing, which is the
//! model's stutter step, rather than doing something the model has no name for.
//!
//! # What is not
//!
//! * **That callers follow the sender's protocol.** A sender's three steps are
//!   `enqueue`, then `set_state`, then `schedule` with what `set_state` returned.
//!   The model tracks that in `ops`; this type cannot, because its items are
//!   opaque. The refinement theorems take it as a hypothesis, and the runtime's
//!   `Permit` and `Session` are what discharge it, by being the only callers.
//! * **[`MailboxCore::requeue`]**, which is not a model step. It puts back, at the
//!   front, messages a round was dropped before handing out — a drain that
//!   panicked or was cancelled — and the model has no such failure. Its contract
//!   says what it does; the theorems do not cover it.
//! * Locking, capacity and wakeups, which are the runtime's.
#![allow(unused_imports)]
// The bodies are written in the forms Verus reasons about directly (`match` on a
// phase, `len() > 0`), not the ones clippy prefers.
#![allow(
    clippy::new_without_default,
    clippy::len_without_is_empty,
    clippy::match_like_matches_macro,
    clippy::single_match,
    clippy::len_zero
)]

use std::collections::VecDeque;

use vstd::prelude::*;

use crate::actor::mailbox::model::Dq;

verus! {

/// Where the drain is in its loop: the model's [`Dq`], executable.
#[derive(Clone, Copy)]
pub enum Phase {
    /// Asleep, or waiting to be scheduled.
    Await,
    /// Scheduled, and has marked itself running.
    Claimed,
    /// Has taken the queue; has not yet decided whether to sleep.
    Drained,
}

/// The model's [`Dq`] that a [`Phase`] stands for.
pub open spec fn dq_of(p: Phase) -> Dq {
    match p {
        Phase::Await => Dq::Await,
        Phase::Claimed => Dq::Claimed,
        Phase::Drained => Dq::Drained,
    }
}

/// The queue and the three flags. `processing`, which the model keeps as a flag,
/// is `phase` not being `Await`.
#[verifier::reject_recursive_types(T)]
pub struct MailboxCore<T> {
    /// Messages waiting to be drained, oldest first.
    pub queue: VecDeque<T>,
    /// Messages have been enqueued since the drain last looked.
    pub has: bool,
    /// The drain has been asked to run.
    pub scheduled: bool,
    /// Where the drain is.
    pub phase: Phase,
}

/// Nothing changed.
pub open spec fn core_stutter<T>(pre: MailboxCore<T>, post: MailboxCore<T>) -> bool {
    &&& post.queue@ == pre.queue@
    &&& post.has == pre.has
    &&& post.scheduled == pre.scheduled
    &&& post.phase == pre.phase
}

/// `mb_enqueue`, on the core: the message goes on the back of the queue.
pub open spec fn core_enqueue<T>(pre: MailboxCore<T>, post: MailboxCore<T>, item: T) -> bool {
    &&& post.queue@ == pre.queue@.push(item)
    &&& post.has == pre.has
    &&& post.scheduled == pre.scheduled
    &&& post.phase == pre.phase
}

/// `mb_set_state`, on the core: `has` is set.
pub open spec fn core_set_state<T>(pre: MailboxCore<T>, post: MailboxCore<T>) -> bool {
    &&& post.queue@ == pre.queue@
    &&& post.has
    &&& post.scheduled == pre.scheduled
    &&& post.phase == pre.phase
}

/// `mb_schedule`, on the core: scheduled if `had` was clear and the drain is not
/// running.
pub open spec fn core_schedule<T>(pre: MailboxCore<T>, post: MailboxCore<T>, had: bool) -> bool {
    &&& post.queue@ == pre.queue@
    &&& post.has == pre.has
    &&& post.scheduled == (pre.scheduled || (!had && pre.phase is Await))
    &&& post.phase == pre.phase
}

/// `mb_claim`'s guard: the drain is at the top of its loop and has been asked to
/// run.
pub open spec fn core_claim_enabled<T>(pre: MailboxCore<T>) -> bool {
    pre.phase is Await && pre.scheduled
}

/// `mb_claim`, on the core.
pub open spec fn core_claim<T>(pre: MailboxCore<T>, post: MailboxCore<T>) -> bool {
    &&& core_claim_enabled(pre)
    &&& post.queue@ == pre.queue@
    &&& !post.has
    &&& post.scheduled == pre.scheduled
    &&& post.phase is Claimed
}

/// `mb_drain`, on the core: the whole queue goes to the drain, in order.
pub open spec fn core_take<T>(pre: MailboxCore<T>, post: MailboxCore<T>, taken: Seq<T>) -> bool {
    &&& pre.phase is Claimed
    &&& taken == pre.queue@
    &&& post.queue@ == Seq::<T>::empty()
    &&& post.has == pre.has
    &&& post.scheduled == pre.scheduled
    &&& post.phase is Drained
}

/// `mb_finish`, on the core: scheduled exactly when `has` was set meanwhile.
pub open spec fn core_finish<T>(pre: MailboxCore<T>, post: MailboxCore<T>) -> bool {
    &&& pre.phase is Drained
    &&& post.queue@ == pre.queue@
    &&& post.has == pre.has
    &&& post.scheduled == pre.has
    &&& post.phase is Await
}

impl<T> MailboxCore<T> {
    /// `mb_init`: nothing queued, nothing flagged, the drain asleep.
    pub fn new() -> (core: MailboxCore<T>)
        ensures
            core.queue@ == Seq::<T>::empty(),
            !core.has,
            !core.scheduled,
            core.phase is Await,
    {
        MailboxCore { queue: VecDeque::new(), has: false, scheduled: false, phase: Phase::Await }
    }

    /// How many messages are queued.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self.queue@.len(),
    {
        self.queue.len()
    }

    /// `mb_enqueue`: put the message on the back of the queue.
    pub fn enqueue(&mut self, item: T)
        ensures
            core_enqueue(*old(self), *final(self), item),
    {
        self.queue.push_back(item);
    }

    /// `mb_set_state`: read `has` and set it. Returns what it was.
    pub fn set_state(&mut self) -> (had: bool)
        ensures
            had == old(self).has,
            core_set_state(*old(self), *final(self)),
    {
        let had = self.has;
        self.has = true;
        had
    }

    /// `mb_schedule`: ask the drain to run — **if** `had` is clear and the drain is
    /// not running.
    ///
    /// `had` is what [`MailboxCore::set_state`] returned for the same message.
    pub fn schedule(&mut self, had: bool)
        ensures
            core_schedule(*old(self), *final(self), had),
    {
        let asleep = match self.phase {
            Phase::Await => true,
            _ => false,
        };
        if !had && asleep {
            self.scheduled = true;
        }
    }

    /// `mb_claim`: once scheduled, mark the drain running and clear `has`, so that
    /// a message that arrives from now on is noticed by [`MailboxCore::finish`].
    /// Returns whether it did; if not, nothing changed.
    pub fn claim(&mut self) -> (claimed: bool)
        ensures
            claimed == core_claim_enabled(*old(self)),
            if claimed {
                core_claim(*old(self), *final(self))
            } else {
                core_stutter(*old(self), *final(self))
            },
    {
        let ready = match self.phase {
            Phase::Await => self.scheduled,
            _ => false,
        };
        if ready {
            self.has = false;
            self.phase = Phase::Claimed;
        }
        ready
    }

    /// `mb_drain`: take everything in the queue, in order. Out of phase — the
    /// drain has not claimed — it takes nothing and changes nothing.
    pub fn take(&mut self) -> (taken: VecDeque<T>)
        ensures
            if old(self).phase is Claimed {
                core_take(*old(self), *final(self), taken@)
            } else {
                core_stutter(*old(self), *final(self)) && taken@ == Seq::<T>::empty()
            },
    {
        let mut taken = VecDeque::new();
        match self.phase {
            Phase::Claimed => {
                std::mem::swap(&mut self.queue, &mut taken);
                self.phase = Phase::Drained;
            },
            _ => {},
        }
        taken
    }

    /// `mb_finish`: stay scheduled exactly when `has` was set while the drain ran,
    /// and otherwise go back to sleep. Returns whether it stays scheduled. Out of
    /// phase — the drain has not taken the queue — it changes nothing.
    pub fn finish(&mut self) -> (scheduled: bool)
        ensures
            scheduled == final(self).scheduled,
            if old(self).phase is Drained {
                core_finish(*old(self), *final(self))
            } else {
                core_stutter(*old(self), *final(self))
            },
    {
        match self.phase {
            Phase::Drained => {
                self.scheduled = self.has;
                self.phase = Phase::Await;
            },
            _ => {},
        }
        self.scheduled
    }

    /// **Not a model step.** Put back, at the front of the queue and ahead of
    /// anything that arrived since, messages a round was dropped before handing
    /// out, and note that there are some so that [`MailboxCore::finish`] stays
    /// scheduled.
    ///
    /// The model's drain takes the whole queue and the messages are processed; a
    /// running drain can also panic or be cancelled in between, and then they must
    /// not vanish with it — their senders are waiting on an answer. The refinement
    /// theorems do not cover this method; its contract is what it is.
    pub fn requeue(&mut self, rest: VecDeque<T>)
        ensures
            final(self).queue@ == rest@ + old(self).queue@,
            final(self).has == (old(self).has || rest@.len() > 0),
            final(self).scheduled == old(self).scheduled,
            final(self).phase == old(self).phase,
    {
        if rest.len() > 0 {
            let mut front = rest;
            front.append(&mut self.queue);
            self.queue = front;
            self.has = true;
        }
    }
}

} // verus!
