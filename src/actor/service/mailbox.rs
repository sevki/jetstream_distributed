//! The mailbox, executable: [`crate::actor::mailbox::model`] with its steps run
//! on real threads, and a bound on how many messages it will hold.
//!
//! The model's state is the queue and three flags, and every step is atomic with
//! respect to the others: a sender's `set_state` reads `has` and sets it in one
//! step, the drain's `claim` clears it in one step, and the bug the protocol
//! exists to avoid lives *between* a sender's steps, not inside one. So the
//! state here is one value behind one lock, each method below takes the lock
//! once and is exactly one step, and the lock is never held across two of them.
//!
//! | model step | method | by |
//! | --- | --- | --- |
//! | `mb_enqueue` | [`Permit::enqueue`] | a sender |
//! | `mb_set_state` | [`Mailbox::set_state`] | a sender |
//! | `mb_schedule` | [`Mailbox::schedule`] | a sender |
//! | `mb_claim` | [`Mailbox::claim`] | the drain |
//! | `mb_drain` | [`Mailbox::take`] | the drain |
//! | `mb_finish` | [`Mailbox::finish`] | the drain |
//!
//! [`Mailbox::send`] runs a sender's three steps back to back, which is one
//! interleaving among the ones the model allows; a [`Sink`](futures::Sink) that
//! enqueues in `start_send` and finishes in `poll_flush` is another.
//!
//! The mailbox is a handle: clones share the one queue, so any number of senders
//! hold one each, and the single drain loop holds another. What a message *is* is
//! the caller's business — the model's `Envelope` numbers messages per sender, and
//! that numbering is the caller's too.
//!
//! # Backpressure
//!
//! The mailbox holds at most as many messages as its [`Capacity`], and the caller
//! says which: a default would be a silent choice of where senders start to wait,
//! and a bare number would make `0` a silent choice of never waiting. Saying
//! [`Capacity::Unbounded`] is a thing you wrote on purpose. A sender
//! first takes a [`Permit`] — a slot reserved for its message — and a full
//! mailbox makes it wait for one ([`Mailbox::reserve`], [`Mailbox::poll_reserve`]),
//! or refuses it ([`Mailbox::try_reserve`]). Only a sender holding a permit can
//! enqueue, so enqueueing never fails and never blocks. A slot comes back when
//! the drain takes the queue, or when a permit is dropped unused.
//!
//! The model's queue is unbounded, and a full mailbox is a sender that has not
//! yet *begun* its operation: no step of the protocol happens, which the model
//! reads as a stutter. So the safety proofs carry over unchanged. The liveness
//! theorem owes progress only to operations already begun, and a sender waiting
//! for a permit has not begun one. That is an argument about the mapping, not a
//! proof; nothing here is checked against it by Verus.
//!
//! **A bound is a place to deadlock.** The drain runs one message at a time, so a
//! handler that waits on an actor whose handler is waiting on it holds both
//! drains whatever the capacity. A bounded mailbox adds a second way in: a
//! sender inside a handler that waits for a permit on a full mailbox. Do not wait
//! on another actor inside a turn that another actor can be waiting on. An
//! unbounded mailbox closes the full-queue way in and not the other.
//!
//! # What is not claimed
//!
//! This is a transcription, not a refinement: nothing here is checked against
//! the model by Verus, and the claim that it behaves like the model rests on each
//! method being the model step it is named for, and on the tests below. It is the
//! same line [`crate::actor::mailbox`] draws: the protocol is proved, connecting
//! it to running code is this file.

use std::collections::VecDeque;
use std::future::poll_fn;
use std::num::NonZeroU32;
use std::sync::{Arc, Mutex};
use std::task::{self, Poll, Waker};

use tokio::sync::Notify;

struct State<T> {
    /// Messages waiting to be drained, oldest first.
    queue: VecDeque<T>,
    /// Slots promised to a [`Permit`] and not yet used.
    reserved: u64,
    /// Senders waiting for a slot.
    waiting: Vec<Waker>,
    /// Messages have been enqueued since the drain last looked.
    has: bool,
    /// The drain is running.
    processing: bool,
    /// The drain has been asked to run.
    scheduled: bool,
}

/// How many messages a [`Mailbox`] holds before a sender has to wait.
///
/// There is deliberately no `Default`, and no number that means "no limit".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Capacity {
    /// At most this many, counting the slots reserved and not yet used.
    Bounded(NonZeroU32),
    /// No limit: every reservation succeeds, and a slow actor's queue grows
    /// without one.
    Unbounded,
}

struct Shared<T> {
    state: Mutex<State<T>>,
    capacity: Capacity,
    /// Rings when `scheduled` becomes true. A permit is stored if nobody is
    /// waiting, so a wakeup that lands before the drain starts to wait is kept.
    wake: Notify,
}

/// A queue in front of an actor, and the protocol that wakes whatever drains it.
pub struct Mailbox<T> {
    shared: Arc<Shared<T>>,
}

impl<T> Clone for Mailbox<T> {
    fn clone(&self) -> Self {
        Mailbox {
            shared: self.shared.clone(),
        }
    }
}

/// A slot in the mailbox, reserved for one message.
///
/// Dropping it unused gives the slot back.
#[must_use = "a permit holds a slot until it is used or dropped"]
pub struct Permit<T> {
    mailbox: Mailbox<T>,
    spent: bool,
}

impl<T> Permit<T> {
    /// `mb_enqueue`: put the message on the queue, in the slot this permit holds.
    pub fn enqueue(mut self, item: T) {
        let mut s = self.mailbox.state();
        s.reserved -= 1;
        s.queue.push_back(item);
        self.spent = true;
    }
}

impl<T> Drop for Permit<T> {
    fn drop(&mut self) {
        if !self.spent {
            let mut s = self.mailbox.state();
            s.reserved -= 1;
            // A slot is free. Wake every waiter, as `take` does, not one: a
            // registered waker can belong to a task that has since been
            // cancelled, and waking only that one would leave the live waiters
            // asleep on a free slot with nothing queued to wake them. The ones
            // that lose the race register again when they poll.
            let waiting = std::mem::take(&mut s.waiting);
            drop(s);
            for waker in waiting {
                waker.wake();
            }
        }
    }
}

impl<T> Mailbox<T> {
    /// Nothing queued, nothing flagged, the drain asleep: `mb_init`. It holds at
    /// most `capacity` messages.
    pub fn new(capacity: Capacity) -> Self {
        Mailbox {
            shared: Arc::new(Shared {
                state: Mutex::new(State {
                    queue: VecDeque::new(),
                    reserved: 0,
                    waiting: Vec::new(),
                    has: false,
                    processing: false,
                    scheduled: false,
                }),
                capacity,
                wake: Notify::new(),
            }),
        }
    }

    fn state(&self) -> std::sync::MutexGuard<'_, State<T>> {
        self.shared.state.lock().expect("mailbox lock")
    }

    /// How many messages are queued, not yet taken by the drain.
    pub fn queued(&self) -> u64 {
        self.state().queue.len() as u64
    }

    // --- a sender's steps -----------------------------------------------------

    /// Reserve a slot if there is one, and refuse if the mailbox is full.
    pub fn try_reserve(&self) -> Option<Permit<T>> {
        let mut s = self.state();
        self.reserve_locked(&mut s)
    }

    fn reserve_locked(&self, s: &mut State<T>) -> Option<Permit<T>> {
        if let Capacity::Bounded(room) = self.shared.capacity
            && (s.queue.len() as u64) + s.reserved >= u64::from(room.get())
        {
            return None;
        }
        s.reserved += 1;
        Some(Permit {
            mailbox: self.clone(),
            spent: false,
        })
    }

    /// Reserve a slot, or register `cx`'s task to be woken when one is free.
    pub fn poll_reserve(&self, cx: &mut task::Context<'_>) -> Poll<Permit<T>> {
        let mut s = self.state();
        if let Some(permit) = self.reserve_locked(&mut s) {
            return Poll::Ready(permit);
        }
        if !s.waiting.iter().any(|w| w.will_wake(cx.waker())) {
            s.waiting.push(cx.waker().clone());
        }
        Poll::Pending
    }

    /// Wait for a slot.
    pub async fn reserve(&self) -> Permit<T> {
        poll_fn(|cx| self.poll_reserve(cx)).await
    }

    /// `mb_set_state`: read `has` and set it. Returns what it was.
    pub fn set_state(&self) -> bool {
        std::mem::replace(&mut self.state().has, true)
    }

    /// `mb_schedule`: ask the drain to run — **if** `has` was clear when this
    /// sender set it, and the drain is not already running.
    ///
    /// A sender that found `has` already set leaves the wakeup to whoever set it;
    /// one that found the drain running leaves it to the drain's last step, which
    /// looks at `has` again.
    pub fn schedule(&self, had: bool) {
        let mut s = self.state();
        if !had && !s.processing {
            s.scheduled = true;
            self.shared.wake.notify_one();
        }
    }

    /// A sender's three steps, one after the other, once there is room.
    pub async fn send(&self, item: T) {
        self.reserve().await.enqueue(item);
        let had = self.set_state();
        self.schedule(had);
    }

    /// As [`send`](Self::send), but refused — with the message handed back —
    /// when the mailbox is full.
    pub fn try_send(&self, item: T) -> Result<(), T> {
        let Some(permit) = self.try_reserve() else {
            return Err(item);
        };
        permit.enqueue(item);
        let had = self.set_state();
        self.schedule(had);
        Ok(())
    }

    // --- the drain's steps ----------------------------------------------------

    /// `mb_claim`: once scheduled, mark the drain running and clear `has`, so a
    /// message that arrives from now on is noticed by [`finish`](Self::finish).
    /// Returns `false`, changing nothing, if the drain has not been asked to run.
    pub fn claim(&self) -> bool {
        let mut s = self.state();
        if !s.scheduled {
            return false;
        }
        s.processing = true;
        s.has = false;
        true
    }

    /// `mb_drain`: take everything in the queue, in order. The slots it held are
    /// free again, and the senders waiting for one are woken.
    pub fn take(&self) -> VecDeque<T> {
        let mut s = self.state();
        let taken = std::mem::take(&mut s.queue);
        let waiting = std::mem::take(&mut s.waiting);
        drop(s);
        for waker in waiting {
            waker.wake();
        }
        taken
    }

    /// `mb_finish`: stay scheduled exactly when `has` was set while the drain
    /// ran, and otherwise go back to sleep. Returns whether it stays scheduled.
    pub fn finish(&self) -> bool {
        let mut s = self.state();
        s.scheduled = s.has;
        s.processing = false;
        s.scheduled
    }

    /// Wait until the drain is asked to run, then claim it and take the queue:
    /// one round. The messages come out of the [`Round`] in the order they were
    /// queued, and dropping it is `finish`.
    ///
    /// Messages arriving while a round runs are not lost: `finish` sees them
    /// through `has`, and the next round finds the drain still scheduled.
    pub async fn round(&self) -> Round<T> {
        while !self.claim() {
            self.shared.wake.notified().await;
        }
        Round {
            items: self.take(),
            mailbox: self.clone(),
        }
    }
}

/// One round of the drain: the messages it took, oldest first.
///
/// The drain is *running* for as long as this is held — senders that arrive
/// meanwhile leave their wakeup to its last step — so it ends the round when it
/// is dropped, including when the handler panics or the task is cancelled.
pub struct Round<T> {
    items: VecDeque<T>,
    mailbox: Mailbox<T>,
}

impl<T> Iterator for Round<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.items.pop_front()
    }
}

impl<T> Drop for Round<T> {
    fn drop(&mut self) {
        self.mailbox.finish();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn cap(n: u32) -> Capacity {
        Capacity::Bounded(NonZeroU32::new(n).expect("a capacity"))
    }

    /// Rounds run until `want` messages have been handled.
    async fn drain_until(mb: Mailbox<(u8, u32)>, want: u32) -> Vec<(u8, u32)> {
        let mut out = Vec::new();
        while (out.len() as u64) < u64::from(want) {
            out.extend(mb.round().await);
        }
        out
    }

    /// Many senders, each sending in order, from several threads, into a mailbox
    /// far smaller than the traffic: nothing is lost or repeated, and each
    /// sender's messages come out in the order it sent them. If a wakeup were
    /// lost, `drain_until` would never return; if a slot were, a sender would
    /// wait for ever.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn nothing_is_lost_and_each_senders_order_holds() {
        const SENDERS: u8 = 8;
        const EACH: u32 = 500;
        let mb = Mailbox::new(cap(16));
        let drain = tokio::spawn(drain_until(mb.clone(), u32::from(SENDERS) * EACH));
        for sender in 0..SENDERS {
            let mb = mb.clone();
            tokio::spawn(async move {
                for seq in 0..EACH {
                    mb.send((sender, seq)).await;
                    if seq % 7 == 0 {
                        tokio::task::yield_now().await;
                    }
                }
            });
        }
        let got = tokio::time::timeout(std::time::Duration::from_secs(20), drain)
            .await
            .expect("every enqueued message was processed")
            .unwrap();

        assert_eq!(got.len() as u64, u64::from(SENDERS) * u64::from(EACH));
        let mut next: HashMap<u8, u32> = HashMap::new();
        for (sender, seq) in got {
            let n = next.entry(sender).or_default();
            assert_eq!(seq, *n, "sender {sender}: in order, none skipped or repeated");
            *n += 1;
        }
    }

    /// The drain is asleep until a sender wakes it, and a sender that finds it
    /// already woken does not wake it again.
    #[test]
    fn only_the_first_sender_schedules() {
        let mb = Mailbox::new(cap(8));
        assert!(!mb.claim(), "nothing scheduled, so the drain stays asleep");

        mb.try_reserve().unwrap().enqueue(1);
        let first = mb.set_state();
        mb.try_reserve().unwrap().enqueue(2);
        let second = mb.set_state();
        assert!(!first && second);
        mb.schedule(first);
        mb.schedule(second);

        assert!(mb.claim());
        assert_eq!(mb.take(), [1, 2]);
        assert!(!mb.finish(), "nothing arrived meanwhile: back to sleep");
        assert!(!mb.claim());
    }

    /// A message that arrives while the drain runs is not left asleep: `finish`
    /// stays scheduled, though the sender, finding the drain running, did not
    /// schedule it.
    #[test]
    fn a_message_during_the_drain_keeps_it_scheduled() {
        let mb = Mailbox::new(cap(8));
        mb.try_send(1).unwrap();
        assert!(mb.claim());
        assert_eq!(mb.take(), [1]);

        mb.try_send(2).unwrap(); // the drain is running: this sender does not schedule
        assert!(mb.finish(), "has was set meanwhile: stay scheduled");
        assert!(mb.claim());
        assert_eq!(mb.take(), [2]);
        assert!(!mb.finish());
    }

    /// A full mailbox refuses, handing the message back, and has room again once
    /// the drain has taken the queue.
    #[test]
    fn a_full_mailbox_refuses_until_it_is_drained() {
        let mb = Mailbox::new(cap(2));
        mb.try_send(1).unwrap();
        mb.try_send(2).unwrap();
        assert_eq!(mb.try_send(3), Err(3));
        assert_eq!(mb.queued(), 2);

        assert!(mb.claim());
        assert_eq!(mb.take(), [1, 2]);
        mb.try_send(3).unwrap();
        assert_eq!(mb.queued(), 1);
    }

    /// An unbounded mailbox never refuses and never makes a sender wait.
    #[test]
    fn an_unbounded_mailbox_never_refuses() {
        let mb = Mailbox::new(Capacity::Unbounded);
        for n in 0..10_000u32 {
            mb.try_send(n).unwrap();
        }
        assert_eq!(mb.queued(), 10_000);
        assert!(mb.try_reserve().is_some());
    }

    /// A reserved slot counts against the capacity before anything is enqueued,
    /// and dropping the permit gives it back.
    #[test]
    fn a_permit_holds_its_slot_until_used_or_dropped() {
        let mb = Mailbox::<u8>::new(cap(1));
        let permit = mb.try_reserve().unwrap();
        assert!(mb.try_reserve().is_none(), "the slot is spoken for");
        drop(permit);
        assert!(mb.try_reserve().is_some(), "an unused permit frees its slot");
    }

    /// A sender waiting for room is woken when the drain makes some, and goes on
    /// to deliver.
    #[tokio::test]
    async fn a_waiting_sender_is_woken_by_the_drain() {
        let mb = Mailbox::new(cap(1));
        mb.try_send(1).unwrap();

        let sender = {
            let mb = mb.clone();
            tokio::spawn(async move { mb.send(2).await })
        };
        tokio::task::yield_now().await;
        assert!(!sender.is_finished(), "no room: the sender waits");

        let first: Vec<_> = mb.round().await.collect();
        assert_eq!(first, [1]);
        tokio::time::timeout(std::time::Duration::from_secs(5), sender)
            .await
            .expect("the drain made room, so the sender was woken")
            .unwrap();

        let second: Vec<_> = mb.round().await.collect();
        assert_eq!(second, [2]);
    }

    /// A waiter that is cancelled does not take with it the wakeup meant for the
    /// ones still waiting. Nothing is queued here, so no drain will wake them: the
    /// permit being dropped is the only thing that can.
    #[tokio::test]
    async fn a_cancelled_waiter_does_not_swallow_the_wakeup() {
        use std::time::Duration;
        let mb = Mailbox::<u8>::new(cap(1));
        let permit = mb.try_reserve().unwrap();

        let first = {
            let mb = mb.clone();
            tokio::spawn(async move { mb.reserve().await })
        };
        tokio::time::sleep(Duration::from_millis(50)).await;
        let second = {
            let mb = mb.clone();
            tokio::spawn(async move { mb.reserve().await })
        };
        tokio::time::sleep(Duration::from_millis(50)).await;

        // The later waiter goes away; its waker is still registered.
        second.abort();
        drop(permit);

        let got = tokio::time::timeout(Duration::from_secs(5), first)
            .await
            .expect("the waiter that is still there was woken")
            .unwrap();
        got.enqueue(1);
        assert_eq!(mb.queued(), 1);
    }
}
