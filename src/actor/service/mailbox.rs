//! The mailbox, executable: [`crate::actor::mailbox::model`] with its steps run
//! on real threads.
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
//! | `mb_enqueue` | [`Mailbox::enqueue`] | a sender |
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
//! # What is not claimed
//!
//! This is a transcription, not a refinement: nothing here is checked against
//! the model by Verus, and the claim that it behaves like the model rests on each
//! method being the model step it is named for, and on the tests below. It is the
//! same line [`crate::actor::mailbox`] draws: the protocol is proved, connecting
//! it to running code is this file.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use tokio::sync::Notify;

struct State<T> {
    /// Messages waiting to be drained, oldest first.
    queue: VecDeque<T>,
    /// Messages have been enqueued since the drain last looked.
    has: bool,
    /// The drain is running.
    processing: bool,
    /// The drain has been asked to run.
    scheduled: bool,
}

struct Shared<T> {
    state: Mutex<State<T>>,
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

impl<T> Default for Mailbox<T> {
    fn default() -> Self {
        Mailbox::new()
    }
}

impl<T> Mailbox<T> {
    /// Nothing queued, nothing flagged, the drain asleep: `mb_init`.
    pub fn new() -> Self {
        Mailbox {
            shared: Arc::new(Shared {
                state: Mutex::new(State {
                    queue: VecDeque::new(),
                    has: false,
                    processing: false,
                    scheduled: false,
                }),
                wake: Notify::new(),
            }),
        }
    }

    fn state(&self) -> std::sync::MutexGuard<'_, State<T>> {
        self.shared.state.lock().expect("mailbox lock")
    }

    // --- a sender's steps -----------------------------------------------------

    /// `mb_enqueue`: put the message on the queue.
    pub fn enqueue(&self, item: T) {
        self.state().queue.push_back(item);
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

    /// A sender's three steps, one after the other.
    pub fn send(&self, item: T) {
        self.enqueue(item);
        let had = self.set_state();
        self.schedule(had);
    }

    // --- the drain's steps ----------------------------------------------------

    /// `mb_claim`: once scheduled, mark the drain running and clear `has`, so a
    /// message that arrives from now on is noticed by [`finish`](Self::finish).
    /// Returns `false`, changing nothing, if the drain has not been asked to run,
    /// **or is already running**: the model's `mb_claim` fires only with the drain
    /// at the top of its loop, and `processing` is that, negated. `scheduled`
    /// stays true throughout a round that is to be followed by another, so
    /// without this a second drain on a clone of the mailbox could claim it and
    /// run concurrently with the first.
    pub fn claim(&self) -> bool {
        let mut s = self.state();
        if !s.scheduled || s.processing {
            return false;
        }
        s.processing = true;
        s.has = false;
        true
    }

    /// `mb_drain`: take everything in the queue, in order.
    pub fn take(&self) -> VecDeque<T> {
        std::mem::take(&mut self.state().queue)
    }

    /// `mb_finish`: stay scheduled exactly when `has` was set while the drain
    /// ran, and otherwise go back to sleep. Returns whether it stays scheduled.
    pub fn finish(&self) -> bool {
        let mut s = self.state();
        s.scheduled = s.has;
        s.processing = false;
        if s.scheduled {
            // A drain that was refused its claim while this round ran is waiting
            // for exactly this.
            self.shared.wake.notify_one();
        }
        s.scheduled
    }

    /// Put back, ahead of anything that arrived since, the messages a round was
    /// dropped before handing out, and note that there are some.
    ///
    /// **Not a model step.** The model's drain takes the whole queue and the
    /// messages are processed; a running drain can also panic, or be cancelled,
    /// between taking them and handling them, and then they must not vanish with
    /// the round — their senders are waiting on an answer. Setting `has` makes
    /// the `finish` that follows stay scheduled, so the next round finds them.
    fn requeue(&self, rest: VecDeque<T>) {
        if rest.is_empty() {
            return;
        }
        let mut s = self.state();
        for item in rest.into_iter().rev() {
            s.queue.push_front(item);
        }
        s.has = true;
    }

    /// Wait until the drain is asked to run, then claim it and take the queue:
    /// one round. The messages come out of the [`Round`] in the order they were
    /// queued, and dropping it is `finish` — after putting back any it had not
    /// handed out.
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
        // Whatever was not handed out goes back to the front of the queue.
        self.mailbox.requeue(std::mem::take(&mut self.items));
        self.mailbox.finish();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// Rounds run until `want` messages have been handled.
    async fn drain_until(mb: Mailbox<(u8, u32)>, want: usize) -> Vec<(u8, u32)> {
        let mut out = Vec::new();
        while out.len() < want {
            out.extend(mb.round().await);
        }
        out
    }

    /// Many senders, each sending in order, from several threads: nothing is lost
    /// or repeated, and each sender's messages come out in the order it sent
    /// them. If a wakeup were lost, `drain_until` would never return.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn nothing_is_lost_and_each_senders_order_holds() {
        const SENDERS: u8 = 8;
        const EACH: u32 = 500;
        let mb = Mailbox::new();
        let drain = tokio::spawn(drain_until(mb.clone(), SENDERS as usize * EACH as usize));
        for sender in 0..SENDERS {
            let mb = mb.clone();
            tokio::spawn(async move {
                for seq in 0..EACH {
                    mb.send((sender, seq));
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

        assert_eq!(got.len(), SENDERS as usize * EACH as usize);
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
        let mb = Mailbox::new();
        assert!(!mb.claim(), "nothing scheduled, so the drain stays asleep");

        mb.enqueue(1);
        let first = mb.set_state();
        mb.enqueue(2);
        let second = mb.set_state();
        assert!(!first && second);
        mb.schedule(first);
        mb.schedule(second);

        assert!(mb.claim());
        assert_eq!(mb.take(), [1, 2]);
        assert!(!mb.finish(), "nothing arrived meanwhile: back to sleep");
        assert!(!mb.claim());
    }

    /// Two drains on clones of one mailbox are never both running: a claim made
    /// while a round is in progress is refused, even though `scheduled` is true.
    #[test]
    fn a_second_drain_cannot_claim_while_a_round_runs() {
        let mb = Mailbox::new();
        mb.send(1);
        assert!(mb.claim());
        assert!(!mb.claim(), "a round is running");
        assert_eq!(mb.take(), [1]);
        assert!(!mb.claim(), "still running until it finishes");
        assert!(!mb.finish());
        assert!(!mb.claim(), "and nothing is scheduled after it");
    }

    /// A round dropped before it handed everything out — a handler panicked, or
    /// the task was cancelled — keeps the rest, ahead of what arrived meanwhile.
    #[tokio::test]
    async fn dropping_a_round_early_keeps_what_it_did_not_hand_out() {
        let mb = Mailbox::new();
        mb.send(1);
        mb.send(2);
        mb.send(3);
        let mut round = mb.round().await;
        assert_eq!(round.next(), Some(1));
        mb.send(4); // arrives during the round
        drop(round); // 2 and 3 were never handled

        let again: Vec<_> = mb.round().await.collect();
        assert_eq!(again, [2, 3, 4], "in their original order, none lost");
    }

    /// A message that arrives while the drain runs is not left asleep: `finish`
    /// stays scheduled, though the sender, finding the drain running, did not
    /// schedule it.
    #[test]
    fn a_message_during_the_drain_keeps_it_scheduled() {
        let mb = Mailbox::new();
        mb.send(1);
        assert!(mb.claim());
        assert_eq!(mb.take(), [1]);

        mb.send(2); // the drain is running: this sender does not schedule
        assert!(mb.finish(), "has was set meanwhile: stay scheduled");
        assert!(mb.claim());
        assert_eq!(mb.take(), [2]);
        assert!(!mb.finish());
    }
}
