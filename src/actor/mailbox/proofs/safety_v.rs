//! The mailbox delivers each message once, in order, and without gaps.
//!
//! These are statements about every state of every run, and every one is a
//! corollary of [`crate::actor::mailbox::proofs::invariant::mb_inv`]: the
//! numbering invariant says what a message's number is, and everything here is
//! what that number then forces.
//!
//! The last of them is the one that connects this module to the actor:
//! [`theorem_the_drain_never_presents_a_message_ahead_of_its_turn`] says the
//! order the drain processes messages in satisfies, at every step, the guard of
//! [`crate::actor::model::as_accept`] — a message's number is exactly the count
//! already processed from its sender. A host that takes its messages from this
//! mailbox is never *refused* for being early.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::mailbox::model::*;
use crate::actor::mailbox::proofs::invariant::*;
use crate::actor::model::Envelope;
use crate::id::Id;

verus! {

/// `b` begins with all of `a`: nothing in `a` moved, changed or vanished.
pub open spec fn prefix_of(a: Seq<Envelope>, b: Seq<Envelope>) -> bool {
    a.len() <= b.len() && b.take(a.len() as int) =~= a
}

pub proof fn lemma_prefix_trans(a: Seq<Envelope>, b: Seq<Envelope>, c: Seq<Envelope>)
    requires
        prefix_of(a, b),
        prefix_of(b, c),
    ensures
        prefix_of(a, c),
{
    assert(c.take(a.len() as int) =~= a) by {
        assert(c.take(b.len() as int).take(a.len() as int) =~= c.take(a.len() as int));
        assert(c.take(b.len() as int) =~= b);
        assert(b.take(a.len() as int) =~= a);
    }
}

pub proof fn lemma_prefix_refl(a: Seq<Envelope>)
    ensures
        prefix_of(a, a),
{
    assert(a.take(a.len() as int) =~= a);
}

pub proof fn lemma_push_extends(a: Seq<Envelope>, e: Envelope)
    ensures
        prefix_of(a, a.push(e)),
{
    assert(a.push(e).take(a.len() as int) =~= a);
}

pub proof fn lemma_append_extends(a: Seq<Envelope>, b: Seq<Envelope>)
    ensures
        prefix_of(a, a + b),
{
    assert((a + b).take(a.len() as int) =~= a);
}

/// A step only ever adds to the end of what the mailbox has taken in, and of
/// what it has processed.
pub proof fn lemma_step_extends(step: MbStep, pre: Mailbox, post: Mailbox)
    requires
        mb_step(step, pre, post),
    ensures
        prefix_of(all_of(pre), all_of(post)),
        prefix_of(pre.processed, post.processed),
{
    lemma_prefix_refl(all_of(pre));
    lemma_prefix_refl(pre.processed);
    match step {
        MbStep::Enqueue { sender, body } => {
            let env = Envelope { sender, seq: mb_seq(pre, sender) as u64, body };
            assert(all_of(post) =~= all_of(pre).push(env));
            lemma_push_extends(all_of(pre), env);
        },
        MbStep::Drain => {
            assert(all_of(post) =~= all_of(pre));
            lemma_append_extends(pre.processed, pre.queue);
        },
        MbStep::SetState { env } => {},
        MbStep::Schedule { env } => {},
        MbStep::Claim => {},
        MbStep::Finish => {},
        MbStep::Stutter => {},
    }
}

/// **Messages are only added at the end, and the processed ones never change.**
///
/// For `i <= j`, what the mailbox had taken in at `i` is the beginning of what
/// it has taken in at `j`, and the same of what it had processed.
pub proof fn theorem_nothing_is_lost_or_reordered(
    ex: spec_fn(nat) -> Mailbox,
    i: nat,
    j: nat,
)
    requires
        mb_run(ex),
        i <= j,
    ensures
        prefix_of(all_of(ex(i)), all_of(ex(j))),
        prefix_of(ex(i).processed, ex(j).processed),
    decreases j - i,
{
    if i == j {
        lemma_prefix_refl(all_of(ex(i)));
        lemma_prefix_refl(ex(i).processed);
    } else {
        theorem_nothing_is_lost_or_reordered(ex, i, (j - 1) as nat);
        let k = (j - 1) as nat;
        assert(mb_next(ex(k), ex(k + 1)));
        let pre = ex(k);
        let post = ex(k + 1);
        let step = choose|step: MbStep| #[trigger] mb_step(step, pre, post);
        lemma_step_extends(step, pre, post);
        lemma_prefix_trans(all_of(ex(i)), all_of(pre), all_of(post));
        lemma_prefix_trans(ex(i).processed, pre.processed, post.processed);
    }
}

/// A later message from the same sender is numbered strictly higher.
pub proof fn lemma_later_is_higher(m: Mailbox, i: int, j: int)
    requires
        inv_numbered(m),
        0 <= i < j < all_of(m).len(),
        all_of(m)[i].sender == all_of(m)[j].sender,
    ensures
        all_of(m)[i].seq < all_of(m)[j].seq,
{
    let a = all_of(m);
    let next = a.take(i + 1);
    assert(next.drop_last() =~= a.take(i));
    assert(next.last() == a[i]);
    assert(a[i].seq == count_from(a.take(i), a[i].sender));
    lemma_count_between(a, i + 1, j, a[i].sender);
}

/// The count over a longer prefix is no smaller.
proof fn lemma_count_between(a: Seq<Envelope>, p: int, q: int, x: Id)
    requires
        0 <= p <= q <= a.len(),
    ensures
        count_from(a.take(p), x) <= count_from(a.take(q), x),
    decreases q - p,
{
    if p < q {
        let next = a.take(p + 1);
        assert(next.drop_last() =~= a.take(p));
        assert(next.last() == a[p]);
        assert(a.take(q).take(p + 1) =~= a.take(p + 1));
        lemma_count_between(a, p + 1, q, x);
    }
}

/// **Each message is taken in once.** No message appears twice among those the
/// mailbox holds, queued or processed.
pub proof fn theorem_a_message_is_taken_in_once(m: Mailbox, i: int, j: int)
    requires
        mb_inv(m),
        0 <= i < j < all_of(m).len(),
    ensures
        all_of(m)[i] != all_of(m)[j],
{
    if all_of(m)[i].sender == all_of(m)[j].sender {
        lemma_later_is_higher(m, i, j);
    }
}

/// **One sender's messages come out in the order it sent them.**
pub proof fn theorem_one_senders_messages_keep_their_order(m: Mailbox, i: int, j: int)
    requires
        mb_inv(m),
        0 <= i < j < all_of(m).len(),
        all_of(m)[i].sender == all_of(m)[j].sender,
    ensures
        all_of(m)[i].seq < all_of(m)[j].seq,
{
    lemma_later_is_higher(m, i, j);
}

/// **Nothing is skipped.** A message's number is the count of messages from its
/// sender that precede it — so there is no message numbered `n` without ones
/// numbered `0..n` before it.
pub proof fn theorem_a_senders_messages_are_numbered_without_gaps(m: Mailbox, i: int)
    requires
        mb_inv(m),
        0 <= i < all_of(m).len(),
    ensures
        all_of(m)[i].seq == count_from(all_of(m).take(i), all_of(m)[i].sender),
{
}

/// **The drain never presents a message ahead of its turn.**
///
/// The `i`th message the drain processed is numbered the count of messages from
/// its sender among the `i` before it — which is, word for word, the guard of
/// the actor's accept ([`crate::actor::model::as_accept`]: `env.seq ==
/// accepted_from(journal, env.sender)`). A host accepting in this order is never
/// refused for being early, and is never offered a message it already accepted.
pub proof fn theorem_the_drain_never_presents_a_message_ahead_of_its_turn(m: Mailbox, i: int)
    requires
        mb_inv(m),
        0 <= i < m.processed.len(),
    ensures
        m.processed[i].seq == count_from(m.processed.take(i), m.processed[i].sender),
{
    let a = all_of(m);
    assert(a[i] == m.processed[i]);
    assert(a.take(i) =~= m.processed.take(i));
}

/// **The processed messages are the beginning of what the mailbox holds**: the
/// drain only ever takes the front of the queue.
pub proof fn theorem_the_drain_takes_the_front_of_the_queue(m: Mailbox)
    ensures
        prefix_of(m.processed, all_of(m)),
{
    lemma_append_extends(m.processed, m.queue);
}

} // verus!
