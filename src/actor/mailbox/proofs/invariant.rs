//! What the mailbox protocol keeps true.
//!
//! Six clauses, each preserved by every step, none provable alone:
//!
//! * [`inv_processing`] — the `processing` flag says whether the drain is running;
//! * [`inv_numbered`] — every message, queued or processed, carries the number
//!   that is the count of messages from its sender before it;
//! * [`inv_next_seq`] — each sender's next number is the count of its messages;
//! * [`inv_ops_known`] — a sender mid-operation is mid-operation on a message the
//!   mailbox has taken in;
//! * [`inv_wakeup_flag`] — **a set `has` with no wakeup pending is accounted for:**
//!   some sender has set it and not yet had its turn to schedule;
//! * [`inv_wakeup_queue`] — **a queued message with `has` clear is accounted for:**
//!   some sender has enqueued it and not yet had its turn to set `has`.
//!
//! The last two are the protocol. Together they say a message on the queue is
//! never *unaccounted for* — never sitting there with nobody who is going to
//! wake the drain for it — and [`crate::actor::mailbox::proofs::liveness`] turns
//! that into delivery.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::mailbox::model::*;
use crate::actor::model::Envelope;
use crate::ownership::model::NodeId;
use crate::temporal::*;

verus! {

/// How many of `s` were sent by `sender`.
pub open spec fn count_from(s: Seq<Envelope>, sender: NodeId) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_from(s.drop_last(), sender) + if s.last().sender == sender {
            1nat
        } else {
            0nat
        }
    }
}

/// Everything the mailbox has taken in, in order: what the drain has processed,
/// then what it has yet to.
pub open spec fn all_of(m: Mailbox) -> Seq<Envelope> {
    m.processed + m.queue
}

pub open spec fn inv_processing(m: Mailbox) -> bool {
    m.processing == !(m.dq is Await)
}

pub open spec fn inv_numbered(m: Mailbox) -> bool {
    let a = all_of(m);
    forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].seq == count_from(a.take(i), a[i].sender)
}

pub open spec fn inv_next_seq(m: Mailbox) -> bool {
    forall|s: NodeId| #[trigger] mb_seq(m, s) == count_from(all_of(m), s)
}

pub open spec fn inv_ops_known(m: Mailbox) -> bool {
    forall|e: Envelope| #[trigger] m.ops.contains_key(e) ==> all_of(m).contains(e)
}

pub open spec fn inv_wakeup_flag(m: Mailbox) -> bool {
    m.dq is Await ==> (m.has && !m.scheduled ==> exists|e: Envelope|
        #[trigger] scheduling(m, e, false))
}

pub open spec fn inv_wakeup_queue(m: Mailbox) -> bool {
    !(m.dq is Claimed) ==> (m.queue.len() > 0 && !m.has ==> exists|e: Envelope|
        #[trigger] marked(m, e))
}

/// The invariant.
pub open spec fn mb_inv(m: Mailbox) -> bool {
    &&& inv_processing(m)
    &&& inv_numbered(m)
    &&& inv_next_seq(m)
    &&& inv_ops_known(m)
    &&& inv_wakeup_flag(m)
    &&& inv_wakeup_queue(m)
}

/// Pushing a message adds one to its sender's count and nothing to anyone
/// else's.
pub proof fn lemma_count_push(s: Seq<Envelope>, e: Envelope, x: NodeId)
    ensures
        count_from(s.push(e), x) == count_from(s, x) + if e.sender == x {
            1nat
        } else {
            0nat
        },
{
    assert(s.push(e).drop_last() =~= s);
}

/// A prefix has no more messages from a sender than the whole.
pub proof fn lemma_count_prefix(a: Seq<Envelope>, j: int, x: NodeId)
    requires
        0 <= j <= a.len(),
    ensures
        count_from(a.take(j), x) <= count_from(a, x),
    decreases a.len() - j,
{
    if j == a.len() {
        assert(a.take(j) =~= a);
    } else {
        let next = a.take(j + 1);
        assert(next.drop_last() =~= a.take(j));
        assert(next.last() == a[j]);
        lemma_count_prefix(a, j + 1, x);
    }
}

/// **A message about to be numbered `count` is not one the mailbox already
/// holds.** The numbering is what makes `(sender, seq)` a name.
pub proof fn lemma_fresh(m: Mailbox, env: Envelope)
    requires
        inv_numbered(m),
        inv_next_seq(m),
        env.seq == mb_seq(m, env.sender),
    ensures
        !all_of(m).contains(env),
{
    let a = all_of(m);
    if a.contains(env) {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == env;
        assert(a[i].seq == count_from(a.take(i), a[i].sender));
        let next = a.take(i + 1);
        assert(next.drop_last() =~= a.take(i));
        assert(next.last() == a[i]);
        lemma_count_prefix(a, i + 1, env.sender);
        assert(mb_seq(m, env.sender) == count_from(a, env.sender));
    }
}

/// A step that leaves the messages and the numbering alone keeps both clauses.
proof fn lemma_same_messages(pre: Mailbox, post: Mailbox)
    requires
        inv_numbered(pre),
        inv_next_seq(pre),
        inv_ops_known(pre),
        all_of(post) == all_of(pre),
        post.next_seq == pre.next_seq,
        post.ops.dom().subset_of(pre.ops.dom()),
    ensures
        inv_numbered(post),
        inv_next_seq(post),
        inv_ops_known(post),
{
    assert forall|s: NodeId| #[trigger] mb_seq(post, s) == count_from(all_of(post), s) by {
        assert(mb_seq(post, s) == mb_seq(pre, s));
    }
    assert forall|e: Envelope| #[trigger] post.ops.contains_key(e) implies all_of(post).contains(e) by {
        assert(pre.ops.contains_key(e));
    }
}

pub proof fn lemma_init_inv(m: Mailbox)
    requires
        mb_init(m),
    ensures
        mb_inv(m),
{
    assert(all_of(m) =~= Seq::<Envelope>::empty());
    assert forall|s: NodeId| #[trigger] mb_seq(m, s) == count_from(all_of(m), s) by {
        assert(!m.next_seq.contains_key(s));
        assert(count_from(Seq::<Envelope>::empty(), s) == 0);
    }
}

pub proof fn lemma_enqueue_preserves_inv(pre: Mailbox, post: Mailbox, sender: NodeId, body: nat)
    requires
        mb_inv(pre),
        mb_enqueue(pre, post, sender, body),
    ensures
        mb_inv(post),
{
    let env = Envelope { sender, seq: mb_seq(pre, sender), body };
    let a = all_of(pre);
    let b = all_of(post);
    assert(b =~= a.push(env));
    lemma_fresh(pre, env);
    assert(!pre.ops.contains_key(env));
    assert forall|i: int| 0 <= i < b.len() implies #[trigger] b[i].seq == count_from(
        b.take(i),
        b[i].sender,
    ) by {
        if i < a.len() {
            assert(b.take(i) =~= a.take(i));
            assert(b[i] == a[i]);
        } else {
            assert(i == a.len());
            assert(b[i] == env);
            assert(b.take(i) =~= a);
        }
    }
    assert forall|s: NodeId| #[trigger] mb_seq(post, s) == count_from(b, s) by {
        lemma_count_push(a, env, s);
        assert(mb_seq(pre, s) == count_from(a, s));
        if s == sender {
            assert(post.next_seq[s] == env.seq + 1);
        } else {
            assert(post.next_seq.contains_key(s) == pre.next_seq.contains_key(s));
        }
    }
    assert forall|e: Envelope| #[trigger] post.ops.contains_key(e) implies b.contains(e) by {
        if e != env {
            assert(pre.ops.contains_key(e));
            assert(a.contains(e));
            let i = choose|i: int| 0 <= i < a.len() && a[i] == e;
            assert(b[i] == e);
        } else {
            assert(b[b.len() - 1] == env);
        }
    }
    assert(marked(post, env));
    if post.dq is Await && post.has && !post.scheduled {
        let e = choose|e: Envelope| scheduling(pre, e, false);
        assert(e != env);
        assert(scheduling(post, e, false));
    }
}

pub proof fn lemma_set_state_preserves_inv(pre: Mailbox, post: Mailbox, env: Envelope)
    requires
        mb_inv(pre),
        mb_set_state(pre, post, env),
    ensures
        mb_inv(post),
{
    assert(all_of(post) =~= all_of(pre));
    assert(post.ops.dom() =~= pre.ops.dom());
    lemma_same_messages(pre, post);
    if post.dq is Await && post.has && !post.scheduled {
        if pre.has {
            let e = choose|e: Envelope| scheduling(pre, e, false);
            assert(e != env);
            assert(scheduling(post, e, false));
        } else {
            assert(scheduling(post, env, false));
        }
    }
}

pub proof fn lemma_schedule_preserves_inv(pre: Mailbox, post: Mailbox, env: Envelope)
    requires
        mb_inv(pre),
        mb_schedule(pre, post, env),
    ensures
        mb_inv(post),
{
    assert(all_of(post) =~= all_of(pre));
    assert(post.ops.dom().subset_of(pre.ops.dom()));
    lemma_same_messages(pre, post);
    if post.dq is Await && post.has && !post.scheduled {
        assert(stage_had(pre.ops[env]));
        let e = choose|e: Envelope| scheduling(pre, e, false);
        assert(e != env);
        assert(scheduling(post, e, false));
    }
    if !(post.dq is Claimed) && post.queue.len() > 0 && !post.has {
        let e = choose|e: Envelope| marked(pre, e);
        assert(e != env);
        assert(marked(post, e));
    }
}

pub proof fn lemma_claim_preserves_inv(pre: Mailbox, post: Mailbox)
    requires
        mb_inv(pre),
        mb_claim(pre, post),
    ensures
        mb_inv(post),
{
    assert(all_of(post) =~= all_of(pre));
    assert(post.ops.dom().subset_of(pre.ops.dom()));
    lemma_same_messages(pre, post);
}

pub proof fn lemma_drain_preserves_inv(pre: Mailbox, post: Mailbox)
    requires
        mb_inv(pre),
        mb_drain(pre, post),
    ensures
        mb_inv(post),
{
    assert(all_of(post) =~= all_of(pre));
    assert(post.ops.dom().subset_of(pre.ops.dom()));
    lemma_same_messages(pre, post);
}

pub proof fn lemma_finish_preserves_inv(pre: Mailbox, post: Mailbox)
    requires
        mb_inv(pre),
        mb_finish(pre, post),
    ensures
        mb_inv(post),
{
    assert(all_of(post) =~= all_of(pre));
    assert(post.ops.dom().subset_of(pre.ops.dom()));
    lemma_same_messages(pre, post);
    assert(post.ops == pre.ops);
    if post.queue.len() > 0 && !post.has {
        let e = choose|e: Envelope| marked(pre, e);
        assert(marked(post, e));
    }
}

pub proof fn lemma_step_preserves_inv(step: MbStep, pre: Mailbox, post: Mailbox)
    requires
        mb_inv(pre),
        mb_step(step, pre, post),
    ensures
        mb_inv(post),
{
    match step {
        MbStep::Enqueue { sender, body } => lemma_enqueue_preserves_inv(pre, post, sender, body),
        MbStep::SetState { env } => lemma_set_state_preserves_inv(pre, post, env),
        MbStep::Schedule { env } => lemma_schedule_preserves_inv(pre, post, env),
        MbStep::Claim => lemma_claim_preserves_inv(pre, post),
        MbStep::Drain => lemma_drain_preserves_inv(pre, post),
        MbStep::Finish => lemma_finish_preserves_inv(pre, post),
        MbStep::Stutter => {},
    }
}

/// A run of the mailbox: the machine, as an infinite execution.
pub open spec fn mb_run(ex: spec_fn(nat) -> Mailbox) -> bool {
    &&& mb_init(ex(0))
    &&& forall|i: nat| #[trigger] mb_next(ex(i), ex(i + 1))
}

/// A run of the mailbox is a run in the sense of [`crate::temporal`].
pub proof fn lemma_mb_run_runs(ex: spec_fn(nat) -> Mailbox)
    requires
        mb_run(ex),
    ensures
        runs(ex, |s: Mailbox| mb_init(s), |s: Mailbox, t: Mailbox| mb_next(s, t)),
{
    let next = |s: Mailbox, t: Mailbox| mb_next(s, t);
    assert forall|i: nat| #[trigger] next(ex(i), ex(i + 1)) by {
        assert(mb_next(ex(i), ex(i + 1)));
    }
}

/// **The invariant holds at every step of every run.**
pub proof fn theorem_run_inv(ex: spec_fn(nat) -> Mailbox, n: nat)
    requires
        mb_run(ex),
    ensures
        mb_inv(ex(n)),
    decreases n,
{
    if n == 0 {
        lemma_init_inv(ex(0));
    } else {
        theorem_run_inv(ex, (n - 1) as nat);
        let k = (n - 1) as nat;
        assert(mb_next(ex(k), ex(k + 1)));
        let pre = ex(k);
        let post = ex(k + 1);
        let step = choose|step: MbStep| #[trigger] mb_step(step, pre, post);
        lemma_step_preserves_inv(step, pre, post);
    }
}

} // verus!
