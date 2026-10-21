//! **A message enqueued is a message processed.**
//!
//! The claim is [`theorem_every_enqueued_message_is_processed`]: in every run of
//! the mailbox in which the steps of [`mailbox_fair`] are not starved, a message
//! on the queue is later in `processed`. It is the property the protocol
//! exists for. Its failure mode is the *lost wakeup*: a message sits on the
//! queue, the drain is asleep, and nobody is going to wake it.
//!
//! # The assumption, and only that
//!
//! [`mailbox_fair`] is weak fairness of six kinds of step: the drain's three
//! (`claim`, `drain`, `finish`), and, for every message, its sender's two
//! remaining ones (`set_state`, `schedule`). Each says: **if the step stays
//! possible, it is eventually taken.** Nothing is assumed about senders sending,
//! nothing about the network, and nothing about how long anything takes. In
//! particular `enqueue` is not fair: a sender that never sends is allowed.
//!
//! A sender that has enqueued, however, *is* owed its turn — if it were not, the
//! message could sit on the queue behind a flag nobody is ever going to set, and
//! the theorem would be false. The proof is how that need is discovered rather
//! than assumed: each stage below is one application of
//! [`crate::temporal::lemma_wf1`], and the assumption is used exactly where a
//! stage cannot move without it.
//!
//! # The shape of the proof
//!
//! Where the drain is decides the next stage.
//!
//! * `Claimed` — [`stage_drain`]: the fair `drain` step takes the queue.
//! * `Drained` — [`stage_finish`]: the fair `finish` step puts it back to
//!   `Await`, and the message is still queued.
//! * `Await` and scheduled — [`stage_claim`]: the fair `claim` step.
//! * `Await` and **not** scheduled — the lost-wakeup case, and the reason for
//!   the invariant. [`crate::actor::mailbox::proofs::invariant::inv_wakeup_flag`]
//!   and `inv_wakeup_queue` say some sender is mid-operation: either one has set
//!   `has` and not scheduled ([`stage_schedule`] — its fair `schedule` step
//!   schedules, since the drain is asleep), or one has enqueued and not set `has`
//!   ([`stage_set_state`] — its fair `set_state` step becomes the first case).
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::mailbox::model::*;
use crate::actor::mailbox::proofs::invariant::*;
use crate::actor::model::Envelope;
use crate::id::Id;
use crate::temporal::*;

verus! {

// -- The fairness assumption ----------------------------------------------------

pub open spec fn en_claim() -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| s.dq is Await && s.scheduled
}

pub open spec fn tk_claim() -> spec_fn(Mailbox, Mailbox) -> bool {
    |s: Mailbox, t: Mailbox| mb_claim(s, t)
}

pub open spec fn en_drain() -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| s.dq is Claimed
}

pub open spec fn tk_drain() -> spec_fn(Mailbox, Mailbox) -> bool {
    |s: Mailbox, t: Mailbox| mb_drain(s, t)
}

pub open spec fn en_finish() -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| s.dq is Drained
}

pub open spec fn tk_finish() -> spec_fn(Mailbox, Mailbox) -> bool {
    |s: Mailbox, t: Mailbox| mb_finish(s, t)
}

pub open spec fn en_set_state(env: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| marked(s, env)
}

pub open spec fn tk_set_state(env: Envelope) -> spec_fn(Mailbox, Mailbox) -> bool {
    |s: Mailbox, t: Mailbox| mb_set_state(s, t, env)
}

pub open spec fn en_schedule(env: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| is_scheduling(s, env)
}

pub open spec fn tk_schedule(env: Envelope) -> spec_fn(Mailbox, Mailbox) -> bool {
    |s: Mailbox, t: Mailbox| mb_schedule(s, t, env)
}

pub open spec fn fair_set_state(ex: spec_fn(nat) -> Mailbox, env: Envelope) -> bool {
    weakly_fair(ex, en_set_state(env), tk_set_state(env))
}

pub open spec fn fair_schedule(ex: spec_fn(nat) -> Mailbox, env: Envelope) -> bool {
    weakly_fair(ex, en_schedule(env), tk_schedule(env))
}

/// **The fairness the liveness theorem assumes.** The drain's three steps, and
/// each sender's two, are not starved. Enqueueing is not on the list.
pub open spec fn mailbox_fair(ex: spec_fn(nat) -> Mailbox) -> bool {
    &&& weakly_fair(ex, en_claim(), tk_claim())
    &&& weakly_fair(ex, en_drain(), tk_drain())
    &&& weakly_fair(ex, en_finish(), tk_finish())
    &&& forall|env: Envelope| #[trigger] fair_set_state(ex, env)
    &&& forall|env: Envelope| #[trigger] fair_schedule(ex, env)
}

// -- The stages -----------------------------------------------------------------

/// The message is queued.
pub open spec fn queued(s: Mailbox, m: Envelope) -> bool {
    s.queue.contains(m)
}

/// The message has been processed.
pub open spec fn done(s: Mailbox, m: Envelope) -> bool {
    s.processed.contains(m)
}

/// Queued, and the drain has claimed the queue but not taken it.
pub open spec fn claimed(s: Mailbox, m: Envelope) -> bool {
    s.dq is Claimed && s.queue.contains(m)
}

/// Queued, and the drain is awake to be woken: scheduled and waiting.
pub open spec fn ready(s: Mailbox, m: Envelope) -> bool {
    s.dq is Await && s.scheduled && s.queue.contains(m)
}

/// Queued, and the drain has taken the queue and not yet decided to sleep.
pub open spec fn drained(s: Mailbox, m: Envelope) -> bool {
    s.dq is Drained && s.queue.contains(m)
}

/// Queued, and the drain is at the top of its loop.
pub open spec fn awaiting(s: Mailbox, m: Envelope) -> bool {
    s.dq is Await && s.queue.contains(m)
}

/// Queued, and the drain is at the top of its loop **with no wakeup pending**:
/// the case the whole protocol is about.
pub open spec fn idle(s: Mailbox, m: Envelope) -> bool {
    s.dq is Await && !s.scheduled && s.queue.contains(m)
}

/// Idle, and `e` has set `has` having found it clear.
pub open spec fn flag_e(s: Mailbox, m: Envelope, e: Envelope) -> bool {
    idle(s, m) && scheduling(s, e, false)
}

/// Idle, and some sender has set `has` having found it clear.
pub open spec fn flagged(s: Mailbox, m: Envelope) -> bool {
    idle(s, m) && exists|e: Envelope| #[trigger] scheduling(s, e, false)
}

/// Idle, and `e` has enqueued and not yet set `has`.
pub open spec fn mark_e(s: Mailbox, m: Envelope, e: Envelope) -> bool {
    idle(s, m) && marked(s, e)
}

/// Idle, and some sender has enqueued and not yet set `has`.
pub open spec fn mark_any(s: Mailbox, m: Envelope) -> bool {
    idle(s, m) && exists|e: Envelope| #[trigger] marked(s, e)
}

pub open spec fn flagged_or_ready(s: Mailbox, m: Envelope) -> bool {
    flagged(s, m) || ready(s, m)
}

pub open spec fn p_queued(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| queued(s, m)
}

pub open spec fn p_done(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| done(s, m)
}

pub open spec fn p_claimed(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| claimed(s, m)
}

pub open spec fn p_ready(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| ready(s, m)
}

pub open spec fn p_drained(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| drained(s, m)
}

pub open spec fn p_awaiting(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| awaiting(s, m)
}

pub open spec fn p_idle(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| idle(s, m)
}

pub open spec fn p_flag_e(m: Envelope, e: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| flag_e(s, m, e)
}

pub open spec fn p_flagged(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| flagged(s, m)
}

pub open spec fn p_mark_e(m: Envelope, e: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| mark_e(s, m, e)
}

pub open spec fn p_mark_any(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| mark_any(s, m)
}

pub open spec fn p_flagged_or_ready(m: Envelope) -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| flagged_or_ready(s, m)
}

pub open spec fn f_inv() -> spec_fn(Mailbox) -> bool {
    |s: Mailbox| mb_inv(s)
}

pub open spec fn f_next() -> spec_fn(Mailbox, Mailbox) -> bool {
    |s: Mailbox, t: Mailbox| mb_next(s, t)
}

// -- Facts about sequences ------------------------------------------------------

proof fn lemma_push_contains(q: Seq<Envelope>, e: Envelope, m: Envelope)
    requires
        q.contains(m),
    ensures
        q.push(e).contains(m),
{
    let i = choose|i: int| 0 <= i < q.len() && q[i] == m;
    assert(q.push(e)[i] == m);
}

proof fn lemma_concat_contains(a: Seq<Envelope>, b: Seq<Envelope>, m: Envelope)
    requires
        b.contains(m),
    ensures
        (a + b).contains(m),
{
    let i = choose|i: int| 0 <= i < b.len() && b[i] == m;
    assert((a + b)[a.len() + i] == m);
}

proof fn lemma_concat_contains_left(a: Seq<Envelope>, b: Seq<Envelope>, m: Envelope)
    requires
        a.contains(m),
    ensures
        (a + b).contains(m),
{
    let i = choose|i: int| 0 <= i < a.len() && a[i] == m;
    assert((a + b)[i] == m);
}

/// A sender about to enqueue is not mid-operation on the message it is about to
/// number.
proof fn lemma_enqueue_fresh(s: Mailbox, sender: Id, body: Vec<u8>)
    requires
        mb_inv(s),
        mb_seq(s, sender) < u64::MAX,
    ensures
        !s.ops.contains_key(Envelope { sender, seq: mb_seq(s, sender) as u64, body }),
{
    let env = Envelope { sender, seq: mb_seq(s, sender) as u64, body };
    lemma_fresh(s, env);
}

// -- One step, from each stage --------------------------------------------------

/// From `Claimed`: stay `Claimed` with the message queued, or drain.
proof fn lemma_from_claimed(step: MbStep, s: Mailbox, t: Mailbox, m: Envelope)
    requires
        mb_step(step, s, t),
        claimed(s, m),
    ensures
        claimed(t, m) || (step is Drain && done(t, m)),
{
    match step {
        MbStep::Enqueue { sender, body } => {
            lemma_push_contains(s.queue, Envelope { sender, seq: mb_seq(s, sender) as u64, body }, m);
        },
        MbStep::Drain => {
            lemma_concat_contains(s.processed, s.queue, m);
        },
        _ => {},
    }
}

/// From `Await` and scheduled: stay so, or claim.
proof fn lemma_from_ready(step: MbStep, s: Mailbox, t: Mailbox, m: Envelope)
    requires
        mb_step(step, s, t),
        ready(s, m),
    ensures
        ready(t, m) || (step is Claim && claimed(t, m)),
{
    match step {
        MbStep::Enqueue { sender, body } => {
            lemma_push_contains(s.queue, Envelope { sender, seq: mb_seq(s, sender) as u64, body }, m);
        },
        _ => {},
    }
}

/// From `Drained`: stay so, or finish.
proof fn lemma_from_drained(step: MbStep, s: Mailbox, t: Mailbox, m: Envelope)
    requires
        mb_step(step, s, t),
        drained(s, m),
    ensures
        drained(t, m) || (step is Finish && awaiting(t, m)),
{
    match step {
        MbStep::Enqueue { sender, body } => {
            lemma_push_contains(s.queue, Envelope { sender, seq: mb_seq(s, sender) as u64, body }, m);
        },
        _ => {},
    }
}

/// From idle, with `e` having set `has` to find it clear: stay so, or the
/// wakeup happens. If the step is `e`'s own schedule, the wakeup happens.
proof fn lemma_from_flag(step: MbStep, s: Mailbox, t: Mailbox, m: Envelope, e: Envelope)
    requires
        mb_inv(s),
        mb_step(step, s, t),
        flag_e(s, m, e),
    ensures
        flag_e(t, m, e) || ready(t, m),
        (step is Schedule && step->Schedule_env == e) ==> ready(t, m),
{
    match step {
        MbStep::Enqueue { sender, body } => {
            lemma_push_contains(s.queue, Envelope { sender, seq: mb_seq(s, sender) as u64, body }, m);
            lemma_enqueue_fresh(s, sender, body);
            assert(e != Envelope { sender, seq: mb_seq(s, sender) as u64, body });
        },
        MbStep::SetState { env } => {
            assert(e != env);
        },
        MbStep::Schedule { env } => {
            if env == e {
                assert(stage_had(s.ops[e]) == false);
            } else {
                assert(t.ops.contains_key(e));
            }
        },
        _ => {},
    }
}

/// From idle, with `e` having enqueued and not set `has`: stay so, or something
/// closer to the wakeup. If the step is `e`'s own set-state, it is `flagged`.
proof fn lemma_from_mark(step: MbStep, s: Mailbox, t: Mailbox, m: Envelope, e: Envelope)
    requires
        mb_inv(s),
        mb_inv(t),
        mb_step(step, s, t),
        mark_e(s, m, e),
    ensures
        mark_e(t, m, e) || flagged(t, m) || ready(t, m),
        (step is SetState && step->SetState_env == e) ==> flagged(t, m),
{
    match step {
        MbStep::Enqueue { sender, body } => {
            lemma_push_contains(s.queue, Envelope { sender, seq: mb_seq(s, sender) as u64, body }, m);
            lemma_enqueue_fresh(s, sender, body);
            assert(e != Envelope { sender, seq: mb_seq(s, sender) as u64, body });
        },
        MbStep::SetState { env } => {
            if env == e {
                if s.has {
                    assert(t.dq is Await && t.has && !t.scheduled);
                } else {
                    assert(scheduling(t, e, false));
                }
            }
        },
        MbStep::Schedule { env } => {
            assert(env != e);
        },
        _ => {},
    }
}

// -- The stages as leads-to -----------------------------------------------------

/// What a run gives the proofs: the invariant at every step, and every step a
/// step.
proof fn lemma_run_facts(ex: spec_fn(nat) -> Mailbox)
    requires
        mb_run(ex),
    ensures
        forall|k: nat| #[trigger] f_inv()(ex(k)),
        forall|k: nat| #[trigger] f_next()(ex(k), ex(k + 1)),
{
    assert forall|k: nat| #[trigger] f_inv()(ex(k)) by {
        theorem_run_inv(ex, k);
    }
    assert forall|k: nat| #[trigger] f_next()(ex(k), ex(k + 1)) by {
        assert(mb_next(ex(k), ex(k + 1)));
    }
}

/// `Claimed ~> processed`, by the drain step.
proof fn stage_drain(ex: spec_fn(nat) -> Mailbox, m: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_claimed(m), p_done(m)),
{
    lemma_run_facts(ex);
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_claimed(m)(s) && #[trigger] f_next()(s, t) implies p_claimed(
        m,
    )(t) || p_done(m)(t) by {
        let step = choose|step: MbStep| #[trigger] mb_step(step, s, t);
        lemma_from_claimed(step, s, t, m);
    }
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_claimed(m)(s) && #[trigger] f_next()(s, t) && tk_drain()(
        s,
        t,
    ) implies p_done(m)(t) by {
        lemma_concat_contains(s.processed, s.queue, m);
    }
    lemma_wf1(ex, f_inv(), f_next(), en_drain(), tk_drain(), p_claimed(m), p_done(m));
}

/// `Await` and scheduled `~> Claimed`, by the claim step.
proof fn stage_claim(ex: spec_fn(nat) -> Mailbox, m: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_ready(m), p_claimed(m)),
{
    lemma_run_facts(ex);
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_ready(m)(s) && #[trigger] f_next()(s, t) implies p_ready(
        m,
    )(t) || p_claimed(m)(t) by {
        let step = choose|step: MbStep| #[trigger] mb_step(step, s, t);
        lemma_from_ready(step, s, t, m);
    }
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_ready(m)(s) && #[trigger] f_next()(s, t) && tk_claim()(
        s,
        t,
    ) implies p_claimed(m)(t) by {}
    lemma_wf1(ex, f_inv(), f_next(), en_claim(), tk_claim(), p_ready(m), p_claimed(m));
}

/// `Drained ~> Await`, by the finish step.
proof fn stage_finish(ex: spec_fn(nat) -> Mailbox, m: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_drained(m), p_awaiting(m)),
{
    lemma_run_facts(ex);
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_drained(m)(s) && #[trigger] f_next()(s, t) implies p_drained(
        m,
    )(t) || p_awaiting(m)(t) by {
        let step = choose|step: MbStep| #[trigger] mb_step(step, s, t);
        lemma_from_drained(step, s, t, m);
    }
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_drained(m)(s) && #[trigger] f_next()(s, t) && tk_finish()(
        s,
        t,
    ) implies p_awaiting(m)(t) by {}
    lemma_wf1(ex, f_inv(), f_next(), en_finish(), tk_finish(), p_drained(m), p_awaiting(m));
}

/// Idle, with `e` having set `has`, `~> ready`: `e`'s schedule step wakes the
/// drain. This is the step that cannot be skipped — and the drain is asleep, so
/// `processing` is clear and `e` does schedule.
proof fn stage_schedule(ex: spec_fn(nat) -> Mailbox, m: Envelope, e: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_flag_e(m, e), p_ready(m)),
{
    lemma_run_facts(ex);
    assert(fair_schedule(ex, e));
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_flag_e(m, e)(s) && #[trigger] f_next()(s, t) implies p_flag_e(
        m,
        e,
    )(t) || p_ready(m)(t) by {
        let step = choose|step: MbStep| #[trigger] mb_step(step, s, t);
        lemma_from_flag(step, s, t, m, e);
    }
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_flag_e(m, e)(s) && #[trigger] f_next()(s, t)
            && tk_schedule(e)(s, t) implies p_ready(m)(t) by {
        let step = choose|step: MbStep| #[trigger] mb_step(step, s, t);
        lemma_from_flag(step, s, t, m, e);
    }
    lemma_wf1(ex, f_inv(), f_next(), en_schedule(e), tk_schedule(e), p_flag_e(m, e), p_ready(m));
}

/// Idle, with `e` having enqueued and not set `has`, `~> flagged or ready`: `e`'s
/// set-state step sets `has` — and either finds it clear, and is the sender that
/// will wake the drain, or finds it set, and the invariant says another is.
proof fn stage_set_state(ex: spec_fn(nat) -> Mailbox, m: Envelope, e: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_mark_e(m, e), p_flagged_or_ready(m)),
{
    lemma_run_facts(ex);
    assert(fair_set_state(ex, e));
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_mark_e(m, e)(s) && #[trigger] f_next()(s, t) implies p_mark_e(
        m,
        e,
    )(t) || p_flagged_or_ready(m)(t) by {
        let step = choose|step: MbStep| #[trigger] mb_step(step, s, t);
        lemma_from_mark(step, s, t, m, e);
    }
    assert forall|s: Mailbox, t: Mailbox|
        f_inv()(s) && f_inv()(t) && p_mark_e(m, e)(s) && #[trigger] f_next()(s, t)
            && tk_set_state(e)(s, t) implies p_flagged_or_ready(m)(t) by {
        let step = choose|step: MbStep| #[trigger] mb_step(step, s, t);
        lemma_from_mark(step, s, t, m, e);
    }
    lemma_wf1(
        ex,
        f_inv(),
        f_next(),
        en_set_state(e),
        tk_set_state(e),
        p_mark_e(m, e),
        p_flagged_or_ready(m),
    );
}

/// Some sender has set `has` `~> ready`.
proof fn stage_flagged(ex: spec_fn(nat) -> Mailbox, m: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_flagged(m), p_ready(m)),
{
    assert forall|i: nat| #[trigger] p_flagged(m)(ex(i)) implies exists|j: nat|
        i <= j && #[trigger] p_ready(m)(ex(j)) by {
        let s = ex(i);
        let e = choose|e: Envelope| #[trigger] scheduling(s, e, false);
        stage_schedule(ex, m, e);
        assert(p_flag_e(m, e)(ex(i)));
    }
}

/// Some sender has enqueued and not set `has` `~> ready`.
proof fn stage_marked(ex: spec_fn(nat) -> Mailbox, m: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_mark_any(m), p_ready(m)),
{
    assert forall|i: nat| #[trigger] p_mark_any(m)(ex(i)) implies exists|j: nat|
        i <= j && #[trigger] p_ready(m)(ex(j)) by {
        let s = ex(i);
        let e = choose|e: Envelope| #[trigger] marked(s, e);
        stage_set_state(ex, m, e);
        assert(p_mark_e(m, e)(ex(i)));
        let j = choose|j: nat| i <= j && #[trigger] p_flagged_or_ready(m)(ex(j));
        stage_flagged(ex, m);
        if flagged(ex(j), m) {
            assert(p_flagged(m)(ex(j)));
            let k = choose|k: nat| j <= k && #[trigger] p_ready(m)(ex(k));
        } else {
            assert(ready(ex(j), m));
            assert(p_ready(m)(ex(j)));
        }
    }
}

/// **The lost-wakeup case.** Queued with the drain at the top of its loop and
/// nothing scheduled `~> scheduled`: the invariant says some sender is on its way
/// to scheduling, and fairness says it gets there.
proof fn stage_idle(ex: spec_fn(nat) -> Mailbox, m: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_idle(m), p_ready(m)),
{
    stage_flagged(ex, m);
    stage_marked(ex, m);
    assert forall|i: nat| #[trigger] p_idle(m)(ex(i)) implies exists|j: nat|
        i <= j && #[trigger] p_ready(m)(ex(j)) by {
        let s = ex(i);
        theorem_run_inv(ex, i);
        if s.has {
            assert(flagged(s, m));
            assert(p_flagged(m)(s));
        } else {
            assert(s.queue.len() > 0);
            assert(mark_any(s, m));
            assert(p_mark_any(m)(s));
        }
    }
}

/// **The theorem.** In every run in which the mailbox's steps are not starved, a
/// message that is on the queue is later processed.
pub proof fn theorem_every_enqueued_message_is_processed(ex: spec_fn(nat) -> Mailbox, m: Envelope)
    requires
        mb_run(ex),
        mailbox_fair(ex),
    ensures
        leads_to(ex, p_queued(m), p_done(m)),
{
    stage_drain(ex, m);
    stage_claim(ex, m);
    stage_finish(ex, m);
    stage_idle(ex, m);
    assert forall|i: nat| #[trigger] p_queued(m)(ex(i)) implies exists|j: nat|
        i <= j && #[trigger] p_done(m)(ex(j)) by {
        let s = ex(i);
        if s.dq is Claimed {
            assert(p_claimed(m)(s));
        } else if s.dq is Drained {
            assert(p_drained(m)(s));
            let a = choose|a: nat| i <= a && #[trigger] p_awaiting(m)(ex(a));
            to_done_from_awaiting(ex, m, a);
        } else {
            assert(p_awaiting(m)(s));
            to_done_from_awaiting(ex, m, i);
        }
    }
}

/// From the top of the drain's loop with the message queued: processed.
proof fn to_done_from_awaiting(ex: spec_fn(nat) -> Mailbox, m: Envelope, i: nat)
    requires
        mb_run(ex),
        mailbox_fair(ex),
        awaiting(ex(i), m),
    ensures
        exists|j: nat| i <= j && #[trigger] p_done(m)(ex(j)),
{
    stage_idle(ex, m);
    stage_claim(ex, m);
    stage_drain(ex, m);
    let s = ex(i);
    let r = if s.scheduled {
        i
    } else {
        assert(p_idle(m)(s));
        choose|r: nat| i <= r && #[trigger] p_ready(m)(ex(r))
    };
    assert(p_ready(m)(ex(r)));
    let c = choose|c: nat| r <= c && #[trigger] p_claimed(m)(ex(c));
    let d = choose|d: nat| c <= d && #[trigger] p_done(m)(ex(d));
}

} // verus!
