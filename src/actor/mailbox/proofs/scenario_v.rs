//! **The guarantees are not vacuous, and the fairness assumption is not
//! decoration.**
//!
//! The liveness theorem is an implication: *if* a run is fair, *then* a queued
//! message is processed. An implication whose hypothesis nothing satisfies is
//! true and says nothing, and one whose hypothesis the conclusion does not need
//! is a theorem about a weaker machine than it appears to be. Two runs, written
//! out in full, check both.
//!
//! * [`scenario_a_fair_run_delivers_two_messages`] — a run that is a run of the
//!   machine **and** satisfies [`mailbox_fair`], in which a message is queued and
//!   later processed, including one that arrives while the drain is mid-loop.
//!   The theorem's hypotheses are met by something that does work.
//! * [`scenario_without_fairness_a_message_waits_forever`] — a run of the machine
//!   in which a message is enqueued and never processed. It is not fair, and
//!   [`mailbox_fair`] is exactly what it fails: the sender's own `set_state`
//!   step stays possible forever and is never taken. Remove the assumption and
//!   the theorem is false.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::mailbox::model::*;
use crate::actor::mailbox::proofs::invariant::*;
use crate::actor::mailbox::proofs::liveness::*;
use crate::actor::model::Envelope;
use crate::id::Id;
use crate::temporal::*;

verus! {

/// Sender 1's first message.
pub open spec fn msg_a(b5: Vec<u8>, b7: Vec<u8>) -> Envelope {
    Envelope { sender: Id(1), seq: 0, body: b5 }
}

/// Sender 1's second message.
pub open spec fn msg_b(b5: Vec<u8>, b7: Vec<u8>) -> Envelope {
    Envelope { sender: Id(1), seq: 1, body: b7 }
}

pub open spec fn sc0(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        queue: Seq::empty(),
        processed: Seq::empty(),
        has: false,
        processing: false,
        scheduled: false,
        dq: Dq::Await,
        ops: Map::empty(),
        next_seq: Map::empty(),
    }
}

/// `A` is enqueued.
pub open spec fn sc1(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        queue: sc0(b5, b7).queue.push(msg_a(b5, b7)),
        ops: sc0(b5, b7).ops.insert(msg_a(b5, b7), Stage::Marked),
        next_seq: sc0(b5, b7).next_seq.insert(Id(1), 1),
        ..sc0(b5, b7)
    }
}

/// `A`'s sender sets `has`, finding it clear.
pub open spec fn sc2(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        has: true,
        ops: sc1(b5, b7).ops.insert(msg_a(b5, b7), Stage::Scheduling { had: sc1(b5, b7).has }),
        ..sc1(b5, b7)
    }
}

/// `A`'s sender wakes the drain.
pub open spec fn sc3(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        ops: sc2(b5, b7).ops.remove(msg_a(b5, b7)),
        scheduled: sc2(b5, b7).scheduled || (!stage_had(sc2(b5, b7).ops[msg_a(b5, b7)]) && !sc2(b5, b7).processing),
        ..sc2(b5, b7)
    }
}

/// The drain wakes.
pub open spec fn sc4(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox { processing: true, has: false, dq: Dq::Claimed, ..sc3(b5, b7) }
}

/// The drain takes `A`.
pub open spec fn sc5(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        processed: sc4(b5, b7).processed + sc4(b5, b7).queue,
        queue: Seq::empty(),
        dq: Dq::Drained,
        ..sc4(b5, b7)
    }
}

/// `B` arrives while the drain is still running.
pub open spec fn sc6(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        queue: sc5(b5, b7).queue.push(msg_b(b5, b7)),
        ops: sc5(b5, b7).ops.insert(msg_b(b5, b7), Stage::Marked),
        next_seq: sc5(b5, b7).next_seq.insert(Id(1), 2),
        ..sc5(b5, b7)
    }
}

/// `B`'s sender sets `has`. The drain cleared it when it woke, so it finds it
/// clear.
pub open spec fn sc7(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        has: true,
        ops: sc6(b5, b7).ops.insert(msg_b(b5, b7), Stage::Scheduling { had: sc6(b5, b7).has }),
        ..sc6(b5, b7)
    }
}

/// `B`'s sender does **not** wake the drain: it is running.
pub open spec fn sc8(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        ops: sc7(b5, b7).ops.remove(msg_b(b5, b7)),
        scheduled: sc7(b5, b7).scheduled || (!stage_had(sc7(b5, b7).ops[msg_b(b5, b7)]) && !sc7(b5, b7).processing),
        ..sc7(b5, b7)
    }
}

/// The drain's last step sees `has` and stays scheduled — **this** is what wakes
/// it for `B`.
pub open spec fn sc9(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox { scheduled: sc8(b5, b7).has, processing: false, dq: Dq::Await, ..sc8(b5, b7) }
}

pub open spec fn sc10(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox { processing: true, has: false, dq: Dq::Claimed, ..sc9(b5, b7) }
}

/// The drain takes `B`.
pub open spec fn sc11(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox {
        processed: sc10(b5, b7).processed + sc10(b5, b7).queue,
        queue: Seq::empty(),
        dq: Dq::Drained,
        ..sc10(b5, b7)
    }
}

/// Nothing set `has` meanwhile, so the drain goes back to sleep.
pub open spec fn sc12(b5: Vec<u8>, b7: Vec<u8>) -> Mailbox {
    Mailbox { scheduled: sc11(b5, b7).has, processing: false, dq: Dq::Await, ..sc11(b5, b7) }
}

/// The fair run: the twelve steps, then nothing happens.
pub open spec fn fair_state(b5: Vec<u8>, b7: Vec<u8>, i: nat) -> Mailbox {
    if i == 0 {
        sc0(b5, b7)
    } else if i == 1 {
        sc1(b5, b7)
    } else if i == 2 {
        sc2(b5, b7)
    } else if i == 3 {
        sc3(b5, b7)
    } else if i == 4 {
        sc4(b5, b7)
    } else if i == 5 {
        sc5(b5, b7)
    } else if i == 6 {
        sc6(b5, b7)
    } else if i == 7 {
        sc7(b5, b7)
    } else if i == 8 {
        sc8(b5, b7)
    } else if i == 9 {
        sc9(b5, b7)
    } else if i == 10 {
        sc10(b5, b7)
    } else if i == 11 {
        sc11(b5, b7)
    } else {
        sc12(b5, b7)
    }
}

/// The facts about the flags that the steps' guards read.
proof fn lemma_flags(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        !sc1(b5, b7).has,
        sc2(b5, b7).has,
        sc3(b5, b7).scheduled,
        !sc3(b5, b7).processing,
        sc4(b5, b7).scheduled,
        !sc4(b5, b7).has,
        sc4(b5, b7).dq is Claimed,
        sc5(b5, b7).dq is Claimed == false,
        !sc6(b5, b7).has,
        sc6(b5, b7).processing,
        sc7(b5, b7).has,
        sc8(b5, b7).scheduled,
        sc8(b5, b7).has,
        sc9(b5, b7).scheduled,
        sc9(b5, b7).dq is Await,
        sc10(b5, b7).dq is Claimed,
        !sc10(b5, b7).has,
        sc11(b5, b7).dq is Drained,
        !sc11(b5, b7).has,
        !sc12(b5, b7).scheduled,
        sc12(b5, b7).dq is Await,
{
    assert(sc0(b5, b7).next_seq =~= Map::<Id, nat>::empty());
}

/// Each step of the fair run is a step of the machine.
proof fn lemma_fair_steps(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        mb_init(sc0(b5, b7)),
        mb_enqueue(sc0(b5, b7), sc1(b5, b7), Id(1), b5),
        mb_set_state(sc1(b5, b7), sc2(b5, b7), msg_a(b5, b7)),
        mb_schedule(sc2(b5, b7), sc3(b5, b7), msg_a(b5, b7)),
        mb_claim(sc3(b5, b7), sc4(b5, b7)),
        mb_drain(sc4(b5, b7), sc5(b5, b7)),
        mb_enqueue(sc5(b5, b7), sc6(b5, b7), Id(1), b7),
        mb_set_state(sc6(b5, b7), sc7(b5, b7), msg_b(b5, b7)),
        mb_schedule(sc7(b5, b7), sc8(b5, b7), msg_b(b5, b7)),
        mb_finish(sc8(b5, b7), sc9(b5, b7)),
        mb_claim(sc9(b5, b7), sc10(b5, b7)),
        mb_drain(sc10(b5, b7), sc11(b5, b7)),
        mb_finish(sc11(b5, b7), sc12(b5, b7)),
{
    lemma_flags(b5, b7);
    assert(mb_seq(sc0(b5, b7), Id(1)) == 0);
    assert(mb_seq(sc5(b5, b7), Id(1)) == 1);
    assert(marked(sc1(b5, b7), msg_a(b5, b7)));
    assert(is_scheduling(sc2(b5, b7), msg_a(b5, b7)));
    assert(marked(sc6(b5, b7), msg_b(b5, b7)));
    assert(is_scheduling(sc7(b5, b7), msg_b(b5, b7)));
}

/// The fair run is a run of the machine.
proof fn lemma_fair_run(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        mb_run(|i: nat| fair_state(b5, b7, i)),
{
    lemma_fair_steps(b5, b7);
    let ex = |i: nat| fair_state(b5, b7, i);
    assert forall|i: nat| #[trigger] mb_next(ex(i), ex(i + 1)) by {
        if i == 0 {
            assert(mb_step(MbStep::Enqueue { sender: Id(1), body: b5 }, ex(0), ex(1)));
        } else if i == 1 {
            assert(mb_step(MbStep::SetState { env: msg_a(b5, b7) }, ex(1), ex(2)));
        } else if i == 2 {
            assert(mb_step(MbStep::Schedule { env: msg_a(b5, b7) }, ex(2), ex(3)));
        } else if i == 3 {
            assert(mb_step(MbStep::Claim, ex(3), ex(4)));
        } else if i == 4 {
            assert(mb_step(MbStep::Drain, ex(4), ex(5)));
        } else if i == 5 {
            assert(mb_step(MbStep::Enqueue { sender: Id(1), body: b7 }, ex(5), ex(6)));
        } else if i == 6 {
            assert(mb_step(MbStep::SetState { env: msg_b(b5, b7) }, ex(6), ex(7)));
        } else if i == 7 {
            assert(mb_step(MbStep::Schedule { env: msg_b(b5, b7) }, ex(7), ex(8)));
        } else if i == 8 {
            assert(mb_step(MbStep::Finish, ex(8), ex(9)));
        } else if i == 9 {
            assert(mb_step(MbStep::Claim, ex(9), ex(10)));
        } else if i == 10 {
            assert(mb_step(MbStep::Drain, ex(10), ex(11)));
        } else if i == 11 {
            assert(mb_step(MbStep::Finish, ex(11), ex(12)));
        } else {
            assert(mb_step(MbStep::Stutter, ex(i), ex(i + 1)));
        }
    }
}

/// After the last step, nothing is enabled: no step the fairness assumption
/// speaks of can be taken.
proof fn lemma_fair_end_disables(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        !en_claim()(sc12(b5, b7)),
        !en_drain()(sc12(b5, b7)),
        !en_finish()(sc12(b5, b7)),
        forall|env: Envelope| !#[trigger] en_set_state(env)(sc12(b5, b7)),
        forall|env: Envelope| !#[trigger] en_schedule(env)(sc12(b5, b7)),
{
    lemma_flags(b5, b7);
    assert(sc12(b5, b7).ops =~= Map::<Envelope, Stage>::empty()) by {
        assert(sc0(b5, b7).ops =~= Map::<Envelope, Stage>::empty());
    }
}

/// **The fair run satisfies the fairness assumption**, vacuously after its last
/// step: from then on nothing is enabled, so nothing is owed.
proof fn lemma_fair_run_is_fair(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        mailbox_fair(|i: nat| fair_state(b5, b7, i)),
{
    lemma_fair_end_disables(b5, b7);
    let ex = |i: nat| fair_state(b5, b7, i);
    // For every i, `enabled` fails at the later of i and 12.
    assert forall|i: nat| #[trigger] enabled_from(ex, en_claim(), i) implies exists|j: nat|
        i <= j && #[trigger] tk_claim()(ex(j), ex(j + 1)) by {
        let j = if i < 12 { 12nat } else { i };
        assert(ex(j) == sc12(b5, b7));
        assert(en_claim()(ex(j)));
    }
    assert forall|i: nat| #[trigger] enabled_from(ex, en_drain(), i) implies exists|j: nat|
        i <= j && #[trigger] tk_drain()(ex(j), ex(j + 1)) by {
        let j = if i < 12 { 12nat } else { i };
        assert(ex(j) == sc12(b5, b7));
        assert(en_drain()(ex(j)));
    }
    assert forall|i: nat| #[trigger] enabled_from(ex, en_finish(), i) implies exists|j: nat|
        i <= j && #[trigger] tk_finish()(ex(j), ex(j + 1)) by {
        let j = if i < 12 { 12nat } else { i };
        assert(ex(j) == sc12(b5, b7));
        assert(en_finish()(ex(j)));
    }
    assert forall|env: Envelope| #[trigger] fair_set_state(ex, env) by {
        assert forall|i: nat| #[trigger] enabled_from(ex, en_set_state(env), i) implies exists|
            j: nat,
        | i <= j && #[trigger] tk_set_state(env)(ex(j), ex(j + 1)) by {
            let j = if i < 12 { 12nat } else { i };
            assert(ex(j) == sc12(b5, b7));
            assert(en_set_state(env)(ex(j)));
        }
    }
    assert forall|env: Envelope| #[trigger] fair_schedule(ex, env) by {
        assert forall|i: nat| #[trigger] enabled_from(ex, en_schedule(env), i) implies exists|
            j: nat,
        | i <= j && #[trigger] tk_schedule(env)(ex(j), ex(j + 1)) by {
            let j = if i < 12 { 12nat } else { i };
            assert(ex(j) == sc12(b5, b7));
            assert(en_schedule(env)(ex(j)));
        }
    }
}

/// **A fair run, in which messages arrive and are processed.**
///
/// There is a run of the machine that satisfies [`mailbox_fair`], in which `A` is
/// queued at step 1 and processed by step 5, and `B` — which arrives after the
/// drain has already taken the queue — is queued at step 6 and processed by
/// step 11. The liveness theorem's hypotheses are satisfied, by a run that
/// delivers.
pub proof fn scenario_a_fair_run_delivers_two_messages(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        exists|ex: spec_fn(nat) -> Mailbox|
            {
                &&& mb_run(ex)
                &&& mailbox_fair(ex)
                &&& queued(ex(1), msg_a(b5, b7))
                &&& done(ex(5), msg_a(b5, b7))
                &&& queued(ex(6), msg_b(b5, b7))
                &&& done(ex(11), msg_b(b5, b7))
                &&& ex(12).processed =~= seq![msg_a(b5, b7), msg_b(b5, b7)]
            },
{
    lemma_fair_run(b5, b7);
    lemma_fair_run_is_fair(b5, b7);
    let ex = |i: nat| fair_state(b5, b7, i);
    lemma_flags(b5, b7);
    assert(ex(1) == sc1(b5, b7));
    assert(ex(5) == sc5(b5, b7));
    assert(ex(6) == sc6(b5, b7));
    assert(ex(11) == sc11(b5, b7));
    assert(ex(12) == sc12(b5, b7));
    assert(sc1(b5, b7).queue =~= seq![msg_a(b5, b7)]);
    assert(sc5(b5, b7).processed =~= seq![msg_a(b5, b7)]);
    assert(sc6(b5, b7).queue =~= seq![msg_b(b5, b7)]);
    assert(sc11(b5, b7).processed =~= seq![msg_a(b5, b7), msg_b(b5, b7)]);
    assert(queued(ex(1), msg_a(b5, b7)));
    assert(done(ex(5), msg_a(b5, b7)));
    assert(queued(ex(6), msg_b(b5, b7)));
    assert(done(ex(11), msg_b(b5, b7)));
}

/// **The same run is a fair run to which the theorem applies**: `B` is processed
/// because the theorem says it is, not only because the run was written down.
pub proof fn scenario_the_theorem_applies_to_it(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        exists|ex: spec_fn(nat) -> Mailbox|
            {
                &&& mb_run(ex)
                &&& mailbox_fair(ex)
                &&& leads_to(ex, p_queued(msg_b(b5, b7)), p_done(msg_b(b5, b7)))
            },
{
    lemma_fair_run(b5, b7);
    lemma_fair_run_is_fair(b5, b7);
    let ex = |i: nat| fair_state(b5, b7, i);
    theorem_every_enqueued_message_is_processed(ex, msg_b(b5, b7));
}

/// The unfair run: `A` is enqueued, and then nothing ever happens.
pub open spec fn stuck_state(b5: Vec<u8>, b7: Vec<u8>, i: nat) -> Mailbox {
    if i == 0 {
        sc0(b5, b7)
    } else {
        sc1(b5, b7)
    }
}

/// **Without fairness, a message waits forever.**
///
/// A run of the machine in which `A` is enqueued at step 1 and never processed,
/// and which is **not** fair: its sender's `set_state` is possible at every step
/// from 1 on and is never taken. This is the lost wakeup the protocol exists to
/// prevent, reached not by a bug in the protocol but by a scheduler that stops
/// listening — and it is why [`mailbox_fair`] is in the theorem.
pub proof fn scenario_without_fairness_a_message_waits_forever(b5: Vec<u8>, b7: Vec<u8>)
    requires
        b5@ == seq![5u8],
        b7@ == seq![7u8],
    ensures
        exists|ex: spec_fn(nat) -> Mailbox|
            {
                &&& mb_run(ex)
                &&& queued(ex(1), msg_a(b5, b7))
                &&& forall|j: nat| !#[trigger] done(ex(j), msg_a(b5, b7))
                &&& !mailbox_fair(ex)
            },
{
    lemma_fair_steps(b5, b7);
    lemma_flags(b5, b7);
    let ex = |i: nat| stuck_state(b5, b7, i);
    assert forall|i: nat| #[trigger] mb_next(ex(i), ex(i + 1)) by {
        if i == 0 {
            assert(mb_step(MbStep::Enqueue { sender: Id(1), body: b5 }, ex(0), ex(1)));
        } else {
            assert(mb_step(MbStep::Stutter, ex(i), ex(i + 1)));
        }
    }
    assert(sc0(b5, b7).processed =~= Seq::<Envelope>::empty());
    assert(sc1(b5, b7).processed =~= Seq::<Envelope>::empty());
    assert forall|j: nat| !#[trigger] done(ex(j), msg_a(b5, b7)) by {
        assert(ex(j).processed.len() == 0);
    }
    assert(ex(1) == sc1(b5, b7));
    assert(sc1(b5, b7).queue[0] == msg_a(b5, b7));
    assert(sc1(b5, b7).queue.contains(msg_a(b5, b7)));
    assert(queued(ex(1), msg_a(b5, b7)));
    // `A`'s own set-state step is possible from step 1 on, and never taken.
    assert(marked(sc1(b5, b7), msg_a(b5, b7)));
    assert(enabled_from(ex, en_set_state(msg_a(b5, b7)), 1)) by {
        assert forall|j: nat| 1 <= j implies #[trigger] en_set_state(msg_a(b5, b7))(ex(j)) by {
            assert(ex(j) == sc1(b5, b7));
        }
    }
    if fair_set_state(ex, msg_a(b5, b7)) {
        let j = choose|j: nat| 1 <= j && #[trigger] tk_set_state(msg_a(b5, b7))(ex(j), ex(j + 1));
        assert(ex(j) == sc1(b5, b7));
        assert(ex(j + 1) == sc1(b5, b7));
        assert(mb_set_state(sc1(b5, b7), sc1(b5, b7), msg_a(b5, b7)));
        assert(sc1(b5, b7).has);
    }
    assert(!fair_set_state(ex, msg_a(b5, b7)));
    assert(ex(0) == sc0(b5, b7));
    assert(mb_run(ex));
    assert(!mailbox_fair(ex));
    assert(forall|j: nat| !#[trigger] done(ex(j), msg_a(b5, b7)));
}

} // verus!
