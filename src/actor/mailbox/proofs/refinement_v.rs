//! The executable core is the model.
//!
//! [`crate::actor::mailbox::exec::MailboxCore`] is the protocol as code, and each
//! of its methods has a `core_*` contract. The obligations are the ones
//! [`crate::actor::proofs::refinement`] discharges for the actor's steps, now for
//! a step with state: when the core takes a step, the model takes the matching
//! one, to a state the core still stands for; and when the core refuses, the
//! model's step is not enabled in *any* post-state.
//!
//! # The relation
//!
//! The core's items are opaque — the runtime's are deliveries, not the model's
//! [`Envelope`]s — so the relation is parameterised by a function `abs` from an
//! item to the envelope it stands for. [`refines`] says the core's queue, mapped
//! through `abs`, is the model's queue, and that the flags and the drain's phase
//! agree. The theorems hold for every `abs`.
//!
//! # What is not here
//!
//! The model also tracks `ops` (each sender's operation in flight), `next_seq` and
//! `processed`. The core has none of them, so [`refines`] says nothing about them
//! and the theorems *construct* the model's post-state, taking the sender's
//! protocol as a hypothesis where a step needs it:
//!
//! * `enqueue` needs the item to stand for the envelope the model would number
//!   next, `abs(item) == Envelope { sender, seq: mb_seq(m, sender), body }`;
//! * `set_state` needs the model to have an operation `Marked` for the message;
//! * `schedule` needs one `Scheduling`, with `had` being what `set_state`
//!   returned for it.
//!
//! These are exactly "the caller does what a sender does", and they are what the
//! runtime's `Permit` and `Session` are for.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::mailbox::exec::*;
use crate::actor::mailbox::model::*;
use crate::actor::model::Envelope;
use crate::id::Id;

verus! {

/// The core `c` stands for the model state `m`, reading each item as `abs` says.
pub open spec fn refines<T>(abs: spec_fn(T) -> Envelope, c: MailboxCore<T>, m: Mailbox) -> bool {
    &&& c.queue@.map_values(abs) =~= m.queue
    &&& c.has == m.has
    &&& c.scheduled == m.scheduled
    &&& dq_of(c.phase) == m.dq
    &&& m.processing == !(c.phase is Await)
}

/// **A fresh core is the model's initial state.**
pub proof fn theorem_new_refines_init<T>(abs: spec_fn(T) -> Envelope, c: MailboxCore<T>)
    requires
        c.queue@ == Seq::<T>::empty(),
        !c.has,
        !c.scheduled,
        c.phase is Await,
    ensures
        exists|m: Mailbox| mb_init(m) && refines(abs, c, m),
{
    let m = Mailbox {
        queue: Seq::empty(),
        processed: Seq::empty(),
        has: false,
        processing: false,
        scheduled: false,
        dq: Dq::Await,
        ops: Map::empty(),
        next_seq: Map::empty(),
    };
    assert(c.queue@.map_values(abs) =~= m.queue);
    assert(mb_init(m));
    assert(refines(abs, c, m));
}

/// **`enqueue` is the model's `mb_enqueue`**, for the sender and number the item
/// stands for.
pub proof fn theorem_enqueue_refines<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    c2: MailboxCore<T>,
    m: Mailbox,
    item: T,
    sender: Id,
    body: nat,
)
    requires
        refines(abs, c, m),
        core_enqueue(c, c2, item),
        abs(item) == (Envelope { sender, seq: mb_seq(m, sender), body }),
    ensures
        exists|m2: Mailbox| mb_enqueue(m, m2, sender, body) && refines(abs, c2, m2),
{
    let env = Envelope { sender, seq: mb_seq(m, sender), body };
    let m2 = Mailbox {
        queue: m.queue.push(env),
        ops: m.ops.insert(env, Stage::Marked),
        next_seq: m.next_seq.insert(sender, env.seq + 1),
        ..m
    };
    assert(mb_enqueue(m, m2, sender, body));
    assert(c2.queue@.map_values(abs) =~= m2.queue) by {
        assert(c2.queue@ == c.queue@.push(item));
        assert(c.queue@.push(item).map_values(abs) =~= c.queue@.map_values(abs).push(abs(item)));
    }
    assert(refines(abs, c2, m2));
}

/// **`set_state` is the model's `mb_set_state`**, for a message whose sender is
/// mid-operation — and what it returns is what that operation recorded.
pub proof fn theorem_set_state_refines<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    c2: MailboxCore<T>,
    m: Mailbox,
    had: bool,
    env: Envelope,
)
    requires
        refines(abs, c, m),
        core_set_state(c, c2),
        had == c.has,
        marked(m, env),
    ensures
        exists|m2: Mailbox|
            mb_set_state(m, m2, env) && refines(abs, c2, m2) && stage_had(m2.ops[env]) == had,
{
    let m2 = Mailbox {
        has: true,
        ops: m.ops.insert(env, Stage::Scheduling { had: m.has }),
        ..m
    };
    assert(mb_set_state(m, m2, env));
    assert(refines(abs, c2, m2));
}

/// **`schedule` is the model's `mb_schedule`**, for a message whose sender has
/// set `has` and is passing back what it saw.
pub proof fn theorem_schedule_refines<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    c2: MailboxCore<T>,
    m: Mailbox,
    had: bool,
    env: Envelope,
)
    requires
        refines(abs, c, m),
        core_schedule(c, c2, had),
        is_scheduling(m, env),
        had == stage_had(m.ops[env]),
    ensures
        exists|m2: Mailbox| mb_schedule(m, m2, env) && refines(abs, c2, m2),
{
    let m2 = Mailbox {
        ops: m.ops.remove(env),
        scheduled: m.scheduled || (!stage_had(m.ops[env]) && !m.processing),
        ..m
    };
    assert(mb_schedule(m, m2, env));
    assert(refines(abs, c2, m2));
}

/// **`claim` is the model's `mb_claim`.**
pub proof fn theorem_claim_refines<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    c2: MailboxCore<T>,
    m: Mailbox,
)
    requires
        refines(abs, c, m),
        core_claim(c, c2),
    ensures
        exists|m2: Mailbox| mb_claim(m, m2) && refines(abs, c2, m2),
{
    let m2 = Mailbox { processing: true, has: false, dq: Dq::Claimed, ..m };
    assert(mb_claim(m, m2));
    assert(refines(abs, c2, m2));
}

/// **A refused claim is a step the model could not have taken**, whatever state
/// it was sent to.
pub proof fn theorem_claim_refuses_exactly_when_disabled<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    m: Mailbox,
    m2: Mailbox,
)
    requires
        refines(abs, c, m),
        !core_claim_enabled(c),
    ensures
        !mb_claim(m, m2),
{
}

/// **`take` is the model's `mb_drain`**, and what it hands out is what the model
/// adds to `processed`: the queue, in order.
pub proof fn theorem_take_refines<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    c2: MailboxCore<T>,
    m: Mailbox,
    taken: Seq<T>,
)
    requires
        refines(abs, c, m),
        core_take(c, c2, taken),
    ensures
        exists|m2: Mailbox|
            mb_drain(m, m2) && refines(abs, c2, m2) && m2.processed =~= m.processed
                + taken.map_values(abs),
{
    let m2 = Mailbox {
        processed: m.processed + m.queue,
        queue: Seq::empty(),
        dq: Dq::Drained,
        ..m
    };
    assert(taken.map_values(abs) =~= m.queue);
    assert(mb_drain(m, m2));
    assert(c2.queue@.map_values(abs) =~= m2.queue);
    assert(refines(abs, c2, m2));
}

/// **A refused take is a step the model could not have taken.**
pub proof fn theorem_take_refuses_exactly_when_disabled<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    m: Mailbox,
    m2: Mailbox,
)
    requires
        refines(abs, c, m),
        !(c.phase is Claimed),
    ensures
        !mb_drain(m, m2),
{
}

/// **`finish` is the model's `mb_finish`.**
pub proof fn theorem_finish_refines<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    c2: MailboxCore<T>,
    m: Mailbox,
)
    requires
        refines(abs, c, m),
        core_finish(c, c2),
    ensures
        exists|m2: Mailbox| mb_finish(m, m2) && refines(abs, c2, m2),
{
    let m2 = Mailbox { scheduled: m.has, processing: false, dq: Dq::Await, ..m };
    assert(mb_finish(m, m2));
    assert(refines(abs, c2, m2));
}

/// **A refused finish is a step the model could not have taken.**
pub proof fn theorem_finish_refuses_exactly_when_disabled<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    m: Mailbox,
    m2: Mailbox,
)
    requires
        refines(abs, c, m),
        !(c.phase is Drained),
    ensures
        !mb_finish(m, m2),
{
}

/// **A step that changes nothing is the model's stutter**, so the core's total
/// methods, called out of order, never leave the model's runs.
pub proof fn theorem_a_stutter_refines<T>(
    abs: spec_fn(T) -> Envelope,
    c: MailboxCore<T>,
    c2: MailboxCore<T>,
    m: Mailbox,
)
    requires
        refines(abs, c, m),
        core_stutter(c, c2),
    ensures
        mb_stutter(m, m) && refines(abs, c2, m),
{
    assert(c2.queue@ == c.queue@);
    assert(refines(abs, c2, m));
}

} // verus!
