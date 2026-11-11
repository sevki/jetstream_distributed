//! **What the register keeps true**, stated of the specification
//! ([`crate::quepaxa::isr_spec`]), which keeps the whole history.
//!
//! These are facts about the *history*, which the constant-space register
//! ([`crate::quepaxa::isr`]) does not hold. They reach it only through the
//! refinement: it stands for such a history ([`Isr::related`](crate::quepaxa::isr::Isr::related))
//! and answers what the history answers, so a reply built from a frozen step is a reply
//! built from a value that cannot have changed.
//!
//! QuePaxa's safety argument leans on a recorder's replies not moving under a
//! proposer's feet. These are the facts it would lean on, none of which mentions
//! a proposer: a recorder's step never goes backward; a step the recorder has left
//! behind is **frozen**, first value and aggregate alike; and an aggregate only ever
//! grows, so the best proposal a recorder has seen at a step never gets worse. The
//! argument that uses them is the paper's concrete protocol's, and is not here.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::quepaxa::isr_spec::*;

verus! {

/// **The step never goes backward.**
pub proof fn theorem_the_step_never_decreases(h: IsrHistory, s: nat, v: nat)
    ensures
        isr_record(h, s, v).s >= h.s,
{
}

/// **A step the register has left behind is frozen.** Recording anything at any step
/// leaves the first value and the aggregate of every step below the current one as
/// they were.
pub proof fn theorem_a_step_left_behind_is_frozen(h: IsrHistory, s: nat, v: nat, x: nat)
    requires
        x < h.s,
    ensures
        hget(isr_record(h, s, v).a, x) == hget(h.a, x),
        hget(isr_record(h, s, v).f, x) == hget(h.f, x),
{
}

/// **An aggregate only grows.** After recording, the aggregate at any step is at
/// least what it was.
pub proof fn theorem_an_aggregate_never_shrinks(h: IsrHistory, s: nat, v: nat, x: nat)
    ensures
        hget(isr_record(h, s, v).a, x) >= hget(h.a, x),
{
}

/// **A value recorded at the current step is in its aggregate.** The aggregate is at
/// least the value, so the best value a recorder has been given at a step is never
/// missing from the aggregate it later reports for it.
pub proof fn theorem_a_recorded_value_is_in_the_aggregate(h: IsrHistory, s: nat, v: nat)
    requires
        s >= h.s,
    ensures
        hget(isr_record(h, s, v).a, s) >= v,
{
}

} // verus!
