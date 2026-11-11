//! **The interval summary register**, as the paper specifies it (Algorithm 2).
//!
//! QuePaxa's recorders are passive: each keeps one small register and answers
//! proposers' requests by reading and updating it. The register accepts a
//! succession of values, each tagged with a logical-clock *step*, and in answer
//! to each returns a short summary of what it has been given in the current and the
//! immediately preceding step.
//!
//! This file is the *specification*: the register as if it kept its whole history,
//! one entry per step ever seen. The paper observes that only the current and the
//! prior step's entries are ever read, so a real register needs constant space
//! ([`crate::quepaxa::isr`], the paper's Algorithm 3), and it is that constant-space
//! register that is verified against this one.
//!
//! # The register
//!
//! * `S`, the current step, starting at 0 and never decreasing;
//! * `F[s]`, the **first** value recorded at step `s`;
//! * `A[s]`, the **aggregate** of every value recorded at step `s` while `s` was
//!   the current step.
//!
//! A value for a step *above* `S` advances the register: `S` becomes that step and
//! the value is the new first value. A value for the *current* step is folded into
//! its aggregate. A value for an *older* step is obsolete and dropped. Whatever
//! happened, the reply is the current step, its first value, and the aggregate of
//! the step before it.
//!
//! The aggregate here is `max`, over naturals with `0` as "nothing recorded"
//! (the paper's `nil`), which is what QuePaxa needs: proposals are encoded so that
//! the highest integer is the best proposal.
#![allow(unused_imports)]

use vstd::prelude::*;

verus! {

/// The larger of two naturals: the register's aggregation.
pub open spec fn agg(a: nat, b: nat) -> nat {
    if a >= b {
        a
    } else {
        b
    }
}

/// What a map holds at `k`, or `0` (nothing recorded) if it holds nothing.
pub open spec fn hget(m: Map<nat, nat>, k: nat) -> nat {
    if m.dom().contains(k) {
        m[k]
    } else {
        0
    }
}

/// The register with its whole history.
pub struct IsrHistory {
    /// The current step.
    pub s: nat,
    /// The first value recorded at each step.
    pub f: Map<nat, nat>,
    /// The aggregate of the values recorded at each step.
    pub a: Map<nat, nat>,
}

/// A register nothing has been recorded in.
pub open spec fn isr_empty() -> IsrHistory {
    IsrHistory { s: 0, f: Map::empty(), a: Map::empty() }
}

/// A value for a step above the current one advances the register to it, and is the
/// first value of that step.
pub open spec fn isr_advance(h: IsrHistory, s: nat, v: nat) -> IsrHistory {
    if s > h.s {
        IsrHistory { s, f: h.f.insert(s, v), a: h.a }
    } else {
        h
    }
}

/// A value for the current step is folded into that step's aggregate.
pub open spec fn isr_aggregate(h: IsrHistory, s: nat, v: nat) -> IsrHistory {
    if s == h.s {
        IsrHistory { a: h.a.insert(s, agg(hget(h.a, s), v)), ..h }
    } else {
        h
    }
}

/// **Record `v` at step `s`**: advance if the step is new, then aggregate if it is
/// current. A value for an older step does nothing.
pub open spec fn isr_record(h: IsrHistory, s: nat, v: nat) -> IsrHistory {
    isr_aggregate(isr_advance(h, s, v), s, v)
}

/// What the register answers: the current step, that step's first value, and the
/// aggregate of the step before it (`0` at step `0`, which has none).
pub open spec fn isr_reply(h: IsrHistory) -> (nat, nat, nat) {
    (h.s, hget(h.f, h.s), if h.s > 0 {
        hget(h.a, (h.s - 1) as nat)
    } else {
        0
    })
}

} // verus!
