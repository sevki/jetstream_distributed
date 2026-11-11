//! **The interval summary register in constant space** (the paper's Algorithm 3),
//! verified to be the register of [`crate::quepaxa::isr_spec`] (Algorithm 2).
//!
//! The specified register keeps a first value and an aggregate for every step it
//! has ever seen. Only two steps' worth is ever read, so a recorder keeps four
//! integers: the current step `s`, the current step's first value `fc` and
//! aggregate `ac`, and the prior step's aggregate `ap`. [`Isr::record`] is the
//! whole of a recorder's behaviour.
//!
//! # What is verified
//!
//! For *any* history the constant-space register stands for, recording a value
//! leaves it standing for the history the specification would have produced, and
//! answers exactly what the specification answers. So a recorder cannot misreport
//! what it has been given, and the discarding of old steps loses nothing that a
//! reply depends on.
//!
//! The history is ghost: nothing in the register holds it. [`Isr::related`] is
//! the relation that says a register stands for a history.
//!
//! # What is not
//!
//! Values are `u128` here. The concrete protocol packs a proposal's priority,
//! proposer and value into one so that the larger integer is the better proposal;
//! that packing is the proposer's and is not in this file.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::quepaxa::isr_spec::*;

verus! {

/// A recorder's register: four integers.
#[derive(Clone, Copy)]
pub struct Isr {
    /// The current step.
    pub s: u64,
    /// The first value recorded at the current step.
    pub fc: u128,
    /// The aggregate (maximum) of the values recorded at the current step.
    pub ac: u128,
    /// The aggregate of the values recorded at the step before the current one.
    pub ap: u128,
}

impl Isr {
    /// This register stands for the history `h`: it holds exactly what the
    /// specification's replies read, and the history holds nothing above the
    /// current step (steps only ever advance, so nothing has been recorded there).
    pub open spec fn related(&self, h: IsrHistory) -> bool {
        &&& self.s as nat == h.s
        &&& self.fc as nat == hget(h.f, h.s)
        &&& self.ac as nat == hget(h.a, h.s)
        &&& self.ap as nat == (if h.s > 0 {
            hget(h.a, (h.s - 1) as nat)
        } else {
            0nat
        })
        &&& forall|x: nat| x > h.s ==> hget(h.f, x) == 0 && hget(h.a, x) == 0
    }

    /// This register stands for *some* history. What a service can know without
    /// carrying a ghost history around: a register made by [`Isr::new`] and only ever
    /// recorded into by [`Isr::record_now`] always does.
    pub open spec fn standing(&self) -> bool {
        exists|h: IsrHistory| self.related(h)
    }

    /// **Record `v` at step `s`, and answer**, for a caller that holds no ghost history.
    ///
    /// The register keeps standing for some history, and answers with its own current
    /// step, first value and prior aggregate. That the history it stands for is the one
    /// the specification produces, and that the answer is the specification's, is
    /// [`Isr::record`]'s contract, which this calls.
    pub fn record_now(&mut self, s: u64, v: u128) -> (reply: (u64, u128, u128))
        requires
            old(self).standing(),
        ensures
            final(self).standing(),
            reply == (final(self).s, final(self).fc, final(self).ap),
    {
        let ghost h = choose|h: IsrHistory| self.related(h);
        self.record(s, v, Ghost(h))
    }

    /// A register nothing has been recorded in.
    pub fn new() -> (r: Isr)
        ensures
            r.related(isr_empty()),
            r.standing(),
    {
        let r = Isr { s: 0, fc: 0, ac: 0, ap: 0 };
        proof {
            let h = isr_empty();
            assert forall|x: nat| x > h.s implies hget(h.f, x) == 0 && hget(h.a, x) == 0 by {
                assert(!h.f.dom().contains(x));
                assert(!h.a.dom().contains(x));
            }
        }
        r
    }

    /// **Record `v` at step `s`, and answer.** Returns the current step, its first
    /// value and the prior step's aggregate.
    ///
    /// `h` is the history this register stands for. The result stands for the history
    /// the specification would produce, and the answer is the specification's.
    pub fn record(&mut self, s: u64, v: u128, Ghost(h): Ghost<IsrHistory>) -> (reply: (u64, u128, u128))
        requires
            old(self).related(h),
        ensures
            final(self).related(isr_record(h, s as nat, v as nat)),
            (reply.0 as nat, reply.1 as nat, reply.2 as nat) == isr_reply(
                isr_record(h, s as nat, v as nat),
            ),
    {
        if s == self.s {
            // The current step: fold the value into the aggregate.
            if v > self.ac {
                self.ac = v;
            }
        } else if s > self.s {
            // A newer step. If it is the very next one, what was current is now prior;
            // if steps were skipped, nothing was recorded in the step before it.
            if s - self.s == 1 {
                self.ap = self.ac;
            } else {
                self.ap = 0;
            }
            self.s = s;
            self.fc = v;
            self.ac = v;
        }
        // An older step is obsolete and changes nothing.
        proof {
            let h1 = isr_record(h, s as nat, v as nat);
            if s as nat > h.s && s as nat != h.s + 1 {
                // Skipped steps: nothing was recorded at the step before `s`.
                assert(hget(h.a, (s - 1) as nat) == 0);
            }
            assert(h1.s == self.s as nat);
            assert forall|x: nat| x > h1.s implies hget(h1.f, x) == 0 && hget(h1.a, x) == 0 by {
                assert(hget(h.f, x) == 0 && hget(h.a, x) == 0);
            }
        }
        (self.s, self.fc, self.ap)
    }
}

} // verus!
