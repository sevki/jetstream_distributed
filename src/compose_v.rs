//! **Safety composes.** A product of safe protocols under a safe coupling is a safe
//! protocol, and its invariant is the parts' invariants and the coupling's.
//!
//! This is the whole argument for why a composition needs only its coupling
//! proved. A part's step preserves that part's invariant (its own theorem, used as
//! it is) and leaves the other part untouched (the product's frame), so the only
//! new fact is that the coupling is preserved, and for a step that belongs to
//! neither part, that the parts' invariants survive it.
//!
//! The conclusion is itself a [`Safe`] protocol, so a product is a part of a
//! larger one with no further work.
//!
//! What this does not say: that the coupling is *right*. The coupling's guards are
//! what the composition means, and a coupling too strong to be useful is safe
//! vacuously. [`crate::composed`] has scenarios for that; this file has none.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::compose::*;
use crate::protocol::Protocol;

verus! {

impl<A: Safe, B: Safe, K: SafeCoupling<A, B>> Safe for Product<A, B, K> {
    open spec fn inv(s: Prod<A::State, B::State, K::Glue>) -> bool {
        &&& A::inv(s.a)
        &&& B::inv(s.b)
        &&& K::coupled(s)
    }

    proof fn init_establishes_inv(cfg: (A::Config, B::Config), s: Prod<A::State, B::State, K::Glue>) {
        A::init_establishes_inv(cfg.0, s.a);
        B::init_establishes_inv(cfg.1, s.b);
        K::coupled_at_init(cfg, s);
    }

    proof fn step_preserves_inv(
        pre: Prod<A::State, B::State, K::Glue>,
        post: Prod<A::State, B::State, K::Glue>,
        label: ProdStep<A::Step, B::Step, K::Joint>,
    ) {
        K::coupled_after(pre, post, label);
        match label {
            ProdStep::Left { la } => {
                A::step_preserves_inv(pre.a, post.a, la);
            },
            ProdStep::Right { lb } => {
                B::step_preserves_inv(pre.b, post.b, lb);
            },
            ProdStep::Joint { lc } => {},
        }
    }
}

/// **Initial states of a safe composition are safe**: each part's invariant, and the
/// coupling's.
pub proof fn theorem_a_composition_starts_safe<A: Safe, B: Safe, K: SafeCoupling<A, B>>(
    cfg: (A::Config, B::Config),
    s: Prod<A::State, B::State, K::Glue>,
)
    requires
        Product::<A, B, K>::init(cfg, s),
    ensures
        A::inv(s.a),
        B::inv(s.b),
        K::coupled(s),
{
    Product::<A, B, K>::init_establishes_inv(cfg, s);
}

/// **A step of a safe composition keeps it safe.** Whichever kind of step it is, the
/// post-state satisfies both parts' invariants and the coupling.
pub proof fn theorem_a_composition_stays_safe<A: Safe, B: Safe, K: SafeCoupling<A, B>>(
    pre: Prod<A::State, B::State, K::Glue>,
    post: Prod<A::State, B::State, K::Glue>,
    label: ProdStep<A::Step, B::Step, K::Joint>,
)
    requires
        A::inv(pre.a),
        B::inv(pre.b),
        K::coupled(pre),
        Product::<A, B, K>::step(pre, post, label),
    ensures
        A::inv(post.a),
        B::inv(post.b),
        K::coupled(post),
{
    Product::<A, B, K>::step_preserves_inv(pre, post, label);
}

} // verus!
