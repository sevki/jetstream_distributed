//! Composing two protocols.
//!
//! [`crate::composed`] joins ownership and Raymond by hand: a state with both and
//! a few extras, a step type with a variant per way the two may move, and a
//! guard on each. Every pairing the book's map lists as not built (Raft with
//! ownership, the mailbox with `Host`, membership with placement) would be
//! another module written the same way. This file is the shape they share.
//!
//! A **composition** of protocols `A` and `B` is a [`Product`] under a
//! [`Coupling`]. Its state is both parts' states and whatever the coupling keeps
//! for itself (the *glue*). It has three kinds of step:
//!
//! * `A` moves alone, if the coupling allows it in the current state;
//! * `B` moves alone, likewise;
//! * a **joint** step, defined entirely by the coupling, for the moves that
//!   belong to neither part. Seizing the privilege is one: it edits Raymond's
//!   state without being a Raymond step, because no node of Raymond's takes it.
//!
//! The coupling is where the two protocols meet, and it is the *only* place: a
//! guard on a part's step may read the other part and the glue, and the glue may
//! change when a part moves, but a part never moves the other. That is why "the
//! coupling is a guard, not an assumption" is a property of the type and not a
//! habit of whoever wrote the model.
//!
//! This file is **trusted**, like a model: it defines shapes and states the
//! obligations a safe coupling owes, and proves nothing. [`crate::compose_safety`]
//! proves what follows from meeting them.
//!
//! # What it does not have
//!
//! * **No liveness.** Safety composes by the argument in [`Safe`]; fairness does
//!   not, and each composition that wants a liveness theorem states its own.
//! * **No services.** This is the machine, not the code that runs it. How a
//!   composed *service* is assembled from two services is a separate question
//!   (the `#[service]` macro takes a trait, not a pair of them).
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::protocol::Protocol;

verus! {

/// A protocol with an invariant it keeps.
///
/// The obligations are the usual two, and an implementation is a proof of them:
/// every initial state satisfies `inv`, and no step leaves it.
pub trait Safe: Protocol {
    spec fn inv(s: Self::State) -> bool;

    proof fn init_establishes_inv(cfg: Self::Config, s: Self::State)
        requires
            Self::init(cfg, s),
        ensures
            Self::inv(s),
    ;

    proof fn step_preserves_inv(pre: Self::State, post: Self::State, label: Self::Step)
        requires
            Self::inv(pre),
            Self::step(pre, post, label),
        ensures
            Self::inv(post),
    ;
}

/// The state of a composition: the two parts', and the coupling's own.
pub struct Prod<SA, SB, G> {
    pub a: SA,
    pub b: SB,
    pub g: G,
}

/// A step of a composition. The three fields are named apart because Verus only
/// generates a `->field` accessor for a field with one type across all variants.
pub enum ProdStep<LA, LB, LC> {
    /// `A` moves alone.
    Left { la: LA },
    /// `B` moves alone.
    Right { lb: LB },
    /// A step that belongs to neither: the coupling's own.
    Joint { lc: LC },
}

/// How two protocols meet.
pub trait Coupling<A: Protocol, B: Protocol> {
    /// What the coupling keeps for itself. `()` if it keeps nothing.
    type Glue;
    /// The labels of the joint steps.
    type Joint;

    /// What the coupling requires of an initial state, beyond each part being
    /// initial.
    spec fn init(s: Prod<A::State, B::State, Self::Glue>) -> bool;

    /// `A` may take `la` in `s`. A guard: it may read all of `s`.
    spec fn allow_a(s: Prod<A::State, B::State, Self::Glue>, la: A::Step) -> bool;

    /// `B` may take `lb` in `s`.
    spec fn allow_b(s: Prod<A::State, B::State, Self::Glue>, lb: B::Step) -> bool;

    /// The glue after `A` takes `la` in `s`.
    spec fn glue_after_a(s: Prod<A::State, B::State, Self::Glue>, la: A::Step) -> Self::Glue;

    /// The glue after `B` takes `lb` in `s`.
    spec fn glue_after_b(s: Prod<A::State, B::State, Self::Glue>, lb: B::Step) -> Self::Glue;

    /// `lc` takes `pre` to `post`. May change any of the three.
    spec fn joint(
        pre: Prod<A::State, B::State, Self::Glue>,
        post: Prod<A::State, B::State, Self::Glue>,
        lc: Self::Joint,
    ) -> bool;
}

/// `A` and `B` under the coupling `K`, as a protocol.
pub struct Product<A, B, K>(core::marker::PhantomData<(A, B, K)>);

impl<A: Protocol, B: Protocol, K: Coupling<A, B>> Protocol for Product<A, B, K> {
    type Config = (A::Config, B::Config);
    type State = Prod<A::State, B::State, K::Glue>;
    type Step = ProdStep<A::Step, B::Step, K::Joint>;

    open spec fn init(cfg: (A::Config, B::Config), s: Self::State) -> bool {
        &&& A::init(cfg.0, s.a)
        &&& B::init(cfg.1, s.b)
        &&& K::init(s)
    }

    open spec fn step(pre: Self::State, post: Self::State, label: Self::Step) -> bool {
        match label {
            ProdStep::Left { la } => {
                &&& A::step(pre.a, post.a, la)
                &&& K::allow_a(pre, la)
                &&& post.b == pre.b
                &&& post.g == K::glue_after_a(pre, la)
            },
            ProdStep::Right { lb } => {
                &&& B::step(pre.b, post.b, lb)
                &&& K::allow_b(pre, lb)
                &&& post.a == pre.a
                &&& post.g == K::glue_after_b(pre, lb)
            },
            ProdStep::Joint { lc } => K::joint(pre, post, lc),
        }
    }
}

/// A coupling between two safe protocols, with the invariant it adds.
///
/// The product's invariant is `A::inv /\ B::inv /\ coupled`, and `coupled` is the
/// only thing a coupling has to supply and prove. What it may assume is the two
/// parts' invariants in the pre-state, which is what makes the obligation
/// small: it never re-proves a part's own safety.
///
/// A joint step is the exception, because by definition neither part's own steps
/// account for it. For those, the coupling also owes each part's invariant in the
/// post-state.
pub trait SafeCoupling<A: Safe, B: Safe>: Coupling<A, B> + Sized {
    spec fn coupled(s: Prod<A::State, B::State, Self::Glue>) -> bool;

    proof fn coupled_at_init(
        cfg: (A::Config, B::Config),
        s: Prod<A::State, B::State, Self::Glue>,
    )
        requires
            Product::<A, B, Self>::init(cfg, s),
        ensures
            Self::coupled(s),
    ;

    proof fn coupled_after(
        pre: Prod<A::State, B::State, Self::Glue>,
        post: Prod<A::State, B::State, Self::Glue>,
        label: ProdStep<A::Step, B::Step, Self::Joint>,
    )
        requires
            A::inv(pre.a),
            B::inv(pre.b),
            Self::coupled(pre),
            Product::<A, B, Self>::step(pre, post, label),
        ensures
            Self::coupled(post),
            label is Joint ==> A::inv(post.a) && B::inv(post.b),
    ;
}

} // verus!
