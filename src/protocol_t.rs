//! What a protocol is, for the purposes of this crate.
//!
//! Every model here is the same thing wearing a different name: a state space, a
//! label for each kind of step, an initial predicate, and a transition relation
//! that says which labelled steps are allowed. Each used its own spelling
//! (`init`/`next`, `raft_init`/`raft_next`, `ray_init`/`ray_next`, ...), so nothing
//! in the types said what a protocol *is*, and anything stated about "a protocol"
//! had to be stated seven times. [`Protocol`] is that shape, written once.
//!
//! This file is **trusted**, like a model: it defines no behaviour, only the shape
//! a model must fill in. A model's instance of it is a statement about the model,
//! and [`crate::protocol_agreement`] proves that the instance says what the model
//! already said, so that instantiating this trait changes no theorem's meaning.
//!
//! # What it deliberately does not have
//!
//! * **No observable view.** Properties a *consumer* may rely on (a membership
//!   protocol's peers, a log's committed prefix) need a view of the state, but a
//!   view is only worth defining against the property that reads it, and none
//!   exists yet. It arrives with the first consumer, the membership contract.
//! * **No fairness.** Liveness is stated per protocol, against [`runs_of`], with
//!   the fairness assumption written out where it is used ([`crate::temporal`]).
//! * **No `next` to override.** `next` is `exists` a step. A protocol whose
//!   transition relation was not of that form would not be a labelled-step
//!   machine, and should say so rather than sneak in a different `next`.
#![allow(unused_imports)]

use vstd::prelude::*;

verus! {

/// A labelled-step state machine.
///
/// `Config` is whatever is fixed before a run starts and is not part of the state
/// (Raymond's root; `()` for the machines whose `init` is a predicate on the
/// state alone). `Step` is the label of one kind of transition, carrying its
/// arguments, so `step(pre, post, l)` reads "`l` takes `pre` to `post`".
pub trait Protocol {
    type Config;
    type State;
    type Step;

    /// The initial states of a run configured with `cfg`.
    spec fn init(cfg: Self::Config, s: Self::State) -> bool;

    /// `label` is an allowed step from `pre` to `post`.
    spec fn step(pre: Self::State, post: Self::State, label: Self::Step) -> bool;

    /// Some allowed step takes `pre` to `post`. Not overridable in spirit: see the
    /// module docs.
    open spec fn next(pre: Self::State, post: Self::State) -> bool {
        exists|label: Self::Step| #[trigger] Self::step(pre, post, label)
    }
}

/// `ex` is an infinite execution of `P` configured with `cfg`: it starts in an
/// initial state and every consecutive pair is a step.
///
/// This is [`crate::temporal::runs`] at `P`'s `init` and `next`, which is what
/// the liveness proofs are stated against.
pub open spec fn runs_of<P: Protocol>(cfg: P::Config, ex: spec_fn(nat) -> P::State) -> bool {
    crate::temporal::runs(ex, |s: P::State| P::init(cfg, s), |a: P::State, b: P::State| P::next(a, b))
}

} // verus!
