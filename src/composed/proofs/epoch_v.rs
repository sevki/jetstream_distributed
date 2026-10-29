//! **The actor's epoch survives composition.**
//!
//! This was stated in `ownership::proofs::properties`, next to the ownership
//! protocol's own epoch theorems, which made the ownership protocol's proofs import
//! the composed machine (and Raymond) for the one theorem whose subject is not
//! ownership. It lives with its subject now, and `ownership` imports nothing of the
//! layers built on top of it.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::composed::model::*;
use crate::id::Id;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::ownership::transfer::*;

verus! {

/// **Epoch monotonicity survives composition.** No composed transition - not
/// routing, not a token transfer, not an acquisition - decreases the actor's
/// epoch.
pub proof fn theorem_composed_epoch_monotone(pre: Composed, post: Composed, s: ComposedStep)
    requires
        composed_step(pre, post, s),
        pre.own.actors.contains_key(pre.actor),
    ensures
        post.own.actors.contains_key(post.actor),
        current_epoch(post.own.actors[post.actor]) >= current_epoch(pre.own.actors[pre.actor]),
{
    match s {
        ComposedStep::Ray { ray_step } => {},
        ComposedStep::PassToken { node, head } => {},
        // A seizure rewrites routing state only; `own` is untouched.
        ComposedStep::SeizeToken { from, to } => {},
        // Reconciliation touches only the seizure marker.
        ComposedStep::Reconcile { node } => {},
        ComposedStep::Own { own_step } => {
            lemma_step_epoch_monotone(pre.own, post.own, own_step, pre.actor);
        },
        ComposedStep::AcquireUnderToken { node } => {
            let acq = Step::Acquire { actor: pre.actor, node: node };
            assert(step(pre.own, post.own, acq));
            lemma_step_epoch_monotone(pre.own, post.own, acq, pre.actor);
        },
    }
}

} // verus!
