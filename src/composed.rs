//! The two layers, composed.
//!
//! [`crate::raymond`] decides *where the token is*; [`crate::ownership`] decides
//! *who may mutate*. On their own, neither constrains the other: `couples` can be
//! stated over a `(Raymond, OwnershipState)` pair, but nothing stops a token
//! transfer from happening while the actor is still `Owned`, which would strand
//! mutable authority at a node that no longer holds the token.
//!
//! This module is what closes that gap. It defines a single state machine over
//! both layers in which the synchronisation is a **guard**, not an assumption:
//!
//! * [`ComposedStep::PassToken`] may only fire while the actor is *not* `Owned` -
//!   ownership has to be released before the token is allowed to move;
//! * [`ComposedStep::AcquireUnderToken`] may only fire for a node that *holds*
//!   the token - authority cannot be taken by a node the routing layer has not
//!   elected;
//! * [`ComposedStep::Own`] carries any ownership transition that does not create
//!   authority over this actor, and [`ComposedStep::Ray`] carries every Raymond
//!   step that does not move the token - request routing and critical-section
//!   bookkeeping alike.
//!
//! (The two carried-step fields are named apart because Verus only generates the
//! `->field` accessor when a field has one type across all variants.)
//!
//! `couples` is then an *invariant* of this machine rather than a side condition,
//! which is what makes "token transfer preserves ownership safety" a statement
//! about the system instead of a hypothetical.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::raymond::*;

verus! {

/// One actor, governed jointly by the ownership protocol and Raymond routing.
pub struct Composed {
    pub own: System,
    pub ray: Raymond,
    pub actor: ActorId,
}

/// `s` is an `Acquire` of actor `a`. This is the one ownership transition that
/// can *create* mutable authority, so the composed machine routes it through
/// [`ComposedStep::AcquireUnderToken`] instead of [`ComposedStep::Own`].
pub open spec fn is_acquire_of(s: Step, a: ActorId) -> bool {
    match s {
        Step::Acquire { actor, node: _ } => actor == a,
        _ => false,
    }
}

/// The composed invariant: both layers hold, and anybody with mutable authority
/// over the actor is the node currently holding the token.
pub open spec fn composed_inv(c: Composed) -> bool {
    &&& inv(c.own)
    &&& ray_inv(c.ray)
    &&& c.own.actors.contains_key(c.actor)
    &&& couples(c.ray, c.own.actors[c.actor])
}

/// Any Raymond step that does not move the token: request routing *and*
/// critical-section bookkeeping. None of them touch ownership.
///
/// The guard is `preserves_token`, not `is_routing_step`: the composed machine
/// has to admit `EnterCs` and `ExitCs` too, or no composed execution could ever
/// enter a critical section and the composed theorems would only cover states
/// where `using` is uniformly false.
pub open spec fn cs_ray(pre: Composed, post: Composed, s: RayStep) -> bool {
    &&& preserves_token(s)
    &&& ray_step(pre.ray, post.ray, s)
    &&& post.own == pre.own
    &&& post.actor == pre.actor
}

/// Any ownership transition that does not create authority over this actor.
pub open spec fn cs_own(pre: Composed, post: Composed, s: Step) -> bool {
    &&& !is_acquire_of(s, pre.actor)
    &&& step(pre.own, post.own, s)
    &&& post.ray == pre.ray
    &&& post.actor == pre.actor
}

/// The token moves - **only** once the actor has been released.
///
/// This guard is the whole point of the module: it is what turns the side
/// condition of `theorem_token_transfer_preserves_ownership_safety` into
/// something the machine enforces.
pub open spec fn cs_pass_token(pre: Composed, post: Composed, n: NodeId, head: NodeId) -> bool {
    &&& !is_owned(pre.own.actors[pre.actor])
    &&& ray_assign_privilege(pre.ray, post.ray, n, head)
    &&& post.own == pre.own
    &&& post.actor == pre.actor
}

/// A node takes ownership - **only** if it is the node holding the token.
pub open spec fn cs_acquire_under_token(pre: Composed, post: Composed, n: NodeId) -> bool {
    &&& has_token(pre.ray, n)
    &&& tr_acquire(pre.own, post.own, pre.actor, n)
    &&& post.ray == pre.ray
    &&& post.actor == pre.actor
}

/// The labelled transitions of the composed machine.
pub enum ComposedStep {
    Ray { ray_step: RayStep },
    Own { own_step: Step },
    PassToken { node: NodeId, head: NodeId },
    AcquireUnderToken { node: NodeId },
}

pub open spec fn composed_step(pre: Composed, post: Composed, s: ComposedStep) -> bool {
    match s {
        ComposedStep::Ray { ray_step } => cs_ray(pre, post, ray_step),
        ComposedStep::Own { own_step } => cs_own(pre, post, own_step),
        ComposedStep::PassToken { node, head } => cs_pass_token(pre, post, node, head),
        ComposedStep::AcquireUnderToken { node } => cs_acquire_under_token(pre, post, node),
    }
}

pub open spec fn composed_next(pre: Composed, post: Composed) -> bool {
    exists|s: ComposedStep| composed_step(pre, post, s)
}

/// Initial composed states: both layers start fresh, and the actor exists.
pub open spec fn composed_init(c: Composed) -> bool {
    &&& init(c.own)
    &&& (exists|root: NodeId| ray_init(c.ray, root))
    &&& c.own.actors.contains_key(c.actor)
}

/// `tr` is a finite execution of the composed machine.
pub open spec fn composed_valid_execution(tr: Seq<Composed>) -> bool {
    &&& tr.len() > 0
    &&& composed_init(tr[0])
    &&& (forall|i: int| 0 <= i < tr.len() - 1 ==> composed_next(#[trigger] tr[i], tr[i + 1]))
}

/// `c` is reachable in the composed machine.
pub open spec fn composed_reachable(c: Composed) -> bool {
    exists|tr: Seq<Composed>| composed_valid_execution(tr) && tr[tr.len() - 1] == c
}

} // verus!
