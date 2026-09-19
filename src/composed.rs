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
//! * [`ComposedStep::PassToken`] may only fire while the actor is `Unowned` -
//!   the release has to have *completed* before the token is allowed to move
//!   (`Transferring` is not enough: it satisfies `!is_owned`, but the outgoing
//!   owner has not acknowledged the revoke yet);
//! * [`ComposedStep::SeizeToken`] moves the token *without* the holder acting,
//!   under the same guard, so that crash-driven takeover - the case epochs
//!   exist for - is reachable rather than requiring a dead node to cooperate;
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

/// The token moves - **only** once the actor has actually been released.
///
/// This guard is the whole point of the module: it is what turns the side
/// condition of `theorem_token_transfer_preserves_ownership_safety` into
/// something the machine enforces.
///
/// The guard is `is_unowned`, not merely `!is_owned`: `Transferring` also
/// satisfies `!is_owned`, so the weaker form would let the token move while a
/// handover was still in flight and the outgoing owner had not yet
/// acknowledged the revoke. Safety would survive that - nobody has authority
/// while `Transferring` either - but it would not be the
/// release-before-transfer discipline this module claims to enforce.
pub open spec fn cs_pass_token(pre: Composed, post: Composed, n: NodeId, head: NodeId) -> bool {
    &&& is_unowned(pre.own.actors[pre.actor])
    &&& ray_assign_privilege(pre.ray, post.ray, n, head)
    &&& post.own == pre.own
    &&& post.actor == pre.actor
}

/// The token is **seized** and re-established at `to`, without the node that
/// holds it acting.
///
/// This is the step that makes crash-driven takeover expressible. Without it
/// the only way the token can move is [`ComposedStep::PassToken`], which
/// requires `has_token(pre.ray, from)` *and* models `from` voluntarily passing
/// the privilege on. So after `RevokeOwner` fires against a crashed owner `A` -
/// leaving the actor `Unowned` at the next epoch and offered to `B` - the only
/// composed continuation was `A`, a node the ownership layer has marked dead,
/// taking a routing step. That is precisely the cooperation epochs and fencing
/// exist to make unnecessary, so a composed machine that required it was
/// proving something narrower than it appeared to: agreement along executions
/// where the token always moves *voluntarily*.
///
/// The first guard is the same `is_unowned` as [`cs_pass_token`], and for the
/// same reason: in `Unowned` nobody has authority at all, so moving the token
/// cannot strand it. Seizure is safe for exactly the reason revocation is - the
/// epoch was burned first.
///
/// The second guard, `!pre.own.live.contains(from)`, is **not** decoration, and
/// `is_unowned` alone is not enough. `RevokeOwner` may fire against a perfectly
/// healthy owner - unreliable detection is modelled on purpose - so without a
/// liveness check a seizure could fire against a live node that is inside its
/// Raymond critical section. `ray_seize` clears `using[from]`, so the model
/// would then report exclusivity while two nodes were really inside: the
/// invariant would be preserved by *erasing* the first node's execution rather
/// than by anything the protocol does.
///
/// The asymmetry is the point. Revoking the *ownership record* is safe against
/// a healthy node because the epoch fences it. Seizing the *token* is not,
/// because Raymond's critical section has no epoch - there is nothing to fence
/// a node that believes it still holds the privilege. So seizure is restricted
/// to fail-stopped nodes, where clearing `using` is a fact about the world
/// rather than a convenience: a crashed node is not executing anything.
pub open spec fn cs_seize_token(pre: Composed, post: Composed, from: NodeId, to: NodeId) -> bool {
    &&& is_unowned(pre.own.actors[pre.actor])
    &&& !pre.own.live.contains(from)
    &&& ray_seize(pre.ray, post.ray, from, to)
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
    SeizeToken { from: NodeId, to: NodeId },
    AcquireUnderToken { node: NodeId },
}

pub open spec fn composed_step(pre: Composed, post: Composed, s: ComposedStep) -> bool {
    match s {
        ComposedStep::Ray { ray_step } => cs_ray(pre, post, ray_step),
        ComposedStep::Own { own_step } => cs_own(pre, post, own_step),
        ComposedStep::PassToken { node, head } => cs_pass_token(pre, post, node, head),
        ComposedStep::SeizeToken { from, to } => cs_seize_token(pre, post, from, to),
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
    // Multi-trigger on both adjacent states, for the reason documented on
    // `crate::model::valid_execution`.
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> composed_next(tr[i], tr[i + 1]))
}

/// `c` is reachable in the composed machine.
pub open spec fn composed_reachable(c: Composed) -> bool {
    exists|tr: Seq<Composed>| composed_valid_execution(tr) && tr[tr.len() - 1] == c
}

} // verus!
