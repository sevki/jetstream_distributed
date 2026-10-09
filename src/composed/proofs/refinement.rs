//! The coupling guards agree with the composed model.
//!
//! The composed machine adds exactly one thing to the two layers it composes:
//! guards that tie a routing move to the ownership state. So the refinement
//! obligations here are the two layers' own (already discharged, in
//! `ownership::proofs::refinement` and `raymond::proofs::refinement`) plus the
//! coupling — and the bridging theorems that say a step the layers have already
//! proved correct is *carried* by the composed machine rather than needing a
//! second proof.
//!
//! # The couplings
//!
//! | Hypothesis | What supplies it |
//! | --- | --- |
//! | `actor_unowned == is_unowned(c.own.actors[c.actor])` | the registry's record, read under the same lock as the routing table |
//! | `privilege == c.ray.privilege` | the router's record of where the privilege is |
//! | `seized == c.seized.contains(n)` | the coordinator's set of nodes owing a reconciliation |
//! | `c.own.live.contains(n)` | **every node is live**: the service has no `Crash` step. See [`crate::composed::steps`] |
//!
//! The last one is the narrowest thing in the file and is stated rather than
//! dropped: the theorems below are about the composed machine's executions in
//! which no node crashes, which is the fragment a service that cannot evaluate
//! liveness can honestly claim.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::composed::model::*;
use crate::composed::steps::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::proofs::refinement::*;
use crate::ownership::spec::*;
use crate::ownership::steps::*;
use crate::raymond::model::*;
use crate::raymond::proofs::refinement::*;
use crate::raymond::steps::*;

verus! {

// ---------------------------------------------------------------------------
// The post-states, built explicitly
// ---------------------------------------------------------------------------

/// Where `PassToken` sends the composed machine: the routing layer's
/// assignment, ownership untouched, and the recipient's debt discharged —
/// receiving the privilege *is* learning the truth.
pub open spec fn pass_post(c: Composed, n: NodeId, head: NodeId) -> Composed {
    Composed {
        own: c.own,
        ray: assign_post(c.ray, n, head),
        actor: c.actor,
        seized: c.seized.remove(head),
    }
}

/// Where `ray_seize` sends the routing layer. **Only `to` acts**: nothing
/// belonging to the old holder is touched.
pub open spec fn seize_ray_post(r: Raymond, to: NodeId) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder.insert(to, to),
        queue: r.queue,
        asked: r.asked,
        using: r.using,
        requests: r.requests,
        privilege: to,
    }
}

/// Where `SeizeToken` sends the composed machine: `from` now owes a
/// reconciliation and `to` no longer does.
pub open spec fn seize_post(c: Composed, from: NodeId, to: NodeId) -> Composed {
    Composed {
        own: c.own,
        ray: seize_ray_post(c.ray, to),
        actor: c.actor,
        seized: c.seized.insert(from).remove(to),
    }
}

/// Where `ray_reconcile` sends the routing layer: the stale holder re-points at
/// the real one and leaves the critical section it thought it was in.
pub open spec fn reconcile_ray_post(r: Raymond, n: NodeId) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder.insert(n, r.privilege),
        queue: r.queue,
        asked: r.asked.insert(n, false),
        using: r.using.insert(n, false),
        requests: r.requests,
        privilege: r.privilege,
    }
}

/// Where `Reconcile` sends the composed machine.
pub open spec fn reconcile_post(c: Composed, n: NodeId) -> Composed {
    Composed {
        own: c.own,
        ray: reconcile_ray_post(c.ray, n),
        actor: c.actor,
        seized: c.seized.remove(n),
    }
}

/// Where `AcquireUnderToken` sends the composed machine: the ownership layer's
/// acquire, routing untouched.
pub open spec fn acquire_under_token_post(c: Composed, n: NodeId) -> Composed {
    Composed {
        own: acquire_post(c.own, c.actor, n),
        ray: c.ray,
        actor: c.actor,
        seized: c.seized,
    }
}

// ---------------------------------------------------------------------------
// PassToken
// ---------------------------------------------------------------------------

/// When the routing layer's own step fires and the actor has been released, the
/// composed machine passes the token — to exactly the state computed.
pub proof fn theorem_pass_token_step_refines(c: Composed, n: NodeId, head: NodeId)
    requires
        c.own.actors.contains_key(c.actor),
        c.own.live.contains(n),
        c.own.live.contains(head),
        ray_maps_total(c.ray),
        c.ray.nodes.contains(n),
        c.ray.queue[n].len() > 0,
        c.ray.queue[n][0] == head,
        assign_fires(
            n,
            c.ray.privilege,
            c.ray.holder[n],
            c.ray.using[n],
            c.ray.queue[n].len(),
            head,
            c.ray.nodes.contains(head),
        ),
        pass_token_fires(is_unowned(c.own.actors[c.actor])),
    ensures
        cs_pass_token(c, pass_post(c, n, head), n, head),
{
    theorem_assign_step_refines(c.ray, n, head);
}

/// **A privilege cannot move while the actor is held.** Whatever the routing
/// layer would have allowed, the composed machine does not.
pub proof fn theorem_pass_token_refuses_while_the_actor_is_held(
    c: Composed,
    post: Composed,
    n: NodeId,
    head: NodeId,
)
    requires
        c.own.actors.contains_key(c.actor),
        !pass_token_fires(is_unowned(c.own.actors[c.actor])),
    ensures
        !cs_pass_token(c, post, n, head),
{
}

/// And when the routing layer's own step refuses, so does the composition: the
/// coupling only ever narrows.
pub proof fn theorem_pass_token_refuses_when_the_routing_step_does(
    c: Composed,
    post: Composed,
    n: NodeId,
    head: NodeId,
)
    requires
        ray_maps_total(c.ray),
        c.ray.nodes.contains(n),
        c.ray.queue[n].len() > 0,
        c.ray.queue[n][0] == head,
        !assign_fires(
            n,
            c.ray.privilege,
            c.ray.holder[n],
            c.ray.using[n],
            c.ray.queue[n].len(),
            head,
            c.ray.nodes.contains(head),
        ),
    ensures
        !cs_pass_token(c, post, n, head),
{
    theorem_assign_step_refuses_exactly_when_disabled(c.ray, post.ray, n, head);
}

// ---------------------------------------------------------------------------
// SeizeToken
// ---------------------------------------------------------------------------

pub proof fn theorem_seize_step_refines(c: Composed, from: NodeId, to: NodeId)
    requires
        c.own.actors.contains_key(c.actor),
        c.own.live.contains(to),
        ray_wf(c.ray),
        seize_fires(
            is_unowned(c.own.actors[c.actor]),
            from,
            c.ray.privilege,
            to,
            c.ray.nodes.contains(to),
        ),
    ensures
        cs_seize_token(c, seize_post(c, from, to), from, to),
{
    assert(c.ray.nodes.contains(c.ray.privilege));
    assert(c.ray.nodes.contains(from));
}

pub proof fn theorem_seize_step_refuses_exactly_when_disabled(
    c: Composed,
    post: Composed,
    from: NodeId,
    to: NodeId,
)
    requires
        c.own.actors.contains_key(c.actor),
        !seize_fires(
            is_unowned(c.own.actors[c.actor]),
            from,
            c.ray.privilege,
            to,
            c.ray.nodes.contains(to),
        ),
    ensures
        !cs_seize_token(c, post, from, to),
{
}

// ---------------------------------------------------------------------------
// AcquireUnderToken
// ---------------------------------------------------------------------------

/// When the ownership layer's own acquire fires and the node holds the
/// privilege, the composed machine acquires — to exactly the state computed.
pub proof fn theorem_acquire_under_token_step_refines(
    c: Composed,
    n: NodeId,
    e: Epoch,
    granted: bool,
)
    requires
        c.own.actors.contains_key(c.actor),
        c.own.live.contains(n),
        granted == c.own.network.contains(Message::Grant { actor: c.actor, to: n, epoch: e }),
        acquire_fires(c.own.actors[c.actor], n, e, granted),
        c.ray.nodes.contains(n),
        acquire_under_token_fires(c.ray.privilege, n),
    ensures
        cs_acquire_under_token(c, acquire_under_token_post(c, n), n),
{
    theorem_acquire_step_refines_tr_acquire(c.own, c.actor, n, e, granted);
}

/// **Authority cannot be taken by a node the routing layer has not elected.**
pub proof fn theorem_acquire_under_token_refuses_a_node_without_the_privilege(
    c: Composed,
    post: Composed,
    n: NodeId,
)
    requires
        !acquire_under_token_fires(c.ray.privilege, n),
    ensures
        !cs_acquire_under_token(c, post, n),
{
}

// ---------------------------------------------------------------------------
// Reconcile
// ---------------------------------------------------------------------------

pub proof fn theorem_reconcile_step_refines(c: Composed, n: NodeId)
    requires
        ray_maps_total(c.ray),
        c.ray.nodes.contains(n),
        reconcile_fires(c.seized.contains(n), c.ray.holder[n] == n, c.ray.privilege == n),
    ensures
        cs_reconcile(c, reconcile_post(c, n), n),
{
}

pub proof fn theorem_reconcile_step_refuses_exactly_when_disabled(
    c: Composed,
    post: Composed,
    n: NodeId,
)
    requires
        ray_maps_total(c.ray),
        c.ray.nodes.contains(n),
        !reconcile_fires(c.seized.contains(n), c.ray.holder[n] == n, c.ray.privilege == n),
    ensures
        !cs_reconcile(c, post, n),
{
}

// ---------------------------------------------------------------------------
// The steps the layers already proved
// ---------------------------------------------------------------------------

/// **A routing step the Raymond layer proved is carried by the composed
/// machine.** `cs_ray` adds only that the step does not move the privilege and
/// that the acting node is live; nothing about ownership is read or changed.
pub proof fn theorem_a_routing_step_is_carried(c: Composed, post_ray: Raymond, s: RayStep)
    requires
        preserves_token(s),
        c.own.live.contains(ray_step_actor(s)),
        ray_step(c.ray, post_ray, s),
    ensures
        cs_ray(
            c,
            Composed { own: c.own, ray: post_ray, actor: c.actor, seized: c.seized },
            s,
        ),
{
}

/// **An ownership step the ownership layer proved is carried by the composed
/// machine**, unless it is the one that would create authority over this actor
/// (which has to go through `AcquireUnderToken`) or would bring back a node
/// that owes a reconciliation.
pub proof fn theorem_an_ownership_step_is_carried(c: Composed, post_own: System, s: Step)
    requires
        !is_acquire_of(s, c.actor),
        !recovers_a_seized_node(c, s),
        step(c.own, post_own, s),
    ensures
        cs_own(
            c,
            Composed { own: post_own, ray: c.ray, actor: c.actor, seized: c.seized },
            s,
        ),
{
}

} // verus!
