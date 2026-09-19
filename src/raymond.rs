//! Raymond's distributed mutual-exclusion algorithm, as a *routing* layer.
//!
//! This module is deliberately independent of [`crate::ownership`]: Raymond
//! decides **where the token is and how requests find it**, not **who is
//! allowed to mutate**. The two are glued together by the `couples` predicate
//! at the bottom of this file, and the glue is what makes it impossible for a
//! routing decision to manufacture authority.
//!
//! State per node:
//!
//! * `holder[n]` - the next hop towards the token. `holder[n] == n` means `n`
//!   currently possesses the token.
//! * `queue[n]`  - the request queue: nodes (or `n` itself) waiting behind `n`.
//! * `asked[n]`  - whether `n` has an outstanding request towards `holder[n]`.
//! * `using[n]`  - whether `n` is inside the critical section.
//!
//! Requests travel hop-by-hop towards the token and the token travels back
//! along the reverse of the request path:
//!
//! ```text
//! request:  D -> B -> A -> C[token]
//! token:    C -> A -> B -> D
//! ```
//!
//! Requests in flight are explicit state: `Raymond::requests` records every
//! request ever sent, never shrinks, and is not consumed by delivery. A request
//! is therefore deliverable zero, one or many times, in any order, and at any
//! later point - including after the token has moved and the holder pointers it
//! was routed against are gone.
//!
//! Only **safety** is modelled. Raymond's liveness (every request is eventually
//! served) requires FIFO, reliable links and no crashes, none of which this
//! model assumes; see `README.md`.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;

verus! {

/// The routing state of the whole cluster.
pub struct Raymond {
    pub nodes: Set<NodeId>,
    pub holder: Map<NodeId, NodeId>,
    pub queue: Map<NodeId, Seq<NodeId>>,
    pub asked: Map<NodeId, bool>,
    pub using: Map<NodeId, bool>,
    /// Every request ever sent, as `(originator, destination)`.
    ///
    /// Like `System::network` in the ownership layer this set never shrinks and
    /// delivery does not consume, so a request stays deliverable for ever, any
    /// number of times, in any order - **including long after the holder
    /// pointers it was routed against have changed**. Recording the destination
    /// at send time is what makes that last case expressible: a guard phrased
    /// against the *current* `holder[from]` would silently drop an in-flight
    /// request the moment the token moved.
    pub requests: Set<(NodeId, NodeId)>,
}

/// `n` currently possesses the token.
pub open spec fn has_token(r: Raymond, n: NodeId) -> bool {
    r.nodes.contains(n) && r.holder.contains_key(n) && r.holder[n] == n
}

/// Every node has an entry in every per-node map.
pub open spec fn ray_maps_total(r: Raymond) -> bool {
    forall|n: NodeId|
        #[trigger] r.nodes.contains(n) ==> r.holder.contains_key(n) && r.queue.contains_key(n)
            && r.asked.contains_key(n) && r.using.contains_key(n)
}

/// Every holder pointer points at a real node.
///
/// This clause used to sit inside `ray_maps_total`, under the same
/// `r.nodes.contains(n)` trigger, and that combination was a **matching loop**:
/// instantiating the quantifier at `n` produced the term
/// `r.nodes.contains(r.holder[n])`, which matched the trigger again at
/// `r.holder[n]`, producing `r.nodes.contains(r.holder[r.holder[n]])`, without
/// bound. `verus --profile` measured 171,941 instantiations of that one
/// quantifier - 40% of 419,801 in a single proof - which is what pushed
/// `routing_one_hop` past the solver's resource limit.
///
/// Triggering on `r.holder[n]` instead breaks the loop: the quantifier fires
/// only for holder pointers that some term already mentions, and its conclusion
/// is a `nodes.contains` fact, which creates no new `holder[_]` term to fire it
/// again.
pub open spec fn ray_holder_closed(r: Raymond) -> bool {
    forall|n: NodeId| r.nodes.contains(n) ==> r.nodes.contains(#[trigger] r.holder[n])
}

/// Every node has an entry in every map, and every holder pointer points at a
/// real node.
pub open spec fn ray_wf(r: Raymond) -> bool {
    &&& ray_maps_total(r)
    &&& ray_holder_closed(r)
}

/// **At most one valid token.**
pub open spec fn ray_unique_token(r: Raymond) -> bool {
    forall|n: NodeId, m: NodeId|
        #![trigger has_token(r, n), has_token(r, m)]
        has_token(r, n) && has_token(r, m) ==> n == m
}

/// **The token exists somewhere.**
///
/// `ray_unique_token` alone only rules out a *second* root; on its own it
/// admits states where every holder pointer sits in a non-root cycle and nobody
/// has the token. Carrying existence in the invariant is what makes the claim
/// "exactly one token" rather than "at most one", and it is what lets every
/// theorem parameterised by `ray_inv` rely on a root being there.
pub open spec fn ray_token_exists(r: Raymond) -> bool {
    exists|n: NodeId| #[trigger] has_token(r, n)
}

/// Only the token holder can be inside the critical section.
pub open spec fn ray_using_implies_token(r: Raymond) -> bool {
    forall|n: NodeId| #[trigger] r.nodes.contains(n) && r.using[n] ==> has_token(r, n)
}

/// The Raymond safety invariant.
pub open spec fn ray_inv(r: Raymond) -> bool {
    &&& ray_wf(r)
    &&& ray_unique_token(r)
    &&& ray_token_exists(r)
    &&& ray_using_implies_token(r)
}

// ---------------------------------------------------------------------------
// Transitions
// ---------------------------------------------------------------------------

/// `n` wants the token: it appends itself to its own queue.
pub open spec fn ray_request_cs(pre: Raymond, post: Raymond, n: NodeId) -> bool {
    &&& pre.nodes.contains(n)
    &&& post.queue == pre.queue.insert(n, pre.queue[n].push(n))
    &&& post.holder == pre.holder
    &&& post.asked == pre.asked
    &&& post.using == pre.using
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

/// `n` forwards a request one hop towards the token.
///
/// The destination is resolved *here*, at send time, and recorded in
/// `requests`. Everything after this point is the network's business.
pub open spec fn ray_make_request(pre: Raymond, post: Raymond, n: NodeId) -> bool {
    &&& pre.nodes.contains(n)
    &&& pre.holder[n] != n
    &&& pre.queue[n].len() > 0
    &&& !pre.asked[n]
    &&& post.asked == pre.asked.insert(n, true)
    &&& post.requests == pre.requests.insert((n, pre.holder[n]))
    &&& post.holder == pre.holder
    &&& post.queue == pre.queue
    &&& post.using == pre.using
    &&& post.nodes == pre.nodes
}

/// `at` receives a request that `from` sent to it at some earlier point.
///
/// The guard is the *sent message*, not the live routing topology, so
/// **duplicated, reordered and arbitrarily delayed requests are all permitted**:
/// this step may fire any number of times for the same `(at, from)` pair, in any
/// order, and - crucially - at any later point, including after the token has
/// moved and `from`'s holder pointer no longer points at `at`. All that happens
/// is that `at`'s queue picks up extra entries, which costs fairness, not
/// safety.
pub open spec fn ray_receive_request(pre: Raymond, post: Raymond, at: NodeId, from: NodeId) -> bool {
    &&& pre.nodes.contains(at)
    &&& pre.nodes.contains(from)
    &&& pre.requests.contains((from, at))
    &&& post.queue == pre.queue.insert(at, pre.queue[at].push(from))
    &&& post.holder == pre.holder
    &&& post.asked == pre.asked
    &&& post.using == pre.using
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

/// The token holder hands the token to the head of its queue.
///
/// This is the only transition that moves the token. It flips exactly two
/// holder pointers: `holder[n] := head` and `holder[head] := head`.
pub open spec fn ray_assign_privilege(
    pre: Raymond,
    post: Raymond,
    n: NodeId,
    head: NodeId,
) -> bool {
    &&& has_token(pre, n)
    &&& !pre.using[n]
    &&& pre.queue[n].len() > 0
    &&& pre.queue[n][0] == head
    &&& head != n
    &&& pre.nodes.contains(head)
    &&& post.holder == pre.holder.insert(n, head).insert(head, head)
    &&& post.queue == pre.queue.insert(n, pre.queue[n].drop_first())
    &&& post.asked == pre.asked.insert(n, false)
    &&& post.using == pre.using
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

/// The token holder is itself at the head of its queue, so it enters the
/// critical section.
pub open spec fn ray_enter_cs(pre: Raymond, post: Raymond, n: NodeId) -> bool {
    &&& has_token(pre, n)
    &&& !pre.using[n]
    &&& pre.queue[n].len() > 0
    &&& pre.queue[n][0] == n
    &&& post.using == pre.using.insert(n, true)
    &&& post.queue == pre.queue.insert(n, pre.queue[n].drop_first())
    &&& post.holder == pre.holder
    &&& post.asked == pre.asked
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

/// Leaving the critical section.
///
/// Guarded on `n` actually being in it: without that, an arbitrary node could
/// "leave" a section it never entered, and the transition relation would admit
/// executions that are not Raymond executions.
pub open spec fn ray_exit_cs(pre: Raymond, post: Raymond, n: NodeId) -> bool {
    &&& pre.nodes.contains(n)
    &&& pre.using[n]
    &&& post.using == pre.using.insert(n, false)
    &&& post.holder == pre.holder
    &&& post.queue == pre.queue
    &&& post.asked == pre.asked
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

/// The labelled Raymond transitions.
pub enum RayStep {
    RequestCs { node: NodeId },
    MakeRequest { node: NodeId },
    ReceiveRequest { at: NodeId, from: NodeId },
    AssignPrivilege { node: NodeId, head: NodeId },
    EnterCs { node: NodeId },
    ExitCs { node: NodeId },
}

pub open spec fn ray_step(pre: Raymond, post: Raymond, s: RayStep) -> bool {
    match s {
        RayStep::RequestCs { node } => ray_request_cs(pre, post, node),
        RayStep::MakeRequest { node } => ray_make_request(pre, post, node),
        RayStep::ReceiveRequest { at, from } => ray_receive_request(pre, post, at, from),
        RayStep::AssignPrivilege { node, head } => ray_assign_privilege(pre, post, node, head),
        RayStep::EnterCs { node } => ray_enter_cs(pre, post, node),
        RayStep::ExitCs { node } => ray_exit_cs(pre, post, node),
    }
}

/// A step that only moves *requests* around: it queues, forwards or receives a
/// request and never touches `holder`. `AssignPrivilege` is excluded because it
/// moves the token; `EnterCs` and `ExitCs` are excluded because they are
/// critical-section bookkeeping rather than routing.
pub open spec fn is_routing_step(s: RayStep) -> bool {
    match s {
        RayStep::RequestCs { node: _ } => true,
        RayStep::MakeRequest { node: _ } => true,
        RayStep::ReceiveRequest { at: _, from: _ } => true,
        RayStep::AssignPrivilege { node: _, head: _ } => false,
        RayStep::EnterCs { node: _ } => false,
        RayStep::ExitCs { node: _ } => false,
    }
}

/// A step that does not move the token: everything except `AssignPrivilege`.
///
/// Both request routing and critical-section bookkeeping qualify - they leave
/// `holder` untouched. This is the classification the composed machine needs:
/// every Raymond step is either token-preserving (and can be carried freely) or
/// the token transfer itself (which needs the ownership guard).
pub open spec fn preserves_token(s: RayStep) -> bool {
    match s {
        RayStep::AssignPrivilege { node: _, head: _ } => false,
        RayStep::RequestCs { node: _ } => true,
        RayStep::MakeRequest { node: _ } => true,
        RayStep::ReceiveRequest { at: _, from: _ } => true,
        RayStep::EnterCs { node: _ } => true,
        RayStep::ExitCs { node: _ } => true,
    }
}

/// Initial routing state: exactly one node holds the token, no requests are
/// outstanding, nobody is in the critical section.
pub open spec fn ray_init(r: Raymond, root: NodeId) -> bool {
    &&& ray_wf(r)
    &&& r.nodes.contains(root)
    &&& r.holder[root] == root
    // Triggered on `r.holder[n]`, not on `r.nodes.contains(n)`. Under the
    // latter, this clause and `ray_holder_closed` regenerate each other: this
    // one introduces `r.holder[n]`, `ray_holder_closed` turns that into
    // `r.nodes.contains(r.holder[n])`, which matches this trigger again at
    // `r.holder[n]` and introduces `r.holder[r.holder[n]]`. Same loop as the one
    // documented on `ray_holder_closed`, spread across two quantifiers.
    &&& (forall|n: NodeId| r.nodes.contains(n) && n != root ==> #[trigger] r.holder[n] != n)
    &&& (forall|n: NodeId|
        #[trigger] r.nodes.contains(n) ==> r.queue[n].len() == 0 && !r.asked[n] && !r.using[n])
    &&& (forall|m: (NodeId, NodeId)| !(#[trigger] r.requests.contains(m)))
}

// ---------------------------------------------------------------------------
// Coupling to the ownership layer
// ---------------------------------------------------------------------------

/// The glue between the two layers: **anybody with mutable authority over the
/// actor must be the node that currently possesses the Raymond token.**
///
/// Note the direction. The routing layer does not *grant* authority; it only
/// constrains who could possibly have it. Authority still comes exclusively
/// from the ownership state and its epoch.
pub open spec fn couples(r: Raymond, s: OwnershipState) -> bool {
    forall|n: NodeId, e: Epoch| #[trigger] may_mutate(s, n, e) ==> has_token(r, n)
}

} // verus!
