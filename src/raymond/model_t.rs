//! Raymond's distributed mutual-exclusion algorithm, as a *routing* layer.
//!
//! This module is deliberately independent of [`crate::ownership::spec`]: Raymond
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

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;

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
    /// Like `OwnershipSystem::network` in the ownership layer this set never shrinks and
    /// delivery does not consume, so a request stays deliverable for ever, any
    /// number of times, in any order - **including long after the holder
    /// pointers it was routed against have changed**. Recording the destination
    /// at send time is what makes that last case expressible: a guard phrased
    /// against the *current* `holder[from]` would silently drop an in-flight
    /// request the moment the token moved.
    pub requests: Set<(NodeId, NodeId)>,
    /// The node that **actually** holds the privilege.
    ///
    /// This is the authoritative fact, and it is deliberately *not* derived from
    /// `holder`. `holder[n]` is state stored **at node `n`**: it is what `n`
    /// believes, and nothing but `n` can change it. Deriving authority from
    /// belief would mean that taking the privilege away from a crashed node
    /// required editing that node's memory, which is the one thing a crash makes
    /// impossible.
    ///
    /// This is the same split the ownership layer makes between `issued` (a
    /// token is physically held) and `token_authorized` (it still confers
    /// authority). There, a crashed owner keeps its token for ever and the
    /// theorems prove it inert. Here, a node whose privilege was seized keeps
    /// *believing* it holds the privilege, and the theorems prove that inert
    /// too - see [`is_stale_holder`] and
    /// `crate::raymond::proofs::routing_layer::theorem_stale_holder_confers_no_authority`.
    pub privilege: NodeId,
}

/// `n` **believes** it holds the privilege.
///
/// Belief is per-node state and can be wrong: after a seizure the old holder
/// still believes, and goes on believing until it reconciles. Raymond's own
/// transitions are driven by belief, because a node has nothing else to act on.
pub open spec fn believes_holds(r: Raymond, n: NodeId) -> bool {
    r.nodes.contains(n) && r.holder.contains_key(n) && r.holder[n] == n
}

/// `n` **actually** holds the privilege.
///
/// This is the predicate [`couples`] is written against, so authority over the
/// actor tracks the real privilege and never a node's belief about it.
pub open spec fn has_token(r: Raymond, n: NodeId) -> bool {
    r.nodes.contains(n) && r.privilege == n
}

/// `n` believes it holds the privilege and does not: a **stale holder**.
///
/// This state is what a seizure creates, and being able to write it down is the
/// point. It is the routing counterpart of a stale capability token: physically
/// present, entirely inert.
pub open spec fn is_stale_holder(r: Raymond, n: NodeId) -> bool {
    believes_holds(r, n) && !has_token(r, n)
}

/// Nobody's belief is stale - every node that believes it holds the privilege
/// does.
///
/// Normal operation. A seizure leaves this false until the seized node
/// reconciles, which is exactly the window in which the routing layer's
/// belief-level guarantees do not hold. Theorems that need those guarantees say
/// so by requiring this.
pub open spec fn ray_no_stale_holders(r: Raymond) -> bool {
    forall|n: NodeId| #[trigger] believes_holds(r, n) ==> has_token(r, n)
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
    &&& r.nodes.contains(r.privilege)
}

/// **At most one valid token.**
///
/// Now structural rather than something to maintain: `privilege` is one value,
/// so two nodes cannot both hold it. That is the payoff of not deriving
/// authority from the holder pointers - uniqueness used to be an invariant that
/// every transition had to be shown to preserve, and it used to be the reason
/// the dangerous state was unrepresentable. Belief is where the multiplicity
/// now lives, and belief is inert.
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

/// **The node that holds the privilege believes it does.**
///
/// The converse is exactly what fails after a seizure, and exactly what
/// [`is_stale_holder`] names. This direction never fails: the privilege only
/// ever moves to a node that is told about it in the same step.
pub open spec fn ray_authority_believes(r: Raymond) -> bool {
    forall|n: NodeId| #[trigger] has_token(r, n) ==> believes_holds(r, n)
}

/// A rank witnessing that the holder pointers form a forest directed at its
/// roots: every node that is not a root has a parent strictly closer to one.
///
/// A strictly decreasing `nat` along every edge is exactly well-foundedness, so
/// no cycle can satisfy this - going round one would have to return to a rank
/// it had already gone below.
pub open spec fn ray_ranked_by(r: Raymond, rank: Map<NodeId, nat>) -> bool {
    &&& (forall|n: NodeId| #[trigger] r.nodes.contains(n) ==> rank.contains_key(n))
    &&& (forall|n: NodeId|
        r.nodes.contains(n) && #[trigger] r.holder[n] != n ==> rank[r.holder[n]] < rank[n])
}

/// **The holder pointers are acyclic.**
///
/// `ray_unique_token` and `ray_token_exists` together say there is exactly one
/// root, and that is *still* not enough to make the holder graph a tree: nothing
/// stopped a set of non-root nodes from pointing at each other in a cycle, off
/// to one side of the real root. `ray_init` permitted it too - it forbids only a
/// non-root pointing at *itself*, so `A -> B`, `B -> A` beside a root `C -> C`
/// satisfied it.
///
/// Such a state is not a Raymond state, and the consequence is visible in this
/// module's own documentation: "requests travel hop-by-hop towards the token"
/// is false for a node in such a cycle, whose request would circle for ever.
/// Nothing in the safety proofs depended on the claim, which is precisely why
/// it went unchecked.
///
/// Stated as the *existence* of a rank rather than as "no cycle" because the
/// existential is what the proofs want: a step preserves acyclicity by
/// exhibiting a new rank, which for both token movers is the old one shifted up
/// by one with the new root sent to zero (see
/// `crate::raymond::proofs::routing_layer::lemma_repoint_acyclic`).
pub open spec fn ray_acyclic(r: Raymond) -> bool {
    exists|rank: Map<NodeId, nat>| #[trigger] ray_ranked_by(r, rank)
}

/// Following holder pointers `k` times from `n`.
pub open spec fn holder_iter(r: Raymond, n: NodeId, k: nat) -> NodeId
    decreases k,
{
    if k == 0 {
        n
    } else {
        r.holder[holder_iter(r, n, (k - 1) as nat)]
    }
}

/// Only a node that **believes** it holds the privilege can be inside its
/// critical section.
///
/// Belief, not authority, because belief is all a node has to act on. This used
/// to say `has_token`, and it could, because seizure reached into the crashed
/// node and cleared its `using` flag for it. Now that it does not, a stale
/// holder inside its critical section is a state this model can write down -
/// which is the point. What it costs is Raymond-level mutual exclusion during
/// the window before reconciliation; what it does not cost is ownership safety,
/// because [`couples`] is written against authority. See
/// `crate::raymond::proofs::routing_layer::theorem_stale_holder_confers_no_authority`.
pub open spec fn ray_using_implies_belief(r: Raymond) -> bool {
    forall|n: NodeId| #[trigger] r.nodes.contains(n) && r.using[n] ==> believes_holds(r, n)
}

/// The Raymond safety invariant.
pub open spec fn ray_inv(r: Raymond) -> bool {
    &&& ray_wf(r)
    &&& ray_authority_believes(r)
    &&& ray_using_implies_belief(r)
    &&& ray_acyclic(r)
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
    &&& post.privilege == pre.privilege
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
    &&& post.privilege == pre.privilege
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
    &&& post.privilege == pre.privilege
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
    &&& believes_holds(pre, n)
    &&& !pre.using[n]
    &&& pre.queue[n].len() > 0
    &&& pre.queue[n][0] == head
    &&& head != n
    &&& pre.nodes.contains(head)
    // Both nodes act: `n` is live and cooperating, so it may rewrite its own
    // belief, and `head` learns it has the privilege in the same step. That is
    // what distinguishes a handover from a seizure, where only the new holder
    // acts.
    &&& post.holder == pre.holder.insert(n, head).insert(head, head)
    &&& post.privilege == head
    &&& post.queue == pre.queue.insert(n, pre.queue[n].drop_first())
    &&& post.asked == pre.asked.insert(n, false)
    &&& post.using == pre.using
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

/// The token holder is itself at the head of its queue, so it enters the
/// critical section.
pub open spec fn ray_enter_cs(pre: Raymond, post: Raymond, n: NodeId) -> bool {
    // Belief, not authority: a node decides to enter on what it knows, and a
    // stale holder does not know it is stale. Guarding this on `has_token`
    // would be assuming the conclusion.
    &&& believes_holds(pre, n)
    &&& !pre.using[n]
    &&& pre.queue[n].len() > 0
    &&& pre.queue[n][0] == n
    &&& post.using == pre.using.insert(n, true)
    &&& post.queue == pre.queue.insert(n, pre.queue[n].drop_first())
    &&& post.holder == pre.holder
    &&& post.privilege == pre.privilege
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
    &&& post.privilege == pre.privilege
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

/// The node a Raymond step makes **act** - the one whose local state it writes.
///
/// Every token-preserving transition mutates the maps of exactly one node:
/// `RequestCs`, `MakeRequest`, `EnterCs` and `ExitCs` write the named node's
/// own entries, and `ReceiveRequest` writes `at`'s queue - `from` sent its
/// request at some earlier point and takes no part in the delivery.
///
/// `AssignPrivilege` is the exception: it makes *two* nodes act, the holder and
/// the recipient. It is never carried by [`crate::composed::model::cs_ray`], which is
/// guarded on `preserves_token`, and
/// [`crate::composed::model::cs_pass_token`] guards both of its nodes explicitly. The
/// arm below exists only to keep this function total.
pub open spec fn ray_step_actor(s: RayStep) -> NodeId {
    match s {
        RayStep::RequestCs { node } => node,
        RayStep::MakeRequest { node } => node,
        RayStep::ReceiveRequest { at, from: _ } => at,
        RayStep::EnterCs { node } => node,
        RayStep::ExitCs { node } => node,
        RayStep::AssignPrivilege { node, head: _ } => node,
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
    // Belief and authority agree at the start: the root is the holder and knows
    // it. Divergence is something a seizure introduces, not something a system
    // begins with.
    &&& r.privilege == root
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
    // Without this clause `ray_init` admits a non-root cycle in `holder` - the
    // clause above forbids only a non-root pointing at itself - so an initial
    // state could contain nodes that never reach the token at all. See
    // `ray_acyclic`.
    &&& ray_acyclic(r)
}

/// **The privilege is seized.** It is re-established at `to` without the node
/// that holds it acting at all.
///
/// This is deliberately *not* a [`RayStep`]. Raymond's algorithm has no
/// seizure: every privilege movement in it is the holder voluntarily passing
/// the privilege to the head of its queue. Seizure is a recovery action taken
/// by the coordinator after it has revoked an owner, so it belongs to the
/// composed machine ([`crate::composed::model::cs_seize_token`]), where the revocation
/// that justifies it is visible.
///
/// **Only `to` acts.** `from`'s `holder`, `using` and `asked` entries are
/// untouched, because they are stored at `from` and `from` may well be
/// unreachable - reaching into them would be modelling something no
/// implementation can do. So after a seizure `from` is a
/// [stale holder][`is_stale_holder`]: it believes it holds the privilege, it
/// does not, and it may still be inside its critical section believing that
/// too.
///
/// An earlier version of this model did edit those entries, and the reason is
/// worth recording: with authority derived from `holder`, there was no other
/// way to move the privilege, and the state where a returning node still
/// believed violated the uniqueness invariant outright. The invariant held
/// because the dangerous state could not be written down. Splitting belief from
/// authority is what makes it writable, and
/// `crate::raymond::proofs::routing_layer::theorem_stale_holder_confers_no_authority` is what
/// makes it harmless.
pub open spec fn ray_seize(pre: Raymond, post: Raymond, from: NodeId, to: NodeId) -> bool {
    &&& has_token(pre, from)
    &&& pre.nodes.contains(to)
    &&& to != from
    // `to` is told it now holds the privilege. Nothing else changes - in
    // particular nothing belonging to `from`.
    &&& post.holder == pre.holder.insert(to, to)
    &&& post.privilege == to
    &&& post.queue == pre.queue
    &&& post.asked == pre.asked
    &&& post.using == pre.using
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

/// **A stale holder reconciles**: it learns its privilege was taken, drops the
/// belief, and leaves the critical section it thought it was in.
///
/// Like [`ray_seize`] this is not a [`RayStep`] - Raymond has no such action.
/// It is the step a real deployment must perform before a fenced node rejoins,
/// and it is the one that does the work: re-point `holder[n]` away from itself,
/// and clear `using[n]`.
///
/// Note which node acts. Reconciliation is `n` itself discovering the truth, so
/// editing `n`'s own state is exactly right here and exactly wrong in
/// [`ray_seize`]. That asymmetry is the whole content of the step: the belief
/// is dropped by the node that holds it, at the moment it comes back, rather
/// than by the coordinator at the moment it left.
pub open spec fn ray_reconcile(pre: Raymond, post: Raymond, n: NodeId) -> bool {
    &&& is_stale_holder(pre, n)
    // It re-points at the node that actually holds the privilege. A real
    // implementation might learn any node on a path to the holder; pointing
    // straight at it is the simplest faithful choice, and it is what makes the
    // repaired belief graph a tree again.
    &&& post.holder == pre.holder.insert(n, pre.privilege)
    &&& post.using == pre.using.insert(n, false)
    &&& post.asked == pre.asked.insert(n, false)
    &&& post.privilege == pre.privilege
    &&& post.queue == pre.queue
    &&& post.nodes == pre.nodes
    &&& post.requests == pre.requests
}

pub open spec fn ray_next(pre: Raymond, post: Raymond) -> bool {
    exists|s: RayStep| #[trigger] ray_step(pre, post, s)
}

/// A finite run of the routing layer.
///
/// Raymond has no `init`-based reachability of its own - the algorithm is a
/// transition relation, not a system with a designated start - so what a
/// scenario needs is "this state leads to that one". Exporting a step and an
/// endpoint as independent existentials says nothing about whether the
/// endpoint came from that step, which is how a twelve-hop construction ends
/// up provable by a directly built state that did none of the hops.
pub open spec fn ray_segment(tr: Seq<Raymond>) -> bool {
    &&& tr.len() > 0
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> ray_next(tr[i], tr[i + 1]))
}

/// A **labelled** finite run of the routing layer: `tr` holds the states and
/// `labels[i]` is the transition from `tr[i]` to `tr[i + 1]`.
///
/// `ray_segment` hides its steps inside `ray_next`'s existential, which is
/// enough to say "this state leads to that one" and not enough to say *how*.
/// For a scenario named after a route it is the how that matters: the request
/// path `D -> B -> A -> C` and a run in which `A`, `B` and `D` each request
/// independently and then serve their own queues end in the same place, and a
/// contract written against `ray_segment` cannot tell them apart. Carrying the
/// labels does.
pub open spec fn ray_run(tr: Seq<Raymond>, labels: Seq<RayStep>) -> bool {
    &&& tr.len() > 0
    &&& labels.len() == tr.len() - 1
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() ==> ray_step(tr[i], tr[i + 1], labels[i]))
}

/// `post` is reachable **from** `pre` by a finite run of the routing layer.
pub open spec fn ray_reachable_from(pre: Raymond, post: Raymond) -> bool {
    exists|tr: Seq<Raymond>|
        #[trigger] ray_segment(tr) && tr[0] == pre && tr[tr.len() - 1] == post
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
