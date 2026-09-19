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
//!   and only from a node that has fail-stopped, so that crash-driven takeover -
//!   the case epochs exist for - is reachable rather than requiring a dead node
//!   to cooperate. Token movement is therefore partitioned by liveness: a live
//!   holder passes, a crashed one is seized from, and there is no third way;
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
    /// Nodes whose routing state was rewritten by a seizure while they were
    /// down, and which have not yet been told.
    ///
    /// This exists because [`cs_seize_token`] edits `from`'s `holder` and
    /// `using` entries while `from` is fail-stopped, and `Step::Recover`'s
    /// contract says a node comes back *with no knowledge of what happened
    /// meanwhile*. Without a marker, recovery would silently inherit the
    /// rewrite: the model would have the returning node know it had lost the
    /// token, while the real one would still believe `holder[n] == n` and could
    /// enter its Raymond critical section beside the new holder. Ownership
    /// would still be safe - the epoch fences it - but Raymond's critical
    /// section has no epoch, which is exactly the asymmetry documented on
    /// [`cs_seize_token`].
    ///
    /// So the reconciliation a real deployment must perform is a *modelled
    /// transition* ([`cs_reconcile`]) rather than an assumption: a seized node
    /// cannot rejoin `live` until it has taken it.
    pub seized: Set<NodeId>,
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
    // The two layers talk about the *same* cluster. Without this, a state could
    // have a Raymond root that the ownership layer has never heard of, so
    // `!own.live.contains(n)` would hold for it with no `Crash` ever having
    // happened - and `cs_seize_token`'s liveness guard would be satisfied by a
    // node whose liveness was simply not modelled rather than by one that
    // fail-stopped.
    &&& c.ray.nodes == c.own.nodes
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
    &&& post.seized == pre.seized
}

/// Any ownership transition that does not create authority over this actor.
pub open spec fn cs_own(pre: Composed, post: Composed, s: Step) -> bool {
    &&& !is_acquire_of(s, pre.actor)
    &&& !recovers_a_seized_node(pre, s)
    &&& step(pre.own, post.own, s)
    &&& post.ray == pre.ray
    &&& post.actor == pre.actor
    &&& post.seized == pre.seized
}

/// The token moves - **only** once the actor has actually been released.
///
/// This guard is the whole point of the module: it is what turns the side
/// condition of `theorem_token_transfer_preserves_ownership_safety` into
/// something the machine enforces.
///
/// The first guard is `is_unowned`, not merely `!is_owned`: `Transferring` also
/// satisfies `!is_owned`, so the weaker form would let the token move while a
/// handover was still in flight and the outgoing owner had not yet
/// acknowledged the revoke. Safety would survive that - nobody has authority
/// while `Transferring` either - but it would not be the
/// release-before-transfer discipline this module claims to enforce.
///
/// The second guard, `pre.own.live.contains(n)`, is what makes this step mean
/// what it is written as. `ray_assign_privilege` models the holder *acting* -
/// choosing to hand the privilege to the head of its queue - and a crashed node
/// cannot act. Without it, a dead node could still voluntarily pass the token,
/// which is exactly the cooperation [`cs_seize_token`] exists to avoid needing;
/// adding seizure without this guard would have opened the forcible path while
/// leaving the impossible one open beside it.
///
/// Together the two transitions partition token movement by the holder's
/// liveness: a live holder passes, a crashed one is seized from, and
/// `proofs::composed::theorem_token_movement_is_partitioned` proves there is no
/// third way.
pub open spec fn cs_pass_token(pre: Composed, post: Composed, n: NodeId, head: NodeId) -> bool {
    &&& is_unowned(pre.own.actors[pre.actor])
    &&& pre.own.live.contains(n)
    &&& ray_assign_privilege(pre.ray, post.ray, n, head)
    &&& post.own == pre.own
    &&& post.actor == pre.actor
    &&& post.seized == pre.seized
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
    &&& post.seized == pre.seized.insert(from)
}

/// A node takes ownership - **only** if it is the node holding the token.
pub open spec fn cs_acquire_under_token(pre: Composed, post: Composed, n: NodeId) -> bool {
    &&& has_token(pre.ray, n)
    &&& tr_acquire(pre.own, post.own, pre.actor, n)
    &&& post.ray == pre.ray
    &&& post.actor == pre.actor
    &&& post.seized == pre.seized
}

/// `s` brings a node back that is still carrying an unacknowledged seizure.
///
/// [`cs_own`] refuses these. Everything else about `Step::Recover` is unchanged
/// - a node that was merely crashed, and whose routing state nobody touched,
/// comes back exactly as before.
pub open spec fn recovers_a_seized_node(c: Composed, s: Step) -> bool {
    match s {
        Step::Recover { node } => c.seized.contains(node),
        _ => false,
    }
}

/// A seized node is told what happened while it was down.
///
/// This is the modelled counterpart of the reconciliation a real
/// implementation has to perform before a fenced node rejoins: re-read the
/// routing state rather than trust what it remembers. It changes nothing except
/// the marker, because in this model the routing state *is* the truth - the
/// step exists so that an execution has to contain it, rather than helping
/// itself to the conclusion.
///
/// It fires while the node is still down, which is the honest ordering: you
/// learn the truth as part of coming back, not after you have started acting.
pub open spec fn cs_reconcile(pre: Composed, post: Composed, n: NodeId) -> bool {
    &&& !pre.own.live.contains(n)
    &&& pre.seized.contains(n)
    &&& post.seized == pre.seized.remove(n)
    &&& post.own == pre.own
    &&& post.ray == pre.ray
    &&& post.actor == pre.actor
}

/// The labelled transitions of the composed machine.
pub enum ComposedStep {
    Ray { ray_step: RayStep },
    Own { own_step: Step },
    PassToken { node: NodeId, head: NodeId },
    SeizeToken { from: NodeId, to: NodeId },
    Reconcile { node: NodeId },
    AcquireUnderToken { node: NodeId },
}

pub open spec fn composed_step(pre: Composed, post: Composed, s: ComposedStep) -> bool {
    match s {
        ComposedStep::Ray { ray_step } => cs_ray(pre, post, ray_step),
        ComposedStep::Own { own_step } => cs_own(pre, post, own_step),
        ComposedStep::PassToken { node, head } => cs_pass_token(pre, post, node, head),
        ComposedStep::SeizeToken { from, to } => cs_seize_token(pre, post, from, to),
        ComposedStep::Reconcile { node } => cs_reconcile(pre, post, node),
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
    &&& c.ray.nodes == c.own.nodes
    &&& c.seized == Set::<NodeId>::empty()
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

/// A **labelled** finite run: `tr` holds the states and `labels[i]` is the step
/// that takes `tr[i]` to `tr[i + 1]`.
///
/// This is the strongest of the run predicates in this file, and it exists
/// because the weaker ones cannot pin a *named* scenario down.
/// `composed_reachable_from(c, d)` says that some run joins `c` to `d`, but
/// which steps it took is hidden inside `composed_next`'s existential. A
/// contract assembled out of reachability plus a handful of exported endpoints
/// therefore claims much less than its name suggests: **any** run ending in a
/// state of the same shape satisfies it. Three scenarios in this crate were
/// caught that way, each by a different substitute execution - a seizure
/// standing in for a handover, a revocation standing in for a voluntary
/// release, independent requests standing in for a forwarded one - and each
/// time the repair was to exclude the one substitute that had been found.
///
/// Exhibiting `labels` removes the room to substitute at all. A scenario that
/// fixes every entry of `labels` has said precisely which steps its run
/// consists of and in what order, so no other run can satisfy it - not because
/// each alternative was anticipated and ruled out one at a time, but because
/// nothing is left free to vary.
pub open spec fn composed_run(tr: Seq<Composed>, labels: Seq<ComposedStep>) -> bool {
    &&& tr.len() > 0
    &&& labels.len() == tr.len() - 1
    // Multi-trigger on the two adjacent states and the label between them, for
    // the reason documented on `crate::model::valid_execution`.
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() ==> composed_step(tr[i], tr[i + 1], labels[i]))
}

/// A labelled run that starts at initialisation: the full history of a system
/// from `composed_init`, with every step named.
pub open spec fn composed_labelled_execution(
    tr: Seq<Composed>,
    labels: Seq<ComposedStep>,
) -> bool {
    &&& composed_run(tr, labels)
    &&& composed_init(tr[0])
}

/// A finite run of the composed machine that need **not** start at
/// `composed_init`.
///
/// `composed_reachable` says a state is reachable from initialisation, which is
/// what safety theorems want. Scenarios want something else: that one state
/// leads to another. Exporting a step and an endpoint as *independent*
/// existentials says nothing about whether the endpoint came from that step -
/// an unrelated execution can supply it - so a scenario built that way keeps
/// verifying even when the interesting continuation becomes impossible.
pub open spec fn composed_segment(tr: Seq<Composed>) -> bool {
    &&& tr.len() > 0
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> composed_next(tr[i], tr[i + 1]))
}

/// `d` is reachable **from** `c` by a finite run of the composed machine.
pub open spec fn composed_reachable_from(c: Composed, d: Composed) -> bool {
    exists|tr: Seq<Composed>|
        #[trigger] composed_segment(tr) && tr[0] == c && tr[tr.len() - 1] == d
}

/// `c` is reachable in the composed machine.
pub open spec fn composed_reachable(c: Composed) -> bool {
    exists|tr: Seq<Composed>| composed_valid_execution(tr) && tr[tr.len() - 1] == c
}

} // verus!
