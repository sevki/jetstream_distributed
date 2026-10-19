//! The two layers, composed.
//!
//! [`crate::raymond::model`] decides *where the token is*; [`crate::ownership::spec`] decides
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
//! * [`ComposedStep::SeizeToken`] moves the privilege *without* the holder
//!   acting, so that crash-driven takeover - the case epochs exist for - is
//!   reachable rather than requiring a dead node to cooperate. It says nothing
//!   about whether that holder is alive: `!live` is ground truth no coordinator
//!   can evaluate, and a node wrongly suspected must be handled rather than
//!   excluded. Privilege movement is therefore partitioned by **cooperation**,
//!   not by liveness: a holder that acts passes it on, one that does not has it
//!   taken, and there is no third way;
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

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::raymond::model::*;

verus! {

/// One actor, governed jointly by the ownership protocol and Raymond routing.
pub struct Composed {
    pub own: OwnershipSystem,
    pub ray: Raymond,
    pub actor: ActorId,
    /// Nodes whose privilege was taken by a seizure and whose belief has not yet
    /// been repaired - the nodes that **owe a reconciliation**.
    ///
    /// [`cs_seize_token`] deliberately leaves `from`'s `holder`, `using` and
    /// `asked` entries exactly as they were, because they are memory at `from`
    /// and nothing can reach into a node that is down. So after a seizure
    /// `from` is a [stale holder][`crate::raymond::model::is_stale_holder`]: it
    /// believes it holds the privilege, it does not, and it may still be inside
    /// its critical section believing that too. Ownership is safe regardless -
    /// the epoch fences it, and
    /// `crate::raymond::proofs::routing_layer::theorem_stale_holder_confers_no_authority`
    /// proves it - but Raymond's critical section has no epoch, so the belief
    /// has to be repaired before the node acts again.
    ///
    /// `composed_inv` ties this set to that: **every stale holder is in it**.
    /// A seizure adds one and creates one; [`cs_reconcile`] removes one and
    /// repairs one; and a grant discharges the debt outright, because receiving
    /// the privilege *is* the node learning the truth. So the reconciliation a
    /// real deployment must perform is a modelled transition rather than an
    /// assumption, and [`recovers_a_seized_node`] is what stops a node coming
    /// back and acting on a belief it never corrected.
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
    // **Every stale holder owes a reconciliation.** This is what makes `seized`
    // mean something: it is exactly the set of nodes whose belief the
    // coordinator has invalidated and not yet repaired. A seizure adds one and
    // creates one; reconciliation removes one and repairs one; no other step
    // creates a stale holder at all.
    &&& (forall|n: NodeId| #[trigger] is_stale_holder(c.ray, n) ==> c.seized.contains(n))
}

/// Any Raymond step that does not move the token: request routing *and*
/// critical-section bookkeeping. None of them touch ownership.
///
/// The guard is `preserves_token`, not `is_routing_step`: the composed machine
/// has to admit `EnterCs` and `ExitCs` too, or no composed execution could ever
/// enter a critical section and the composed theorems would only cover states
/// where `using` is uniformly false.
///
/// **The acting node must be live.** Every one of these transitions writes some
/// node's own local maps - its queue, its `asked` flag, its `using` flag - and
/// a crashed node executes nothing, so without this guard the carrier admitted
/// a dead node queueing requests, forwarding them, and entering its critical
/// section. That last one is the serious case: after
/// `Crash(A) -> RevokeOwner -> SeizeToken(A, B)`, the carrier let
/// `Ray { EnterCs(A) }` fire on `A`'s untouched holder and queue while `A` was
/// still down and still marked, walking straight past the
/// reconciliation-before-acting discipline that
/// [`recovers_a_seized_node`] exists to enforce.
///
/// This is the same rule as on [`cs_pass_token`] and [`cs_seize_token`] -
/// liveness may guard the nodes a step makes act - applied to the carrier that
/// has most of them. [`crate::raymond::model::ray_step_actor`] names which node that
/// is for each variant; `ReceiveRequest` acts at `at`, since `from` sent its
/// request earlier and takes no part in the delivery.
pub open spec fn cs_ray(pre: Composed, post: Composed, s: RayStep) -> bool {
    &&& preserves_token(s)
    &&& pre.own.live.contains(ray_step_actor(s))
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
/// The liveness guards are what make this step mean what it is written as.
/// `ray_assign_privilege` models *both* nodes acting - the holder choosing to
/// hand the privilege to the head of its queue, and the head receiving it - and
/// a crashed node cannot act. Without the guard on `n`, a dead node could still
/// voluntarily pass the privilege, which is exactly the cooperation
/// [`cs_seize_token`] exists to avoid needing; without the guard on `head`, the
/// step would install a belief in a node that cannot receive it.
///
/// Together the two transitions partition privilege movement by whether the
/// holder acts: a cooperating holder passes, an uncooperative one is seized
/// from, and
/// `proofs::composed::theorem_token_movement_is_partitioned` proves there is no
/// third way.
pub open spec fn cs_pass_token(pre: Composed, post: Composed, n: NodeId, head: NodeId) -> bool {
    &&& is_unowned(pre.own.actors[pre.actor])
    // Both nodes must be live, because `ray_assign_privilege` has both of them
    // act: `n` chooses to pass the privilege on and rewrites its own belief,
    // and `head` receives it and records `holder[head] := head`. Without the
    // second guard the step installs a belief in a node that may have crashed
    // after its request arrived - the same unreachable-memory move that
    // [`cs_seize_token`] no longer makes for the old holder - and a later
    // `Recover(head)` would frame it in, so the node would be modelled as
    // knowing about an event it could not have observed.
    //
    // See the note on [`cs_seize_token`] for why these guards are not the
    // oracle that `!live` was.
    &&& pre.own.live.contains(n)
    &&& pre.own.live.contains(head)
    &&& ray_assign_privilege(pre.ray, post.ray, n, head)
    &&& post.own == pre.own
    &&& post.actor == pre.actor
    // Same discharge as on [`cs_seize_token`]: `head` receives the privilege,
    // records that it holds it, and really does, so a reconciliation it owed
    // from an earlier seizure is settled by the handover itself.
    &&& post.seized == pre.seized.remove(head)
}

/// The privilege is **seized** and re-established at `to`, without the node
/// that holds it acting.
///
/// This is the step that makes crash-driven takeover expressible. Without it
/// the only way the privilege can move is [`cs_pass_token`], which requires
/// `has_token(pre.ray, from)` *and* models `from` voluntarily passing it on. So
/// after `RevokeOwner` fires against a crashed owner `A` - leaving the actor
/// `Unowned` at the next epoch and offered to `B` - the only composed
/// continuation was `A`, a node the ownership layer has marked dead, taking a
/// routing step. That is precisely the cooperation epochs and fencing exist to
/// make unnecessary.
///
/// The guard is the same `is_unowned` as [`cs_pass_token`], and for the same
/// reason: in `Unowned` nobody has authority at all, so moving the privilege
/// cannot strand it. Seizure is safe for exactly the reason revocation is - the
/// epoch was burned first.
///
/// **There is deliberately no liveness guard.** An earlier version required
/// `!pre.own.live.contains(from)`, on the argument that seizing from a live
/// node would let the model report exclusivity while two nodes were really
/// inside their Raymond critical sections. The argument was sound and the
/// conclusion was wrong, for two reasons.
///
/// The first is that it conflated two guarantees. Ownership safety is fenced by
/// the epoch, which is burned *before* the seizure fires, so it does not need
/// the node to be dead. Raymond's critical-section exclusivity has no epoch and
/// does need something - but the honest something is
/// `crate::raymond::model::ray_no_stale_holders`, a condition on the state, not a
/// guard on the step.
///
/// The second is that `!live` is **ground truth**, and no coordinator has it. A
/// real one has a suspicion, which is exactly why `RevokeOwner` is modelled as
/// firing against healthy nodes. Guarding the forcible path on perfect failure
/// detection would have put the composed machine's strongest theorems out of
/// reach of any deployment, in a clause that reads like an ordinary guard.
///
/// What replaces it is that [`crate::raymond::model::ray_seize`] no longer touches
/// anything belonging to `from`, so the state it creates - a stale holder,
/// possibly still inside its critical section - is representable and proved
/// inert rather than excluded.
///
/// **`to` must be live, and that is not the same kind of guard.** The step
/// writes `holder[to] := to`, which is memory at `to`, so `to` is one of the
/// nodes *acting*: the coordinator hands it the privilege and it records that.
/// A liveness guard on a node that acts in the step is a statement about who
/// takes part, not a detection requirement - nobody has to determine that `to`
/// is up, because if it is not, the exchange simply does not happen. A liveness
/// guard on a node that does *not* act, which is what `!live(from)` was, is an
/// oracle, because something has to evaluate it before the step may fire.
///
/// That is the rule the whole file now follows: **liveness may guard the nodes
/// a step makes act, and may not guard the ones it does not.** Under it,
/// `cs_pass_token` guards both `n` and `head`, this step guards `to` and says
/// nothing about `from`, and `cs_reconcile` guards nobody - a node repairing
/// its own belief is acting by definition.
pub open spec fn cs_seize_token(pre: Composed, post: Composed, from: NodeId, to: NodeId) -> bool {
    &&& is_unowned(pre.own.actors[pre.actor])
    &&& pre.own.live.contains(to)
    &&& ray_seize(pre.ray, post.ray, from, to)
    &&& post.own == pre.own
    &&& post.actor == pre.actor
    // `from` now owes a reconciliation, and `to` no longer does. Granting the
    // privilege *is* the node learning the truth: `to` is live, it records
    // `holder[to] := to`, and it really does hold, so its belief is correct
    // again and there is nothing left to repair.
    //
    // Without the `remove`, a node marked by an earlier seizure and then handed
    // the privilege back would stop being stale while staying marked, so
    // `cs_reconcile` - which requires `is_stale_holder` - could never clear it,
    // and `recovers_a_seized_node` would reject its recovery for ever. That
    // became reachable only when the `!live(from)` guard came off: before, a
    // marked node was always dead and had to reconcile before rejoining, so it
    // could never be a live grant target.
    &&& post.seized == pre.seized.insert(from).remove(to)
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

/// A seized node **reconciles**: it discovers its privilege was taken, drops
/// the belief, and leaves the critical section it thought it was in.
///
/// This step used to be a marker removal - it changed nothing but the `seized`
/// set, because seizure had already edited the node's routing state on its
/// behalf. Row C6 claimed it made reconciliation "a step an execution has to
/// contain rather than an assumption", and the step was in the execution, but
/// it carried no content: the work a deployment must actually do had been done
/// at seizure time, by the coordinator, reaching into a node it could not
/// reach.
///
/// Now that [`crate::raymond::model::ray_seize`] leaves the seized node alone, this is
/// where the stale belief is dropped, by the node that holds it.
///
/// It is not guarded on the node being down. Seizure is no longer restricted to
/// crashed nodes, so a live node can be left stale - by a coordinator that
/// suspected it wrongly - and must be able to learn the truth as well. What the
/// ordering rule still enforces is the *crashed* case:
/// [`recovers_a_seized_node`] refuses `Step::Recover` until this step has run,
/// so a node cannot come back and start acting on a belief it never corrected.
pub open spec fn cs_reconcile(pre: Composed, post: Composed, n: NodeId) -> bool {
    &&& pre.seized.contains(n)
    &&& ray_reconcile(pre.ray, post.ray, n)
    &&& post.seized == pre.seized.remove(n)
    &&& post.own == pre.own
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
    // `crate::ownership::model::valid_execution`.
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
    // the reason documented on `crate::ownership::model::valid_execution`.
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
