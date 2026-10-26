//! **Claim 7 - the Raymond routing layer.**
//!
//! * there is at most one valid token;
//! * token transfer preserves ownership safety;
//! * holder/routing changes cannot manufacture ownership;
//! * duplicate/reordered requests cannot create a second owner.
//!
//! Liveness is *not* claimed. See the book's Reference (`book/src/reference/raymond.md`).
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::raymond::model::*;

verus! {

/// The initial routing state satisfies the Raymond invariant.
pub proof fn theorem_ray_init_inv(r: Raymond, root: Id)
    requires
        ray_init(r, root),
    ensures
        ray_inv(r),
        has_token(r, root),
        believes_holds(r, root),
        ray_no_stale_holders(r),
{
    assert(has_token(r, root));
    assert(believes_holds(r, root));
    assert forall|n: Id| #[trigger] has_token(r, n) implies believes_holds(r, n) by {
        assert(n == root);
    }
    assert forall|n: Id| #[trigger] r.nodes.contains(n) && r.using[n] implies believes_holds(
        r,
        n,
    ) by {
        assert(!r.using[n]);
    }
    // Nobody is stale at the start: a non-root node does not point at itself,
    // and the root is the holder.
    assert forall|n: Id| #[trigger] believes_holds(r, n) implies has_token(r, n) by {
        if n != root {
            assert(r.holder[n] != n);
            assert(false);
        }
    }
}

/// Request routing never moves the privilege: neither `holder` nor `privilege`
/// is touched by `RequestCs`, `MakeRequest` and `ReceiveRequest`.
pub proof fn lemma_routing_preserves_holder(pre: Raymond, post: Raymond, s: RayStep)
    requires
        ray_step(pre, post, s),
        is_routing_step(s),
    ensures
        post.holder == pre.holder,
        post.privilege == pre.privilege,
        post.nodes == pre.nodes,
        forall|n: Id| #[trigger] has_token(post, n) <==> has_token(pre, n),
        forall|n: Id| #[trigger] believes_holds(post, n) <==> believes_holds(pre, n),
{
    match s {
        RayStep::RequestCs { node } => {},
        RayStep::MakeRequest { node } => {},
        RayStep::ReceiveRequest { at, from } => {},
        _ => {
            assert(false);
        },
    }
}

/// Every step except the privilege transfer leaves `holder` and `privilege` -
/// and therefore both belief and authority - completely alone.
pub proof fn lemma_token_preserving_steps_keep_holder(pre: Raymond, post: Raymond, s: RayStep)
    requires
        ray_step(pre, post, s),
        preserves_token(s),
    ensures
        post.holder == pre.holder,
        post.privilege == pre.privilege,
        post.nodes == pre.nodes,
        forall|n: Id| #[trigger] has_token(post, n) <==> has_token(pre, n),
        forall|n: Id| #[trigger] believes_holds(post, n) <==> believes_holds(pre, n),
{
    match s {
        RayStep::RequestCs { node } => {},
        RayStep::MakeRequest { node } => {},
        RayStep::ReceiveRequest { at, from } => {},
        RayStep::EnterCs { node } => {},
        RayStep::ExitCs { node } => {},
        RayStep::AssignPrivilege { node, head } => {
            assert(false);
        },
    }
}

/// **Holder/routing changes cannot manufacture ownership.**
///
/// A routing step leaves the token where it is, therefore it leaves the
/// coupling to the ownership layer intact: nobody gains authority by sending,
/// forwarding, duplicating or reordering requests.
pub proof fn theorem_routing_cannot_manufacture_ownership(
    pre: Raymond,
    post: Raymond,
    s: RayStep,
    own: OwnershipState,
)
    requires
        ray_inv(pre),
        ray_step(pre, post, s),
        is_routing_step(s),
        couples(pre, own),
    ensures
        couples(post, own),
        forall|n: Id| #[trigger] has_token(post, n) <==> has_token(pre, n),
{
    lemma_routing_preserves_holder(pre, post, s);
}

/// **Duplicate and reordered requests cannot create a second owner.**
///
/// `ray_receive_request` has no sequence number and no duplicate suppression:
/// it can fire arbitrarily often, for any `(at, from)` pair whose request was
/// ever sent, in any order. It still cannot produce a second token holder,
/// because it does not touch `holder` at all.
pub proof fn theorem_duplicate_requests_are_safe(
    pre: Raymond,
    mid: Raymond,
    post: Raymond,
    at: Id,
    from: Id,
)
    requires
        ray_inv(pre),
        ray_receive_request(pre, mid, at, from),
        ray_receive_request(mid, post, at, from),
    ensures
        ray_inv(post),
        forall|n: Id| #[trigger] has_token(post, n) <==> has_token(pre, n),
{
    lemma_ray_step_preserves_inv(pre, mid, RayStep::ReceiveRequest { at: at, from: from });
    lemma_ray_step_preserves_inv(mid, post, RayStep::ReceiveRequest { at: at, from: from });
}

/// A step that leaves `nodes`, `holder` and `privilege` alone leaves both
/// belief and authority alone.
pub proof fn lemma_same_holder_same_token(pre: Raymond, post: Raymond)
    requires
        post.nodes == pre.nodes,
        post.holder == pre.holder,
        post.privilege == pre.privilege,
    ensures
        forall|m: Id| #[trigger] has_token(post, m) <==> has_token(pre, m),
        forall|m: Id| #[trigger] believes_holds(post, m) <==> believes_holds(pre, m),
{
}


/// The whole Raymond invariant survives any step that does not move the
/// privilege, provided the per-node maps keep their entries and nobody enters a
/// critical section without believing it holds the privilege.
pub proof fn lemma_ray_frame_inv(pre: Raymond, post: Raymond)
    requires
        ray_inv(pre),
        post.nodes == pre.nodes,
        post.holder == pre.holder,
        post.privilege == pre.privilege,
        forall|m: Id|
            #[trigger] pre.nodes.contains(m) ==> post.queue.contains_key(m)
                && post.asked.contains_key(m) && post.using.contains_key(m),
        forall|m: Id|
            #[trigger] pre.nodes.contains(m) && post.using[m] ==> believes_holds(pre, m),
    ensures
        ray_inv(post),
{
    lemma_same_holder_same_token(pre, post);
    lemma_frame_acyclic(pre, post);
    // Split exactly as `ray_maps_total` / `ray_holder_closed` are split. An
    // `assert forall` introduces a quantified fact with the trigger written
    // here, so proving both halves in one block would reintroduce the matching
    // loop locally: the conclusion `post.nodes.contains(post.holder[m])` would
    // match this block's own `post.nodes.contains(m)` trigger at `post.holder[m]`.
    assert forall|m: Id| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m)
        && post.using.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: Id| post.nodes.contains(m) implies post.nodes.contains(
        #[trigger] post.holder[m],
    ) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: Id| #[trigger] has_token(post, m) implies believes_holds(post, m) by {
        assert(has_token(pre, m));
    }
    assert forall|m: Id| #[trigger] post.nodes.contains(m) && post.using[m]
        implies believes_holds(post, m) by {
        assert(pre.nodes.contains(m));
        assert(believes_holds(pre, m));
    }
}

/// Acyclicity survives any step that leaves `nodes` and `holder` alone: the
/// same rank still works.
pub proof fn lemma_frame_acyclic(pre: Raymond, post: Raymond)
    requires
        ray_acyclic(pre),
        post.nodes == pre.nodes,
        post.holder == pre.holder,
    ensures
        ray_acyclic(post),
{
    let rank = choose|rank: Map<Id, nat>| ray_ranked_by(pre, rank);
    assert forall|n: Id| #[trigger] post.nodes.contains(n) implies rank.contains_key(n) by {
        assert(pre.nodes.contains(n));
    }
    assert forall|n: Id|
        post.nodes.contains(n) && #[trigger] post.holder[n] != n implies rank[post.holder[n]]
            < rank[n] by {
        assert(pre.nodes.contains(n));
        assert(pre.holder[n] == post.holder[n]);
    }
    assert(ray_ranked_by(post, rank));
}

/// **Reversing the edge at the root keeps the tree a tree.**
///
/// Both token movers rewrite exactly the same two pointers -
/// `holder[from] := to` and `holder[to] := to` - so one lemma serves
/// `ray_assign_privilege` and `ray_seize` alike. Note what it does *not* need:
/// no assumption that `to` was a child of `from`, and no assumption about where
/// the token was. Reversing the pointer at any node and rooting the result at
/// the target is acyclicity-preserving on its own.
///
/// The new rank is the old one shifted up by one with `to` sent to zero:
///
/// * `to` is now a root, so it is unconstrained;
/// * every edge that now points at `to` decreases, because nothing else has
///   rank zero - this covers `from`'s new edge and any node that already
///   pointed at `to`;
/// * every other edge is unchanged and both its ends moved up together, so its
///   strict decrease comes straight from the old rank.
pub proof fn lemma_repoint_acyclic(pre: Raymond, post: Raymond, from: Id, to: Id)
    requires
        ray_wf(pre),
        ray_acyclic(pre),
        // The new root has to be a real node: the rank is defined on `nodes`,
        // and rewriting a pointer to something outside them would not leave a
        // tree over the nodes at all. Both callers guard it -
        // `ray_assign_privilege` requires `pre.nodes.contains(head)` and
        // `ray_seize` requires `pre.nodes.contains(to)`.
        pre.nodes.contains(to),
        post.nodes == pre.nodes,
        post.holder == pre.holder.insert(from, to).insert(to, to),
    ensures
        ray_acyclic(post),
{
    let rank = choose|rank: Map<Id, nat>| ray_ranked_by(pre, rank);
    // Defined exactly on the nodes, which is where `ray_ranked_by` asks for it.
    // `ray_wf`'s holder-closedness is what makes every parent's rank land inside
    // that domain.
    let rank2 = Map::new(
        post.nodes,
        |k: Id| if k == to { 0nat } else { (rank[k] + 1) as nat },
    );
    assert(post.holder[to] == to);
    assert(post.holder[from] == to);
    assert(rank2[to] == 0nat);
    assert(rank2.dom() == post.nodes);
    assert forall|n: Id| #[trigger] post.nodes.contains(n) implies rank2.contains_key(n) by {
    }
    assert forall|n: Id|
        post.nodes.contains(n) && #[trigger] post.holder[n] != n implies rank2[post.holder[n]]
            < rank2[n] by {
        assert(n != to);
        assert(rank2[n] == (rank[n] + 1) as nat);
        if post.holder[n] == to {
            assert(post.nodes.contains(to));
            assert(rank2[to] == 0nat);
        } else {
            assert(n != from);
            assert(post.holder[n] == pre.holder[n]);
            assert(pre.nodes.contains(n));
            // Holder-closedness: the parent is a node, so `rank2` is defined on
            // it.
            assert(pre.nodes.contains(pre.holder[n]));
            assert(pre.holder[n] != n);
            assert(rank.contains_key(n));
            assert(rank[pre.holder[n]] < rank[n]);
            assert(rank2[pre.holder[n]] == (rank[pre.holder[n]] + 1) as nat);
        }
    }
    assert(ray_ranked_by(post, rank2));
}

/// One more hop from `n` is the same as one fewer hop from `n`'s parent.
pub proof fn lemma_holder_iter_shift(r: Raymond, n: Id, k: nat)
    ensures
        holder_iter(r, n, (k + 1) as nat) == holder_iter(r, r.holder[n], k),
    decreases k,
{
    // Each `assert` is one unfolding of `holder_iter` at a concrete argument,
    // which is what the default fuel of 1 permits; the induction supplies the
    // step between them.
    if k == 0 {
        assert(holder_iter(r, n, 0nat) == n);
        assert(holder_iter(r, n, 1nat) == r.holder[holder_iter(r, n, 0nat)]);
        assert(holder_iter(r, r.holder[n], 0nat) == r.holder[n]);
    } else {
        lemma_holder_iter_shift(r, n, (k - 1) as nat);
        assert(holder_iter(r, n, k) == holder_iter(r, r.holder[n], (k - 1) as nat));
        assert(holder_iter(r, n, (k + 1) as nat) == r.holder[holder_iter(r, n, k)]);
        assert(holder_iter(r, r.holder[n], k) == r.holder[holder_iter(
            r,
            r.holder[n],
            (k - 1) as nat,
        )]);
    }
}

/// Following belief from any node reaches a node that believes it holds the
/// privilege, by induction on the rank.
proof fn lemma_reaches_token_from(r: Raymond, rank: Map<Id, nat>, n: Id) -> (k: nat)
    requires
        ray_wf(r),
        ray_ranked_by(r, rank),
        r.nodes.contains(n),
    ensures
        believes_holds(r, holder_iter(r, n, k)),
    decreases rank[n],
{
    if r.holder[n] == n {
        assert(holder_iter(r, n, 0nat) == n);
        assert(believes_holds(r, n));
        0nat
    } else {
        let m = r.holder[n];
        // `ray_holder_closed` - the parent is a real node.
        assert(r.nodes.contains(m));
        // `ray_ranked_by` - and it is strictly closer to a root, which is what
        // makes this recursion terminate.
        assert(rank[m] < rank[n]);
        let j = lemma_reaches_token_from(r, rank, m);
        lemma_holder_iter_shift(r, n, j);
        assert(holder_iter(r, n, (j + 1) as nat) == holder_iter(r, m, j));
        (j + 1) as nat
    }
}

/// **Every node reaches the privilege holder by following holder pointers** -
/// as long as nobody's belief is stale.
///
/// This is what turns this module's opening claim, "requests travel hop-by-hop
/// towards the token", into something checked. Two hypotheses carry it, and
/// both are load-bearing. Acyclicity says the walk terminates rather than
/// circling; `ray_no_stale_holders` says the node it terminates at is the real
/// holder rather than somebody who merely thinks so.
///
/// The second was free before, because authority was *defined* as believing.
/// It is not free now, and it should not be: after a seizure a node whose
/// belief-path leads to the seized holder genuinely cannot route to the
/// privilege, and no amount of proving will make it. That is the routing damage
/// a seizure does, and reconciliation - [`lemma_reconcile_preserves_inv`] - is
/// what repairs it.
///
/// It is still a *safety* property, not liveness: the route exists in the
/// current state, not that any request traverses it.
pub proof fn theorem_every_node_reaches_the_token(r: Raymond, n: Id) -> (k: nat)
    requires
        ray_inv(r),
        ray_no_stale_holders(r),
        r.nodes.contains(n),
    ensures
        has_token(r, holder_iter(r, n, k)),
{
    let rank = choose|rank: Map<Id, nat>| ray_ranked_by(r, rank);
    let k = lemma_reaches_token_from(r, rank, n);
    assert(believes_holds(r, holder_iter(r, n, k)));
    assert(has_token(r, holder_iter(r, n, k)));
    k
}

/// Exactly which holder pointers `AssignPrivilege` rewrites.
pub proof fn lemma_assign_holder_pointers(pre: Raymond, post: Raymond, n: Id, head: Id)
    requires
        ray_assign_privilege(pre, post, n, head),
    ensures
        post.holder[head] == head,
        post.holder[n] == head,
        post.holder.contains_key(head),
        post.holder.contains_key(n),
        forall|m: Id| m != n && m != head ==> #[trigger] post.holder[m] == pre.holder[m],
        forall|m: Id|
            m != n && m != head ==> (#[trigger] post.holder.contains_key(m)
                <==> pre.holder.contains_key(m)),
{
}

/// The privilege moves from `n` to `head`, and belief moves with it.
pub proof fn lemma_assign_token_moves(pre: Raymond, post: Raymond, n: Id, head: Id)
    requires
        ray_inv(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        has_token(post, head),
        believes_holds(post, head),
        !has_token(post, n),
        !believes_holds(post, n),
        forall|m: Id| #[trigger] has_token(post, m) ==> m == head,
{
    lemma_assign_holder_pointers(pre, post, n, head);
    assert(post.privilege == head);
    assert(post.holder[head] == head);
    assert(post.holder[n] == head);
    assert(head != n);
}

/// `AssignPrivilege` keeps every node's maps well formed.
pub proof fn lemma_assign_wf(pre: Raymond, post: Raymond, n: Id, head: Id)
    requires
        ray_wf(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        ray_wf(post),
{
    lemma_assign_holder_pointers(pre, post, n, head);
    assert(post.nodes.contains(post.privilege));
    assert forall|m: Id| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m)
        && post.using.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: Id| post.nodes.contains(m) implies post.nodes.contains(
        #[trigger] post.holder[m],
    ) by {
        assert(pre.nodes.contains(m));
        if m == head || m == n {
            assert(post.holder[m] == head);
            assert(pre.nodes.contains(head));
        } else {
            assert(post.holder[m] == pre.holder[m]);
        }
    }
}

/// Nobody is in the critical section when the privilege is passed on, so
/// `ray_using_implies_belief` survives the move vacuously.
///
/// This is where a voluntary handover differs from a seizure. `n` is guarded on
/// `!pre.using[n]`, and `ray_inv` says only believers are in a critical
/// section, so the only node whose belief this step revokes was not using it.
pub proof fn lemma_assign_using(pre: Raymond, post: Raymond, n: Id, head: Id)
    requires
        ray_inv(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        ray_using_implies_belief(post),
{
    lemma_assign_holder_pointers(pre, post, n, head);
    assert forall|m: Id| #[trigger] post.nodes.contains(m) && post.using[m]
        implies believes_holds(post, m) by {
        assert(pre.nodes.contains(m));
        assert(pre.using[m]);
        assert(believes_holds(pre, m));
        if m == n {
            assert(!pre.using[n]);
            assert(false);
        } else if m == head {
            assert(post.holder[head] == head);
        } else {
            assert(post.holder[m] == pre.holder[m]);
        }
    }
}

/// **A request outlives the topology it was routed against.**
///
/// After the token moves, `from`'s holder pointer no longer points at `at` and
/// `from`'s `asked` flag may have been cleared - but the request itself is still
/// in `requests`, so it is still deliverable. This is the adversarial case a
/// model that guarded on the live holder pointer could not express at all.
pub proof fn theorem_delayed_request_survives_token_move(
    pre: Raymond,
    mid: Raymond,
    n: Id,
    head: Id,
    at: Id,
    from: Id,
)
    requires
        ray_assign_privilege(pre, mid, n, head),
        pre.nodes.contains(at),
        pre.nodes.contains(from),
        pre.requests.contains((from, at)),
    ensures
        mid.nodes.contains(at),
        mid.nodes.contains(from),
        mid.requests.contains((from, at)),
{
}

/// **Delivering an arbitrarily delayed request is safe.**
///
/// Whenever such a request is delivered - however late, however many times - the
/// Raymond invariant survives and token possession is completely unchanged.
pub proof fn theorem_delayed_request_delivery_is_safe(
    pre: Raymond,
    post: Raymond,
    at: Id,
    from: Id,
)
    requires
        ray_inv(pre),
        ray_receive_request(pre, post, at, from),
    ensures
        ray_inv(post),
        forall|m: Id| #[trigger] has_token(post, m) <==> has_token(pre, m),
{
    lemma_ray_step_preserves_inv(pre, post, RayStep::ReceiveRequest { at: at, from: from });
    lemma_routing_preserves_holder(pre, post, RayStep::ReceiveRequest { at: at, from: from });
}

/// Passing the privilege on preserves the Raymond invariant, and leaves `head`
/// holding it and believing so.
pub proof fn lemma_assign_privilege_preserves_unique_token(
    pre: Raymond,
    post: Raymond,
    n: Id,
    head: Id,
)
    requires
        ray_inv(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        ray_inv(post),
        has_token(post, head),
        !has_token(post, n),
        forall|m: Id| #[trigger] has_token(post, m) ==> m == head,
{
    lemma_assign_token_moves(pre, post, n, head);
    lemma_assign_wf(pre, post, n, head);
    lemma_assign_using(pre, post, n, head);
    lemma_repoint_acyclic(pre, post, n, head);
    lemma_assign_holder_pointers(pre, post, n, head);
    assert forall|m: Id| #[trigger] has_token(post, m) implies believes_holds(post, m) by {
        assert(m == head);
    }
}

// ---------------------------------------------------------------------------
// Seizure
// ---------------------------------------------------------------------------
//
// These mirror the `assign` family above. `ray_seize` rewrites the same two
// holder pointers as `ray_assign_privilege`, so the token-uniqueness argument
// is identical; the differences are that it does not touch the queue and that
// it clears `using[from]` instead of requiring it to be false.





/// **A seizure preserves the Raymond invariant and leaves `to` holding the one
/// privilege** - without touching anything belonging to `from`.
///
/// Shorter than the handover case, and the reason is the point of the split.
/// Moving authority is now a single assignment to `privilege`; uniqueness is
/// structural, so there is nothing to re-establish. What the step *does* create
/// is a stale holder, and the invariant tolerates one by construction:
/// `ray_authority_believes` constrains the holder's belief, not everyone's, and
/// `ray_using_implies_belief` is untroubled by a node that both believes and is
/// using.
pub proof fn lemma_seize_preserves_inv(pre: Raymond, post: Raymond, from: Id, to: Id)
    requires
        ray_inv(pre),
        ray_seize(pre, post, from, to),
    ensures
        ray_inv(post),
        has_token(post, to),
        believes_holds(post, to),
        !has_token(post, from),
        forall|m: Id| #[trigger] has_token(post, m) ==> m == to,
        // The state the old model could not write down.
        is_stale_holder(post, from),
{
    assert(post.privilege == to);
    assert(post.holder[to] == to);
    assert(believes_holds(pre, from));
    assert(post.holder[from] == pre.holder[from]);
    assert(is_stale_holder(post, from));
    // Well-formedness.
    assert(post.nodes.contains(post.privilege));
    assert forall|m: Id| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m)
        && post.using.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: Id| post.nodes.contains(m) implies post.nodes.contains(
        #[trigger] post.holder[m],
    ) by {
        assert(pre.nodes.contains(m));
        if m == to {
            assert(post.holder[m] == to);
        } else {
            assert(post.holder[m] == pre.holder[m]);
        }
    }
    assert forall|m: Id| #[trigger] has_token(post, m) implies believes_holds(post, m) by {
        assert(m == to);
    }
    assert forall|m: Id| #[trigger] post.nodes.contains(m) && post.using[m]
        implies believes_holds(post, m) by {
        assert(pre.nodes.contains(m));
        assert(pre.using[m]);
        assert(believes_holds(pre, m));
        if m != to {
            assert(post.holder[m] == pre.holder[m]);
        }
    }
    // Acyclicity: the step only makes `to` point at itself, which *removes* a
    // constraint from the ranking, so the old rank still witnesses it.
    let rank = choose|rank: Map<Id, nat>| ray_ranked_by(pre, rank);
    assert forall|m: Id| #[trigger] post.nodes.contains(m) implies rank.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: Id|
        post.nodes.contains(m) && #[trigger] post.holder[m] != m implies rank[post.holder[m]]
            < rank[m] by {
        assert(m != to);
        assert(post.holder[m] == pre.holder[m]);
        assert(pre.nodes.contains(m));
    }
    assert(ray_ranked_by(post, rank));
}

/// **A stale holder confers no authority.**
///
/// The routing counterpart of `theorem_stale_token_confers_no_authority`, and
/// the reason a seizure need not reach into the crashed node. `couples` is
/// written against `has_token` - actual possession of the privilege - so a node
/// that merely believes cannot be permitted to mutate, however firmly it
/// believes and whatever it is doing in its critical section meanwhile.
///
/// This is what survives imperfect failure detection. It does not depend on the
/// seized node being crashed, or on anything having cleared its state.
pub proof fn theorem_stale_holder_confers_no_authority(
    r: Raymond,
    own: OwnershipState,
    n: Id,
    e: Epoch,
)
    requires
        couples(r, own),
        is_stale_holder(r, n),
    ensures
        !may_mutate(own, n, e),
{
    if may_mutate(own, n, e) {
        assert(has_token(r, n));
        assert(false);
    }
}

/// **Reconciliation drops the stale belief**, and preserves the invariant.
///
/// The node acts on its own state here, which is what makes this step
/// implementable where editing it from outside was not.
///
/// Acyclicity comes straight from [`lemma_repoint_acyclic`]: re-pointing `n` at
/// the privilege holder is the same rewrite as a seizure that moves the
/// privilege to a node already believing it holds it, and the holder does
/// already believe - that is `ray_authority_believes`.
pub proof fn lemma_reconcile_preserves_inv(pre: Raymond, post: Raymond, n: Id)
    requires
        ray_inv(pre),
        ray_reconcile(pre, post, n),
    ensures
        ray_inv(post),
        !believes_holds(post, n),
        !post.using[n],
        has_token(post, pre.privilege),
{
    let priv_node = pre.privilege;
    assert(has_token(pre, priv_node));
    assert(believes_holds(pre, priv_node));
    assert(pre.holder[priv_node] == priv_node);
    assert(n != priv_node);
    assert(post.holder[n] == priv_node);
    assert(!believes_holds(post, n));
    assert(post.nodes.contains(post.privilege));

    assert forall|m: Id| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m)
        && post.using.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: Id| post.nodes.contains(m) implies post.nodes.contains(
        #[trigger] post.holder[m],
    ) by {
        assert(pre.nodes.contains(m));
        if m == n {
            assert(post.holder[m] == priv_node);
        } else {
            assert(post.holder[m] == pre.holder[m]);
        }
    }
    assert forall|m: Id| #[trigger] has_token(post, m) implies believes_holds(post, m) by {
        assert(m == priv_node);
        assert(post.holder[priv_node] == pre.holder[priv_node]);
    }
    assert forall|m: Id| #[trigger] post.nodes.contains(m) && post.using[m]
        implies believes_holds(post, m) by {
        assert(m != n);
        assert(post.using[m] == pre.using[m]);
        assert(pre.nodes.contains(m));
        assert(believes_holds(pre, m));
        assert(post.holder[m] == pre.holder[m]);
    }

    // `holder.insert(n, priv)` and `holder.insert(n, priv).insert(priv, priv)`
    // agree, because the holder already believes.
    assert(post.holder =~= pre.holder.insert(n, priv_node).insert(priv_node, priv_node));
    lemma_repoint_acyclic(pre, post, n, priv_node);
}

/// A one-state labelled run.
pub proof fn lemma_ray_run_init(r: Raymond)
    ensures
        ray_run(seq![r], Seq::<RayStep>::empty()),
{
    let tr = seq![r];
    let labels = Seq::<RayStep>::empty();
    assert(tr.len() == 1);
    assert(labels.len() == 0);
}

/// A labelled run extends by one **named** transition.
pub proof fn lemma_ray_run_push(
    tr: Seq<Raymond>,
    labels: Seq<RayStep>,
    post: Raymond,
    s: RayStep,
)
    requires
        ray_run(tr, labels),
        ray_step(tr[tr.len() - 1], post, s),
    ensures
        ray_run(tr.push(post), labels.push(s)),
        tr.push(post).len() == tr.len() + 1,
        labels.push(s).len() == labels.len() + 1,
        tr.push(post)[tr.len() as int] == post,
        labels.push(s)[labels.len() as int] == s,
        forall|i: int| 0 <= i < tr.len() ==> #[trigger] tr.push(post)[i] == tr[i],
        forall|i: int| 0 <= i < labels.len() ==> #[trigger] labels.push(s)[i] == labels[i],
{
    let tr2 = tr.push(post);
    let l2 = labels.push(s);
    assert(tr2.len() == tr.len() + 1);
    assert(l2.len() == labels.len() + 1);
    assert forall|i: int|
        #![trigger tr2[i], tr2[i + 1], l2[i]]
        0 <= i < l2.len() implies ray_step(tr2[i], tr2[i + 1], l2[i]) by {
        if i < labels.len() {
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == tr[i + 1]);
            assert(l2[i] == labels[i]);
            assert(ray_step(tr[i], tr[i + 1], labels[i]));
        } else {
            assert(i == labels.len());
            assert(i == tr.len() - 1);
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == post);
            assert(l2[i] == s);
        }
    }
}

/// **A labelled run is a run.** Exporting the labels loses nothing: the
/// unlabelled `ray_segment` and `ray_reachable_from` follow from it.
pub proof fn lemma_ray_run_is_segment(tr: Seq<Raymond>, labels: Seq<RayStep>)
    requires
        ray_run(tr, labels),
    ensures
        ray_segment(tr),
        ray_reachable_from(tr[0], tr[tr.len() - 1]),
{
    assert forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 implies ray_next(tr[i], tr[i + 1]) by {
        assert(ray_step(tr[i], tr[i + 1], labels[i]));
    }
    assert(ray_segment(tr));
}

/// Every state of a labelled run whose first state satisfies the Raymond
/// invariant satisfies it too.
pub proof fn lemma_ray_run_inv(tr: Seq<Raymond>, labels: Seq<RayStep>, i: int)
    requires
        ray_run(tr, labels),
        ray_inv(tr[0]),
        0 <= i < tr.len(),
    ensures
        ray_inv(tr[i]),
    decreases i,
{
    if i > 0 {
        let j = i - 1;
        lemma_ray_run_inv(tr, labels, j);
        assert(ray_step(tr[j], tr[j + 1], labels[j]));
        lemma_ray_step_preserves_inv(tr[j], tr[j + 1], labels[j]);
    }
}

/// Every Raymond transition preserves the Raymond invariant.
pub proof fn lemma_ray_step_preserves_inv(pre: Raymond, post: Raymond, s: RayStep)
    requires
        ray_inv(pre),
        ray_step(pre, post, s),
    ensures
        ray_inv(post),
{
    match s {
        RayStep::AssignPrivilege { node, head } => {
            lemma_assign_privilege_preserves_unique_token(pre, post, node, head);
        },
        RayStep::EnterCs { node } => {
            assert forall|m: Id| #[trigger] pre.nodes.contains(m) && post.using[m]
                implies believes_holds(pre, m) by {
                if m == node {
                    assert(believes_holds(pre, node));
                } else {
                    assert(post.using[m] == pre.using[m]);
                }
            }
            lemma_ray_frame_inv(pre, post);
        },
        RayStep::ExitCs { node } => {
            assert forall|m: Id| #[trigger] pre.nodes.contains(m) && post.using[m]
                implies believes_holds(pre, m) by {
                assert(m != node);
                assert(post.using[m] == pre.using[m]);
            }
            lemma_ray_frame_inv(pre, post);
        },
        RayStep::RequestCs { node } => {
            lemma_ray_frame_inv(pre, post);
        },
        RayStep::MakeRequest { node } => {
            lemma_ray_frame_inv(pre, post);
        },
        RayStep::ReceiveRequest { at, from } => {
            lemma_ray_frame_inv(pre, post);
        },
    }
}

/// **At most one node holds the privilege.** Structural now: `privilege` is a
/// single node id, so this needs no invariant at all. It used to be an
/// inductive invariant, and it used to be the reason a returning stale holder
/// was unrepresentable.
pub proof fn theorem_ray_at_most_one_token(r: Raymond, n: Id, m: Id)
    requires
        has_token(r, n),
        has_token(r, m),
    ensures
        n == m,
{
}

/// The initial routing state has the privilege.
pub proof fn lemma_ray_token_exists_init(r: Raymond, root: Id)
    requires
        ray_init(r, root),
    ensures
        ray_token_exists(r),
{
    assert(has_token(r, root));
}

/// **The privilege is never lost.** Every Raymond transition leaves
/// `privilege` pointing at a node: the token-preserving steps do not touch it,
/// and the transfer hands it to `head` in the same step that takes it from `n`.
pub proof fn lemma_ray_token_exists_step(pre: Raymond, post: Raymond, s: RayStep)
    requires
        ray_inv(pre),
        ray_step(pre, post, s),
    ensures
        ray_token_exists(post),
{
    match s {
        RayStep::AssignPrivilege { node, head } => {
            lemma_assign_token_moves(pre, post, node, head);
            assert(has_token(post, head));
        },
        _ => {
            lemma_token_preserving_steps_keep_holder(pre, post, s);
            assert(has_token(post, pre.privilege));
        },
    }
}

/// **Exactly one privilege.** In any well-formed state there is a holder, and
/// it is unique.
pub proof fn theorem_ray_exactly_one_token(r: Raymond)
    requires
        ray_inv(r),
    ensures
        exists|n: Id| #[trigger] has_token(r, n),
        forall|n: Id, m: Id| has_token(r, n) && has_token(r, m) ==> n == m,
{
    assert(has_token(r, r.privilege));
    assert forall|n: Id, m: Id| has_token(r, n) && has_token(r, m) implies n == m by {
        theorem_ray_at_most_one_token(r, n, m);
    }
}

/// **Raymond critical sections are exclusive - while nobody's belief is
/// stale.**
///
/// The extra hypothesis is not a weakening of the algorithm; it is the
/// algorithm's actual scope becoming visible. Raymond's mutual exclusion rests
/// on there being one privilege and every node agreeing where it is. A seizure
/// breaks the agreement, and until the seized node reconciles, two nodes can be
/// inside their critical sections: the stale holder, which never learned, and
/// the new holder.
///
/// That window is real in any deployment that takes a privilege away from a
/// node it cannot reach, and this model now says so rather than hiding it by
/// editing the absent node's state. What does *not* break in that window is
/// ownership safety - see
/// [`theorem_stale_holder_confers_no_authority`].
pub proof fn theorem_ray_critical_section_is_exclusive(r: Raymond, n: Id, m: Id)
    requires
        ray_inv(r),
        ray_no_stale_holders(r),
        r.nodes.contains(n),
        r.nodes.contains(m),
        r.using[n],
        r.using[m],
    ensures
        n == m,
{
    assert(believes_holds(r, n));
    assert(believes_holds(r, m));
    assert(has_token(r, n));
    assert(has_token(r, m));
    theorem_ray_at_most_one_token(r, n, m);
}

/// **At most one node is authorised to be in its critical section**, with no
/// side conditions at all: the authorised occupant is the privilege holder, and
/// there is one of those by construction.
///
/// This is the part of Raymond's exclusivity that survives a seizure, stated
/// separately from the part that does not.
pub proof fn theorem_authorised_critical_section_is_exclusive(
    r: Raymond,
    n: Id,
    m: Id,
)
    requires
        ray_inv(r),
        r.using[n] && has_token(r, n),
        r.using[m] && has_token(r, m),
    ensures
        n == m,
{
    theorem_ray_at_most_one_token(r, n, m);
}

/// **Privilege transfer preserves ownership safety.**
///
/// The privilege may only be passed on while the ownership layer is *not*
/// `Owned` - that is, after the actor has been released. Under that condition
/// the coupling survives the transfer, so afterwards still at most one node can
/// possibly hold authority, and it is the new holder.
pub proof fn theorem_token_transfer_preserves_ownership_safety(
    pre: Raymond,
    post: Raymond,
    n: Id,
    head: Id,
    own: OwnershipState,
)
    requires
        ray_inv(pre),
        ray_assign_privilege(pre, post, n, head),
        !is_owned(own),
        couples(pre, own),
    ensures
        ray_inv(post),
        couples(post, own),
        has_token(post, head),
        forall|m: Id| has_token(post, m) ==> m == head,
{
    lemma_assign_privilege_preserves_unique_token(pre, post, n, head);
    assert forall|m: Id, e: Epoch| may_mutate(own, m, e) implies has_token(post, m) by {
        assert(!is_owned(own));
        assert(false);
    }
}

/// Taking ownership while holding the privilege establishes the coupling: the
/// only node that can mutate is exactly the privilege holder.
pub proof fn theorem_acquire_under_token_establishes_coupling(r: Raymond, n: Id, e: Epoch)
    requires
        has_token(r, n),
    ensures
        couples(r, OwnershipState::Owned { owner: n, epoch: e }),
{
    assert forall|m: Id, x: Epoch|
        may_mutate(OwnershipState::Owned { owner: n, epoch: e }, m, x) implies has_token(r, m) by {
        assert(m == n);
    }
}

/// **The composed safety property.** Under the coupling, two nodes permitted to
/// mutate the actor are the same node, and that node actually holds the
/// privilege - not merely believes it does.
pub proof fn theorem_coupled_exclusivity(
    r: Raymond,
    own: OwnershipState,
    n1: Id,
    e1: Epoch,
    n2: Id,
    e2: Epoch,
)
    requires
        couples(r, own),
        may_mutate(own, n1, e1),
        may_mutate(own, n2, e2),
    ensures
        n1 == n2,
        e1 == e2,
        has_token(r, n1),
{
    lemma_exclusive_owner(own, n1, e1, n2, e2);
}

} // verus!
