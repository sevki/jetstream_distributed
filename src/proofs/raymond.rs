//! **Claim 7 - the Raymond routing layer.**
//!
//! * there is at most one valid token;
//! * token transfer preserves ownership safety;
//! * holder/routing changes cannot manufacture ownership;
//! * duplicate/reordered requests cannot create a second owner.
//!
//! Liveness is *not* claimed. See `README.md`.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::raymond::*;

verus! {

/// The initial routing state satisfies the Raymond invariant.
pub proof fn theorem_ray_init_inv(r: Raymond, root: NodeId)
    requires
        ray_init(r, root),
    ensures
        ray_inv(r),
        has_token(r, root),
{
    assert(has_token(r, root));
    assert(ray_token_exists(r));
    assert forall|n: NodeId, m: NodeId| has_token(r, n) && has_token(r, m) implies n == m by {
        if n != root {
            assert(r.holder[n] != n);
            assert(false);
        }
        if m != root {
            assert(r.holder[m] != m);
            assert(false);
        }
    }
}

/// Request routing never moves the token: `holder` is untouched by
/// `RequestCs`, `MakeRequest` and `ReceiveRequest`.
pub proof fn lemma_routing_preserves_holder(pre: Raymond, post: Raymond, s: RayStep)
    requires
        ray_step(pre, post, s),
        is_routing_step(s),
    ensures
        post.holder == pre.holder,
        post.nodes == pre.nodes,
        forall|n: NodeId| #[trigger] has_token(post, n) <==> has_token(pre, n),
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

/// Every step except the token transfer leaves `holder` - and therefore token
/// possession - completely alone. This covers critical-section bookkeeping as
/// well as request routing.
pub proof fn lemma_token_preserving_steps_keep_holder(pre: Raymond, post: Raymond, s: RayStep)
    requires
        ray_step(pre, post, s),
        preserves_token(s),
    ensures
        post.holder == pre.holder,
        post.nodes == pre.nodes,
        forall|n: NodeId| #[trigger] has_token(post, n) <==> has_token(pre, n),
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
        forall|n: NodeId| #[trigger] has_token(post, n) <==> has_token(pre, n),
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
    at: NodeId,
    from: NodeId,
)
    requires
        ray_inv(pre),
        ray_receive_request(pre, mid, at, from),
        ray_receive_request(mid, post, at, from),
    ensures
        ray_inv(post),
        forall|n: NodeId| #[trigger] has_token(post, n) <==> has_token(pre, n),
{
    lemma_ray_step_preserves_inv(pre, mid, RayStep::ReceiveRequest { at: at, from: from });
    lemma_ray_step_preserves_inv(mid, post, RayStep::ReceiveRequest { at: at, from: from });
}

/// A step that leaves `nodes` and `holder` alone leaves token possession alone.
///
/// Stated explicitly so that the `has_token(pre, _)` terms exist for the SMT
/// solver: `ray_unique_token` triggers on them, and without this lemma the
/// trigger never fires for framing steps.
pub proof fn lemma_same_holder_same_token(pre: Raymond, post: Raymond)
    requires
        post.nodes == pre.nodes,
        post.holder == pre.holder,
    ensures
        forall|m: NodeId| #[trigger] has_token(post, m) <==> has_token(pre, m),
{
}

/// Unique token possession survives any step that does not move the token.
pub proof fn lemma_frame_unique_token(pre: Raymond, post: Raymond)
    requires
        ray_unique_token(pre),
        post.nodes == pre.nodes,
        post.holder == pre.holder,
    ensures
        ray_unique_token(post),
{
    lemma_same_holder_same_token(pre, post);
    assert forall|x: NodeId, y: NodeId|
        #![trigger has_token(post, x), has_token(post, y)]
        has_token(post, x) && has_token(post, y) implies x == y by {
        assert(has_token(pre, x));
        assert(has_token(pre, y));
    }
}

/// The whole Raymond invariant survives any step that does not move the token,
/// provided the per-node maps keep their entries and nobody enters the critical
/// section without the token.
pub proof fn lemma_ray_frame_inv(pre: Raymond, post: Raymond)
    requires
        ray_inv(pre),
        post.nodes == pre.nodes,
        post.holder == pre.holder,
        forall|m: NodeId|
            #[trigger] pre.nodes.contains(m) ==> post.queue.contains_key(m)
                && post.asked.contains_key(m) && post.using.contains_key(m),
        forall|m: NodeId| #[trigger] pre.nodes.contains(m) && post.using[m] ==> has_token(pre, m),
    ensures
        ray_inv(post),
{
    lemma_same_holder_same_token(pre, post);
    lemma_frame_unique_token(pre, post);
    let root = choose|n: NodeId| has_token(pre, n);
    assert(has_token(post, root));
    assert(ray_token_exists(post));
    // Split exactly as `ray_maps_total` / `ray_holder_closed` are split. An
    // `assert forall` introduces a quantified fact with the trigger written
    // here, so proving both halves in one block would reintroduce the matching
    // loop locally: the conclusion `post.nodes.contains(post.holder[m])` would
    // match this block's own `post.nodes.contains(m)` trigger at `post.holder[m]`.
    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m)
        && post.using.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: NodeId| post.nodes.contains(m) implies post.nodes.contains(
        #[trigger] post.holder[m],
    ) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) && post.using[m] implies has_token(
        post,
        m,
    ) by {
        assert(pre.nodes.contains(m));
        assert(has_token(pre, m));
    }
}

/// Exactly which holder pointers `AssignPrivilege` rewrites.
pub proof fn lemma_assign_holder_pointers(pre: Raymond, post: Raymond, n: NodeId, head: NodeId)
    requires
        ray_assign_privilege(pre, post, n, head),
    ensures
        post.holder[head] == head,
        post.holder[n] == head,
        post.holder.contains_key(head),
        post.holder.contains_key(n),
        forall|m: NodeId| m != n && m != head ==> #[trigger] post.holder[m] == pre.holder[m],
        forall|m: NodeId|
            m != n && m != head ==> (#[trigger] post.holder.contains_key(m)
                <==> pre.holder.contains_key(m)),
{
}

/// The token moves from `n` to `head`, and stays unique while it does.
pub proof fn lemma_assign_token_moves(pre: Raymond, post: Raymond, n: NodeId, head: NodeId)
    requires
        ray_inv(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        has_token(post, head),
        !has_token(post, n),
        forall|m: NodeId| #[trigger] has_token(post, m) ==> m == head,
        ray_unique_token(post),
{
    lemma_assign_holder_pointers(pre, post, n, head);
    assert(has_token(pre, n));
    assert(has_token(post, head));
    assert(!has_token(post, n));
    assert forall|m: NodeId| #[trigger] has_token(post, m) implies m == head by {
        if m != head {
            assert(m != n);
            assert(post.holder[m] == pre.holder[m]);
            assert(pre.holder.contains_key(m));
            assert(has_token(pre, m));
            assert(has_token(pre, n));
            assert(m == n);
            assert(false);
        }
    }
    assert forall|x: NodeId, y: NodeId|
        #![trigger has_token(post, x), has_token(post, y)]
        has_token(post, x) && has_token(post, y) implies x == y by {
    }
}

/// `AssignPrivilege` keeps every node's maps well formed.
pub proof fn lemma_assign_wf(pre: Raymond, post: Raymond, n: NodeId, head: NodeId)
    requires
        ray_wf(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        ray_wf(post),
{
    lemma_assign_holder_pointers(pre, post, n, head);
    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m)
        && post.using.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: NodeId| post.nodes.contains(m) implies post.nodes.contains(
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

/// Nobody is in the critical section when the token is passed on, so
/// `ray_using_implies_token` survives the move vacuously.
pub proof fn lemma_assign_using(pre: Raymond, post: Raymond, n: NodeId, head: NodeId)
    requires
        ray_inv(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        ray_using_implies_token(post),
{
    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) && post.using[m] implies has_token(
        post,
        m,
    ) by {
        assert(pre.nodes.contains(m));
        assert(pre.using[m]);
        assert(has_token(pre, m));
        assert(has_token(pre, n));
        assert(m == n);
        assert(!pre.using[n]);
        assert(false);
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
    n: NodeId,
    head: NodeId,
    at: NodeId,
    from: NodeId,
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
    at: NodeId,
    from: NodeId,
)
    requires
        ray_inv(pre),
        ray_receive_request(pre, post, at, from),
    ensures
        ray_inv(post),
        forall|m: NodeId| #[trigger] has_token(post, m) <==> has_token(pre, m),
{
    lemma_ray_step_preserves_inv(pre, post, RayStep::ReceiveRequest { at: at, from: from });
    lemma_routing_preserves_holder(pre, post, RayStep::ReceiveRequest { at: at, from: from });
}

/// Passing the token preserves the "exactly one token" invariant: the old
/// holder stops being a root at the same instant the new holder becomes one.
pub proof fn lemma_assign_privilege_preserves_unique_token(
    pre: Raymond,
    post: Raymond,
    n: NodeId,
    head: NodeId,
)
    requires
        ray_inv(pre),
        ray_assign_privilege(pre, post, n, head),
    ensures
        ray_inv(post),
        has_token(post, head),
        !has_token(post, n),
        forall|m: NodeId| #[trigger] has_token(post, m) ==> m == head,
{
    lemma_assign_token_moves(pre, post, n, head);
    lemma_assign_wf(pre, post, n, head);
    lemma_assign_using(pre, post, n, head);
    assert(has_token(post, head));
    assert(ray_token_exists(post));
}

// ---------------------------------------------------------------------------
// Seizure
// ---------------------------------------------------------------------------
//
// These mirror the `assign` family above. `ray_seize` rewrites the same two
// holder pointers as `ray_assign_privilege`, so the token-uniqueness argument
// is identical; the differences are that it does not touch the queue and that
// it clears `using[from]` instead of requiring it to be false.

/// Exactly which holder pointers a seizure rewrites.
pub proof fn lemma_seize_holder_pointers(pre: Raymond, post: Raymond, from: NodeId, to: NodeId)
    requires
        ray_seize(pre, post, from, to),
    ensures
        post.holder[to] == to,
        post.holder[from] == to,
        post.holder.contains_key(to),
        post.holder.contains_key(from),
        forall|m: NodeId| m != from && m != to ==> #[trigger] post.holder[m] == pre.holder[m],
        forall|m: NodeId|
            m != from && m != to ==> (#[trigger] post.holder.contains_key(m)
                <==> pre.holder.contains_key(m)),
{
}

/// The token moves to `to`, and stays unique while it does.
pub proof fn lemma_seize_token_moves(pre: Raymond, post: Raymond, from: NodeId, to: NodeId)
    requires
        ray_inv(pre),
        ray_seize(pre, post, from, to),
    ensures
        has_token(post, to),
        !has_token(post, from),
        forall|m: NodeId| #[trigger] has_token(post, m) ==> m == to,
        ray_unique_token(post),
{
    lemma_seize_holder_pointers(pre, post, from, to);
    assert(has_token(pre, from));
    assert(has_token(post, to));
    assert(!has_token(post, from));
    assert forall|m: NodeId| #[trigger] has_token(post, m) implies m == to by {
        if m != to {
            assert(m != from);
            assert(post.holder[m] == pre.holder[m]);
            assert(pre.holder.contains_key(m));
            assert(has_token(pre, m));
            assert(has_token(pre, from));
            assert(m == from);
            assert(false);
        }
    }
    assert forall|x: NodeId, y: NodeId|
        #![trigger has_token(post, x), has_token(post, y)]
        has_token(post, x) && has_token(post, y) implies x == y by {
    }
}

/// A seizure keeps every node's maps well formed.
pub proof fn lemma_seize_wf(pre: Raymond, post: Raymond, from: NodeId, to: NodeId)
    requires
        ray_wf(pre),
        ray_seize(pre, post, from, to),
    ensures
        ray_wf(post),
{
    lemma_seize_holder_pointers(pre, post, from, to);
    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m)
        && post.using.contains_key(m) by {
        assert(pre.nodes.contains(m));
    }
    assert forall|m: NodeId| post.nodes.contains(m) implies post.nodes.contains(
        #[trigger] post.holder[m],
    ) by {
        assert(pre.nodes.contains(m));
        if m == to || m == from {
            assert(post.holder[m] == to);
            assert(pre.nodes.contains(to));
        } else {
            assert(post.holder[m] == pre.holder[m]);
        }
    }
}

/// The node whose token is seized is no longer in a critical section, and it is
/// the only node that could have been, so `ray_using_implies_token` survives.
pub proof fn lemma_seize_using(pre: Raymond, post: Raymond, from: NodeId, to: NodeId)
    requires
        ray_inv(pre),
        ray_seize(pre, post, from, to),
    ensures
        ray_using_implies_token(post),
{
    lemma_seize_token_moves(pre, post, from, to);
    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) && post.using[m] implies has_token(
        post,
        m,
    ) by {
        assert(pre.nodes.contains(m));
        if m == from {
            assert(post.using[m] == false);
            assert(false);
        } else {
            assert(post.using[m] == pre.using[m]);
            assert(pre.using[m]);
            assert(has_token(pre, m));
            assert(has_token(pre, from));
            assert(m == from);
            assert(false);
        }
    }
}

/// **A seizure preserves the Raymond invariant and leaves `to` holding the one
/// token.** The routing layer cannot end up with two tokens, or none, because
/// the coordinator took one away from a node that was not cooperating.
pub proof fn lemma_seize_preserves_inv(pre: Raymond, post: Raymond, from: NodeId, to: NodeId)
    requires
        ray_inv(pre),
        ray_seize(pre, post, from, to),
    ensures
        ray_inv(post),
        has_token(post, to),
        !has_token(post, from),
        forall|m: NodeId| #[trigger] has_token(post, m) ==> m == to,
{
    lemma_seize_token_moves(pre, post, from, to);
    lemma_seize_wf(pre, post, from, to);
    lemma_seize_using(pre, post, from, to);
    assert(has_token(post, to));
    assert(ray_token_exists(post));
}

/// Every routing state reaches itself.
pub proof fn lemma_ray_reachable_from_refl(r: Raymond)
    ensures
        ray_reachable_from(r, r),
{
    let tr = seq![r];
    assert(tr.len() == 1);
    assert(tr[0] == r);
    assert(tr[tr.len() - 1] == r);
    assert(ray_segment(tr));
}

/// Reachability-from extends by one transition.
pub proof fn lemma_ray_reachable_from_step(pre: Raymond, mid: Raymond, post: Raymond, s: RayStep)
    requires
        ray_reachable_from(pre, mid),
        ray_step(mid, post, s),
    ensures
        ray_reachable_from(pre, post),
{
    let tr = choose|tr: Seq<Raymond>|
        ray_segment(tr) && tr[0] == pre && tr[tr.len() - 1] == mid;
    let tr2 = tr.push(post);
    assert(tr2.len() == tr.len() + 1);
    assert(tr2[0] == tr[0]);
    assert forall|i: int|
        #![trigger tr2[i], tr2[i + 1]]
        0 <= i < tr2.len() - 1 implies ray_next(tr2[i], tr2[i + 1]) by {
        if i < tr.len() - 1 {
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == tr[i + 1]);
            assert(ray_next(tr[i], tr[i + 1]));
        } else {
            assert(i == tr.len() - 1);
            assert(tr2[i] == tr[i]);
            assert(tr2[i + 1] == post);
            assert(ray_step(mid, post, s));
            assert(ray_next(mid, post));
        }
    }
    assert(ray_segment(tr2));
    assert(tr2[tr2.len() - 1] == post);
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
            assert forall|m: NodeId| #[trigger] pre.nodes.contains(m) && post.using[m]
                implies has_token(pre, m) by {
                if m == node {
                    assert(has_token(pre, node));
                } else {
                    assert(post.using[m] == pre.using[m]);
                }
            }
            lemma_ray_frame_inv(pre, post);
        },
        RayStep::ExitCs { node } => {
            assert forall|m: NodeId| #[trigger] pre.nodes.contains(m) && post.using[m]
                implies has_token(pre, m) by {
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

/// **At most one valid token**, in any state reachable by Raymond steps.
pub proof fn theorem_ray_at_most_one_token(r: Raymond, n: NodeId, m: NodeId)
    requires
        ray_inv(r),
        has_token(r, n),
        has_token(r, m),
    ensures
        n == m,
{
}

/// The initial routing state has the token.
pub proof fn lemma_ray_token_exists_init(r: Raymond, root: NodeId)
    requires
        ray_init(r, root),
    ensures
        ray_token_exists(r),
{
    assert(has_token(r, root));
}

/// **The token is never lost.** Every Raymond transition keeps a token in the
/// system: the token-preserving steps leave possession alone, and the transfer
/// hands it to `head` in the same step that takes it from `n`.
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
            let n = choose|n: NodeId| has_token(pre, n);
            assert(has_token(post, n));
        },
    }
}

/// **Exactly one token.** In any state satisfying both invariants there is a
/// token, and it is unique.
pub proof fn theorem_ray_exactly_one_token(r: Raymond)
    requires
        ray_inv(r),
    ensures
        exists|n: NodeId| #[trigger] has_token(r, n),
        forall|n: NodeId, m: NodeId| has_token(r, n) && has_token(r, m) ==> n == m,
{
    assert forall|n: NodeId, m: NodeId| has_token(r, n) && has_token(r, m) implies n == m by {
        theorem_ray_at_most_one_token(r, n, m);
    }
}

/// **Only the token holder can be in the critical section.** Exposed as a
/// theorem in its own right, since it is the Raymond-layer counterpart of
/// ownership exclusivity.
pub proof fn theorem_ray_critical_section_is_exclusive(r: Raymond, n: NodeId, m: NodeId)
    requires
        ray_inv(r),
        r.nodes.contains(n),
        r.nodes.contains(m),
        r.using[n],
        r.using[m],
    ensures
        n == m,
{
    assert(has_token(r, n));
    assert(has_token(r, m));
    theorem_ray_at_most_one_token(r, n, m);
}

/// **Token transfer preserves ownership safety.**
///
/// The token may only be passed on while the ownership layer is *not* `Owned` -
/// that is, after the actor has been released. Under that condition the
/// coupling survives the transfer, so afterwards still at most one node can
/// possibly hold authority, and it is the new token holder.
pub proof fn theorem_token_transfer_preserves_ownership_safety(
    pre: Raymond,
    post: Raymond,
    n: NodeId,
    head: NodeId,
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
        forall|m: NodeId| has_token(post, m) ==> m == head,
{
    lemma_assign_privilege_preserves_unique_token(pre, post, n, head);
    assert forall|m: NodeId, e: Epoch| may_mutate(own, m, e) implies has_token(post, m) by {
        assert(!is_owned(own));
        assert(false);
    }
}

/// Taking ownership while holding the token establishes the coupling: the only
/// node that can mutate is exactly the token holder.
pub proof fn theorem_acquire_under_token_establishes_coupling(
    r: Raymond,
    n: NodeId,
    e: Epoch,
)
    requires
        ray_inv(r),
        has_token(r, n),
    ensures
        couples(r, OwnershipState::Owned { owner: n, epoch: e }),
{
    assert forall|m: NodeId, x: Epoch|
        may_mutate(OwnershipState::Owned { owner: n, epoch: e }, m, x) implies has_token(r, m) by {
        assert(m == n);
    }
}

/// **The composed safety property.** Under the coupling, two nodes permitted to
/// mutate the actor are the same node, and that node is the Raymond token
/// holder. Routing cannot create a second one because there is only ever one
/// token.
pub proof fn theorem_coupled_exclusivity(
    r: Raymond,
    own: OwnershipState,
    n1: NodeId,
    e1: Epoch,
    n2: NodeId,
    e2: Epoch,
)
    requires
        ray_inv(r),
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
