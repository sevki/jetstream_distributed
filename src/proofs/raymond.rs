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
    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m) && post.using.contains_key(m)
        && post.nodes.contains(post.holder[m]) by {
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
        && post.queue.contains_key(m) && post.asked.contains_key(m) && post.using.contains_key(m)
        && post.nodes.contains(post.holder[m]) by {
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
