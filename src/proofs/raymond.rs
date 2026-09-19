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
        forall|n: NodeId| has_token(post, n) <==> has_token(pre, n),
{
    match s {
        RayStep::RequestCs { node } => {},
        RayStep::MakeRequest { node } => {},
        RayStep::ReceiveRequest { at, from } => {},
        RayStep::EnterCs { node } => {},
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
        forall|n: NodeId| has_token(post, n) <==> has_token(pre, n),
{
    lemma_routing_preserves_holder(pre, post, s);
}

/// **Duplicate and reordered requests cannot create a second owner.**
///
/// `ray_receive_request` has no sequence number and no duplicate suppression:
/// it can fire arbitrarily often, for arbitrary `(at, from)` pairs whose
/// routing topology matches, in any order. It still cannot produce a second
/// token holder, because it does not touch `holder` at all.
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
        forall|n: NodeId| has_token(post, n) <==> has_token(pre, n),
{
    lemma_ray_step_preserves_inv(pre, mid, RayStep::ReceiveRequest { at: at, from: from });
    lemma_ray_step_preserves_inv(mid, post, RayStep::ReceiveRequest { at: at, from: from });
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
        forall|m: NodeId| has_token(post, m) ==> m == head,
{
    assert(post.holder[head] == head);
    assert(post.holder[n] == head);
    assert(has_token(post, head));

    assert forall|m: NodeId| has_token(post, m) implies m == head by {
        if m != head && m != n {
            assert(post.holder[m] == pre.holder[m]);
            assert(has_token(pre, m));
            assert(has_token(pre, n));
            assert(m == n);
            assert(false);
        }
        if m == n {
            assert(post.holder[n] == head);
            assert(false);
        }
    }

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

    assert forall|m: NodeId| #[trigger] post.nodes.contains(m) implies post.holder.contains_key(m)
        && post.queue.contains_key(m) && post.asked.contains_key(m) && post.using.contains_key(m)
        && post.nodes.contains(post.holder[m]) by {
        assert(pre.nodes.contains(m));
        if m == head {
            assert(post.holder[m] == head);
        } else if m == n {
            assert(post.holder[m] == head);
        } else {
            assert(post.holder[m] == pre.holder[m]);
        }
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
            assert forall|m: NodeId| #[trigger] post.nodes.contains(m) && post.using[m]
                implies has_token(post, m) by {
                if m == node {
                    assert(has_token(pre, node));
                } else {
                    assert(post.using[m] == pre.using[m]);
                    assert(has_token(pre, m));
                }
            }
        },
        RayStep::ExitCs { node } => {
            assert forall|m: NodeId| #[trigger] post.nodes.contains(m) && post.using[m]
                implies has_token(post, m) by {
                assert(m != node);
                assert(post.using[m] == pre.using[m]);
                assert(has_token(pre, m));
            }
        },
        RayStep::RequestCs { node } => {},
        RayStep::MakeRequest { node } => {},
        RayStep::ReceiveRequest { at, from } => {},
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
