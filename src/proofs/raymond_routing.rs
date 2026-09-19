//! A concrete Raymond routing execution.
//!
//! Four nodes, with `C` holding the token and holder pointers forming a tree
//! rooted at `C`:
//!
//! ```text
//! holder:  A -> C     B -> A     C -> C[token]     D -> B
//! ```
//!
//! `D` asks for the token. The request is routed hop-by-hop towards the token:
//!
//! ```text
//! D -> B -> A -> C[token]
//! ```
//!
//! and the token then travels back along the reverse of that path:
//!
//! ```text
//! C -> A -> B -> D
//! ```
//!
//! Every hop below is proved to be a legal Raymond transition, and the Raymond
//! invariant (in particular: at most one token) is carried through all eleven
//! steps - plus a twelfth, adversarial one: `D`'s original request to `B` is
//! redelivered after the token has finished travelling, when the holder pointers
//! it was routed against are long gone.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::raymond::*;
use crate::raymond::*;

verus! {

/// The routing tree the scenario starts from:
/// `A -> C`, `B -> A`, `C -> C` (token), `D -> B`.
///
/// Named rather than built inline so every phase can refer to *the same* start
/// state, and so the scenario's postcondition can say the final state is
/// reachable **from** it. Without that anchor the exported endpoint is just a
/// state satisfying `ray_inv`, which a directly constructed four-node state
/// meets without any of the hops having happened.
pub open spec fn routing_init_state(a: NodeId, b: NodeId, c: NodeId, d: NodeId) -> Raymond {
    Raymond {
        nodes: Set::<NodeId>::empty().insert(a).insert(b).insert(c).insert(d),
        holder: Map::<NodeId, NodeId>::empty().insert(a, c).insert(b, a).insert(c, c).insert(d, b),
        queue: Map::<NodeId, Seq<NodeId>>::empty().insert(a, Seq::<NodeId>::empty()).insert(
            b,
            Seq::<NodeId>::empty(),
        ).insert(c, Seq::<NodeId>::empty()).insert(d, Seq::<NodeId>::empty()),
        asked: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false).insert(
            c,
            false,
        ).insert(d, false),
        using: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false).insert(
            c,
            false,
        ).insert(d, false),
        requests: Set::<(NodeId, NodeId)>::empty(),
    }
}

/// Phase one: the request travels `D -> B -> A -> C`.
///
/// The end state is handed back through an *abstract* characterisation rather
/// than as a literal, so the later phases never have to reason about the
/// `Map`/`Set` nest built here. Replaying all twelve hops in one function made
/// the single SMT query large enough to dominate the whole proof run.
pub proof fn routing_phase_requests(a: NodeId, b: NodeId, c: NodeId, d: NodeId) -> (r: Raymond)
    requires
        a != b,
        a != c,
        a != d,
        b != c,
        b != d,
        c != d,
    ensures
        ray_inv(r),
        has_token(r, c),
        ray_init(routing_init_state(a, b, c, d), c),
        ray_reachable_from(routing_init_state(a, b, c, d), r),
        r.nodes == routing_init_state(a, b, c, d).nodes,
        r.nodes.contains(a),
        r.nodes.contains(b),
        r.nodes.contains(c),
        r.nodes.contains(d),
        r.queue[c].len() == 1 && r.queue[c][0] == a,
        r.queue[a].len() == 1 && r.queue[a][0] == b,
        r.queue[b].len() == 1 && r.queue[b][0] == d,
        r.queue[d].len() == 1 && r.queue[d][0] == d,
        !r.using[a],
        !r.using[b],
        !r.using[c],
        !r.using[d],
        r.requests.contains((d, b)),
{
    let r0 = routing_init_state(a, b, c, d);
    lemma_ray_reachable_from_refl(r0);
    assert(r0.holder[a] == c);
    assert(r0.holder[b] == a);
    assert(r0.holder[c] == c);
    assert(r0.holder[d] == b);
    assert(ray_init(r0, c));
    theorem_ray_init_inv(r0, c);
    assert(has_token(r0, c));

    // 1. D asks for the token.
    let r1 = Raymond {
        nodes: r0.nodes,
        holder: r0.holder,
        queue: r0.queue.insert(d, r0.queue[d].push(d)),
        asked: r0.asked,
        using: r0.using,
        requests: r0.requests,
    };
    assert(ray_step(r0, r1, RayStep::RequestCs { node: d }));
    lemma_ray_step_preserves_inv(r0, r1, RayStep::RequestCs { node: d });
    lemma_ray_reachable_from_step(r0, r0, r1, RayStep::RequestCs { node: d });

    // 2. D forwards the request to its next hop, B.
    let r2 = Raymond {
        nodes: r1.nodes,
        holder: r1.holder,
        queue: r1.queue,
        asked: r1.asked.insert(d, true),
        using: r1.using,
        requests: r1.requests.insert((d, r1.holder[d])),
    };
    assert(r1.queue[d].len() == 1);
    assert(ray_step(r1, r2, RayStep::MakeRequest { node: d }));
    lemma_ray_step_preserves_inv(r1, r2, RayStep::MakeRequest { node: d });
    lemma_ray_reachable_from_step(r0, r1, r2, RayStep::MakeRequest { node: d });

    // 3. B receives D's request.
    let r3 = Raymond {
        nodes: r2.nodes,
        holder: r2.holder,
        queue: r2.queue.insert(b, r2.queue[b].push(d)),
        asked: r2.asked,
        using: r2.using,
        requests: r2.requests,
    };
    assert(r2.requests.contains((d, b)));
    assert(ray_step(r2, r3, RayStep::ReceiveRequest { at: b, from: d }));
    lemma_ray_step_preserves_inv(r2, r3, RayStep::ReceiveRequest { at: b, from: d });
    lemma_ray_reachable_from_step(r0, r2, r3, RayStep::ReceiveRequest { at: b, from: d });

    // 4. B forwards the request to its next hop, A.
    let r4 = Raymond {
        nodes: r3.nodes,
        holder: r3.holder,
        queue: r3.queue,
        asked: r3.asked.insert(b, true),
        using: r3.using,
        requests: r3.requests.insert((b, r3.holder[b])),
    };
    assert(r3.queue[b].len() == 1);
    assert(!r3.asked[b]);
    assert(ray_step(r3, r4, RayStep::MakeRequest { node: b }));
    lemma_ray_step_preserves_inv(r3, r4, RayStep::MakeRequest { node: b });
    lemma_ray_reachable_from_step(r0, r3, r4, RayStep::MakeRequest { node: b });

    // 5. A receives B's request.
    let r5 = Raymond {
        nodes: r4.nodes,
        holder: r4.holder,
        queue: r4.queue.insert(a, r4.queue[a].push(b)),
        asked: r4.asked,
        using: r4.using,
        requests: r4.requests,
    };
    assert(r4.requests.contains((b, a)));
    assert(ray_step(r4, r5, RayStep::ReceiveRequest { at: a, from: b }));
    lemma_ray_step_preserves_inv(r4, r5, RayStep::ReceiveRequest { at: a, from: b });
    lemma_ray_reachable_from_step(r0, r4, r5, RayStep::ReceiveRequest { at: a, from: b });

    // 6. A forwards the request to its next hop, C - the token holder.
    let r6 = Raymond {
        nodes: r5.nodes,
        holder: r5.holder,
        queue: r5.queue,
        asked: r5.asked.insert(a, true),
        using: r5.using,
        requests: r5.requests.insert((a, r5.holder[a])),
    };
    assert(r5.queue[a].len() == 1);
    assert(!r5.asked[a]);
    assert(ray_step(r5, r6, RayStep::MakeRequest { node: a }));
    lemma_ray_step_preserves_inv(r5, r6, RayStep::MakeRequest { node: a });
    lemma_ray_reachable_from_step(r0, r5, r6, RayStep::MakeRequest { node: a });

    // 7. C receives A's request. The path D -> B -> A -> C is complete.
    let r7 = Raymond {
        nodes: r6.nodes,
        holder: r6.holder,
        queue: r6.queue.insert(c, r6.queue[c].push(a)),
        asked: r6.asked,
        using: r6.using,
        requests: r6.requests,
    };
    assert(r6.requests.contains((a, c)));
    assert(ray_step(r6, r7, RayStep::ReceiveRequest { at: c, from: a }));
    lemma_ray_step_preserves_inv(r6, r7, RayStep::ReceiveRequest { at: c, from: a });
    lemma_ray_reachable_from_step(r0, r6, r7, RayStep::ReceiveRequest { at: c, from: a });
    assert(has_token(r7, c));
    assert(r7.requests.contains((d, b)));
    r7
}


/// One hop of the token, packaged so that callers never see the holder map.
///
/// `AssignPrivilege` rewrites two holder pointers, so chaining three of them
/// inline leaves the solver unfolding `has_token` through six nested
/// `Map::insert`s. Proving the hop once, against an *abstract* `r`, and
/// exporting only the queue facts the next hop needs keeps `holder` out of the
/// caller entirely.
///
/// This function is also what exposed the matching loop documented on
/// [`crate::raymond::ray_holder_closed`]: reduced to a single transition, it
/// still exceeded the solver's resource limit, which is how a cost that scales
/// with nothing in the proof became visible.
pub proof fn routing_one_hop(r: Raymond, n: NodeId, head: NodeId) -> (r2: Raymond)
    requires
        ray_inv(r),
        has_token(r, n),
        !r.using[n],
        r.queue[n].len() > 0,
        r.queue[n][0] == head,
        head != n,
        r.nodes.contains(head),
    ensures
        ray_inv(r2),
        has_token(r2, head),
        // Exported so callers can chain `ray_reachable_from` across the hop.
        ray_step(r, r2, RayStep::AssignPrivilege { node: n, head: head }),
        r2.nodes == r.nodes,
        r2.queue == r.queue.insert(n, r.queue[n].drop_first()),
        r2.using == r.using,
        r2.requests == r.requests,
{
    let r2 = Raymond {
        nodes: r.nodes,
        holder: r.holder.insert(n, head).insert(head, head),
        queue: r.queue.insert(n, r.queue[n].drop_first()),
        asked: r.asked.insert(n, false),
        using: r.using,
        requests: r.requests,
    };
    assert(ray_assign_privilege(r, r2, n, head));
    assert(ray_step(r, r2, RayStep::AssignPrivilege { node: n, head: head }));
    lemma_assign_privilege_preserves_unique_token(r, r2, n, head);
    r2
}

/// Phase two: the token travels back `C -> A -> B -> D`.
///
/// Three hops, each delegated to [`routing_one_hop`], so this function only
/// ever reasons about queues.
pub proof fn routing_phase_token_hops(
    init: Raymond,
    r7: Raymond,
    a: NodeId,
    b: NodeId,
    c: NodeId,
    d: NodeId,
) -> (r: Raymond)
    requires
        ray_reachable_from(init, r7),
        a != b,
        a != c,
        a != d,
        b != c,
        b != d,
        c != d,
        ray_inv(r7),
        has_token(r7, c),
        r7.nodes.contains(a),
        r7.nodes.contains(b),
        r7.nodes.contains(c),
        r7.nodes.contains(d),
        r7.queue[c].len() == 1 && r7.queue[c][0] == a,
        r7.queue[a].len() == 1 && r7.queue[a][0] == b,
        r7.queue[b].len() == 1 && r7.queue[b][0] == d,
        r7.queue[d].len() == 1 && r7.queue[d][0] == d,
        !r7.using[a],
        !r7.using[b],
        !r7.using[c],
        !r7.using[d],
        r7.requests.contains((d, b)),
    ensures
        ray_inv(r),
        has_token(r, d),
        ray_reachable_from(init, r),
        r.nodes == r7.nodes,
        r.queue[d].len() == 1 && r.queue[d][0] == d,
        !r.using[d],
        r.requests.contains((d, b)),
{
    // 8. C hands the token to A.
    let r8 = routing_one_hop(r7, c, a);
    lemma_ray_reachable_from_step(init, r7, r8, RayStep::AssignPrivilege { node: c, head: a });
    assert(r8.queue[a] == r7.queue[a]);
    assert(r8.queue[b] == r7.queue[b]);
    assert(r8.queue[d] == r7.queue[d]);

    // 9. A hands the token to B.
    let r9 = routing_one_hop(r8, a, b);
    lemma_ray_reachable_from_step(init, r8, r9, RayStep::AssignPrivilege { node: a, head: b });
    assert(r9.queue[b] == r8.queue[b]);
    assert(r9.queue[d] == r8.queue[d]);

    // 10. B hands the token to D. The path C -> A -> B -> D is complete.
    let r10 = routing_one_hop(r9, b, d);
    lemma_ray_reachable_from_step(init, r9, r10, RayStep::AssignPrivilege { node: b, head: d });
    assert(r10.queue[d] == r9.queue[d]);

    // `requests` is untouched by every hop, so D's request to B - sent back at
    // step 2, against holder pointers that no longer exist - is still there.
    assert(r10.requests.contains((d, b)));
    r10
}

/// Phase three: `D` enters the critical section, and `D`'s *original* request to
/// `B` is redelivered afterwards - when the holder pointers it was routed
/// against are long gone.
///
/// Note how little this phase needs to know: the whole eleven-hop history is
/// compressed into six preconditions. That is the point of splitting - the
/// solver never sees the `Map`/`Set` nest the earlier phases built.
pub proof fn routing_phase_delivery(
    init: Raymond,
    r10: Raymond,
    b: NodeId,
    d: NodeId,
) -> (r: Raymond)
    requires
        ray_reachable_from(init, r10),
        b != d,
        ray_inv(r10),
        has_token(r10, d),
        r10.nodes.contains(b),
        r10.queue[d].len() == 1 && r10.queue[d][0] == d,
        !r10.using[d],
        r10.requests.contains((d, b)),
    ensures
        ray_inv(r),
        has_token(r, d),
        r.using[d],
        r.nodes == r10.nodes,
        forall|m: NodeId| #[trigger] has_token(r, m) ==> m == d,
        // The delayed redelivery itself, as a step out of a state in which `D`
        // already holds the token and is inside its critical section, and in
        // which `D`'s original request to `B` is still outstanding. Exporting
        // only the endpoint would be satisfied by any `ray_inv` state with `D`
        // as sole root - including a singleton with no routing history at all.
        exists|p: Raymond|
            {
                &&& #[trigger] ray_step(p, r, RayStep::ReceiveRequest { at: b, from: d })
                &&& #[trigger] ray_reachable_from(init, p)
                &&& ray_inv(p)
                &&& has_token(p, d)
                &&& p.using[d]
                &&& p.requests.contains((d, b))
                &&& p.nodes == r10.nodes
            },
{
    // 11. D, at the head of its own queue, enters the critical section.
    let r11 = Raymond {
        nodes: r10.nodes,
        holder: r10.holder,
        queue: r10.queue.insert(d, r10.queue[d].drop_first()),
        asked: r10.asked,
        using: r10.using.insert(d, true),
        requests: r10.requests,
    };
    assert(ray_step(r10, r11, RayStep::EnterCs { node: d }));
    lemma_ray_step_preserves_inv(r10, r11, RayStep::EnterCs { node: d });
    lemma_ray_reachable_from_step(init, r10, r11, RayStep::EnterCs { node: d });
    assert(has_token(r11, d));

    // 12. The adversarial tail: D's original request to B, sent back at step 2,
    // is redelivered now - after the token has travelled the whole path and
    // `holder[d]` has become `d`, so the topology it was routed against is long
    // gone. It is still deliverable, because `requests` records what was sent.
    assert(r11.holder[d] == d);
    assert(r11.requests.contains((d, b)));
    let r12 = Raymond {
        nodes: r11.nodes,
        holder: r11.holder,
        queue: r11.queue.insert(b, r11.queue[b].push(d)),
        asked: r11.asked,
        using: r11.using,
        requests: r11.requests,
    };
    assert(ray_step(r11, r12, RayStep::ReceiveRequest { at: b, from: d }));
    theorem_delayed_request_delivery_is_safe(r11, r12, b, d);
    lemma_ray_reachable_from_step(init, r11, r12, RayStep::ReceiveRequest { at: b, from: d });

    assert(has_token(r12, d));
    assert(r12.using[d]);
    assert(r12.nodes == r10.nodes);
    assert forall|m: NodeId| #[trigger] has_token(r12, m) implies m == d by {
        theorem_ray_at_most_one_token(r12, m, d);
    }
    // `r11` is the witness for the exported redelivery step.
    assert(ray_step(r11, r12, RayStep::ReceiveRequest { at: b, from: d }));
    assert(ray_inv(r11));
    assert(has_token(r11, d));
    assert(r11.using[d]);
    assert(r11.requests.contains((d, b)));
    assert(r11.nodes == r10.nodes);
    assert(ray_reachable_from(init, r11));
    assert(ray_reachable_from(init, r12));
    r12
}

/// Requests route `D -> B -> A -> C`, then the token routes `C -> A -> B -> D`.
pub proof fn scenario_request_and_token_routing(a: NodeId, b: NodeId, c: NodeId, d: NodeId)
    requires
        a != b,
        a != c,
        a != d,
        b != c,
        b != d,
        c != d,
    ensures
        // The endpoint *and* the step that reaches it, so that deleting the
        // routing phases cannot leave this verifying: a singleton Raymond with
        // `D` as sole root satisfies the endpoint clauses on their own.
        // Anchored at the start state and linked by reachability. `ray_init(r0, c)`
        // pins where the run began - four nodes, the token at `C` - and
        // `ray_reachable_from(r0, p)` pins that `p` was *reached* from there
        // rather than constructed. Without both, a directly built four-node
        // state with `D` already root, already in its critical section and with
        // `(d, b)` already in `requests` satisfies everything after a single
        // `ReceiveRequest`, and `A` and `C` need never participate.
        exists|r0: Raymond, p: Raymond, r: Raymond|
            {
                &&& #[trigger] ray_step(p, r, RayStep::ReceiveRequest { at: b, from: d })
                &&& #[trigger] ray_reachable_from(r0, p)
                // `ray_init` alone constrains only the root and the empty
                // queues, not the holder *tree*: an initial `D -> B -> C`,
                // `A -> C` satisfies it, and the run could then go
                // `D -> B -> C` and back with `A` never participating. Pinning
                // `r0` to the named state is what protects the advertised
                // `D -> B -> A -> C` path.
                &&& r0 == routing_init_state(a, b, c, d)
                &&& ray_init(r0, c)
                &&& has_token(r0, c)
                &&& r0.nodes.contains(a)
                &&& r0.nodes.contains(b)
                &&& r0.nodes.contains(c)
                &&& r0.nodes.contains(d)
                &&& ray_inv(p)
                &&& ray_inv(r)
                &&& p.requests.contains((d, b))
                &&& has_token(p, d)
                &&& p.using[d]
                &&& has_token(r, d)
                &&& r.using[d]
                &&& forall|m: NodeId| has_token(r, m) ==> m == d
            },
{
    let r0 = routing_init_state(a, b, c, d);
    let after_requests = routing_phase_requests(a, b, c, d);
    let after_hops = routing_phase_token_hops(r0, after_requests, a, b, c, d);
    let fin = routing_phase_delivery(r0, after_hops, b, d);
    assert(ray_inv(fin));
    assert(has_token(fin, d));
    assert(fin.using[d]);
    assert(ray_init(r0, c));
    assert(has_token(r0, c));
    assert(r0.nodes == after_requests.nodes);
    let p = choose|p: Raymond| {
        &&& ray_step(p, fin, RayStep::ReceiveRequest { at: b, from: d })
        &&& ray_reachable_from(r0, p)
        &&& ray_inv(p)
        &&& has_token(p, d)
        &&& p.using[d]
        &&& p.requests.contains((d, b))
        &&& p.nodes == after_hops.nodes
    };
    assert(ray_reachable_from(r0, p));
    assert(r0 == routing_init_state(a, b, c, d));
}

} // verus!
