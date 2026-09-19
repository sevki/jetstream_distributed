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
        exists|r: Raymond|
            {
                &&& #[trigger] ray_inv(r)
                &&& has_token(r, d)
                &&& r.using[d]
                &&& forall|m: NodeId| has_token(r, m) ==> m == d
            },
{
    let nodes = Set::<NodeId>::empty().insert(a).insert(b).insert(c).insert(d);
    let empty_q = Seq::<NodeId>::empty();

    // holder: A -> C, B -> A, C -> C (token), D -> B
    let holder0 = Map::<NodeId, NodeId>::empty().insert(a, c).insert(b, a).insert(c, c).insert(
        d,
        b,
    );
    let queue0 = Map::<NodeId, Seq<NodeId>>::empty().insert(a, empty_q).insert(b, empty_q).insert(
        c,
        empty_q,
    ).insert(d, empty_q);
    let flags0 = Map::<NodeId, bool>::empty().insert(a, false).insert(b, false).insert(
        c,
        false,
    ).insert(d, false);

    let r0 = Raymond {
        nodes: nodes,
        holder: holder0,
        queue: queue0,
        asked: flags0,
        using: flags0,
        requests: Set::<(NodeId, NodeId)>::empty(),
    };
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

    // 7. C receives A's request. The request path D -> B -> A -> C is complete.
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
    assert(has_token(r7, c));

    // 8. C hands the token to A.
    let r8 = Raymond {
        nodes: r7.nodes,
        holder: r7.holder.insert(c, a).insert(a, a),
        queue: r7.queue.insert(c, r7.queue[c].drop_first()),
        asked: r7.asked.insert(c, false),
        using: r7.using,
        requests: r7.requests,
    };
    assert(r7.queue[c].len() == 1);
    assert(r7.queue[c][0] == a);
    assert(!r7.using[c]);
    assert(ray_step(r7, r8, RayStep::AssignPrivilege { node: c, head: a }));
    lemma_ray_step_preserves_inv(r7, r8, RayStep::AssignPrivilege { node: c, head: a });
    lemma_assign_privilege_preserves_unique_token(r7, r8, c, a);
    assert(has_token(r8, a));
    assert(!has_token(r8, c));

    // 9. A hands the token to B.
    let r9 = Raymond {
        nodes: r8.nodes,
        holder: r8.holder.insert(a, b).insert(b, b),
        queue: r8.queue.insert(a, r8.queue[a].drop_first()),
        asked: r8.asked.insert(a, false),
        using: r8.using,
        requests: r8.requests,
    };
    assert(r8.queue[a].len() == 1);
    assert(r8.queue[a][0] == b);
    assert(!r8.using[a]);
    assert(ray_step(r8, r9, RayStep::AssignPrivilege { node: a, head: b }));
    lemma_ray_step_preserves_inv(r8, r9, RayStep::AssignPrivilege { node: a, head: b });
    lemma_assign_privilege_preserves_unique_token(r8, r9, a, b);
    assert(has_token(r9, b));
    assert(!has_token(r9, a));

    // 10. B hands the token to D. The token path C -> A -> B -> D is complete.
    let r10 = Raymond {
        nodes: r9.nodes,
        holder: r9.holder.insert(b, d).insert(d, d),
        queue: r9.queue.insert(b, r9.queue[b].drop_first()),
        asked: r9.asked.insert(b, false),
        using: r9.using,
        requests: r9.requests,
    };
    assert(r9.queue[b].len() == 1);
    assert(r9.queue[b][0] == d);
    assert(!r9.using[b]);
    assert(ray_step(r9, r10, RayStep::AssignPrivilege { node: b, head: d }));
    lemma_ray_step_preserves_inv(r9, r10, RayStep::AssignPrivilege { node: b, head: d });
    lemma_assign_privilege_preserves_unique_token(r9, r10, b, d);
    assert(has_token(r10, d));
    assert(!has_token(r10, b));

    // 11. D, finally at the head of its own queue, enters the critical section.
    let r11 = Raymond {
        nodes: r10.nodes,
        holder: r10.holder,
        queue: r10.queue.insert(d, r10.queue[d].drop_first()),
        asked: r10.asked,
        using: r10.using.insert(d, true),
        requests: r10.requests,
    };
    assert(r10.queue[d].len() == 1);
    assert(r10.queue[d][0] == d);
    assert(!r10.using[d]);
    assert(ray_step(r10, r11, RayStep::EnterCs { node: d }));
    lemma_ray_step_preserves_inv(r10, r11, RayStep::EnterCs { node: d });

    // The token ended up exactly where the request came from, and it is still
    // the only token in the system.
    assert(has_token(r11, d));
    assert(ray_unique_token(r11));
    assert forall|m: NodeId| has_token(r11, m) implies m == d by {
        theorem_ray_at_most_one_token(r11, m, d);
    }

    // 12. The adversarial tail: D's *original* request to B, sent back at step
    // 2, is redelivered now - after the token has travelled the whole path and
    // `holder[d]` has become `d`, so the topology it was routed against is long
    // gone. It is still deliverable, because `requests` records what was sent
    // rather than what the holder pointers currently say.
    assert(r11.holder[d] == d);
    assert(r11.requests.contains((d, b)));
    theorem_delayed_request_survives_token_move(r9, r10, b, d, b, d);
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

    // Delivering it changed nothing about who holds the token.
    assert(has_token(r12, d));
    assert forall|m: NodeId| has_token(r12, m) implies m == d by {
        theorem_ray_at_most_one_token(r12, m, d);
    }
}

} // verus!
