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

use vstd::assert_seqs_equal;
use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::raymond::proofs::routing_layer::*;
use crate::raymond::model::*;

verus! {

/// The routing tree the scenario starts from:
/// `A -> C`, `B -> A`, `C -> C` (token), `D -> B`.
///
/// Named rather than built inline so every phase can refer to *the same* start
/// state, and so the scenario's postcondition can say the final state is
/// reachable **from** it. Without that anchor the exported endpoint is just a
/// state satisfying `ray_inv`, which a directly constructed four-node state
/// meets without any of the hops having happened.
pub open spec fn routing_init_state(a: Id, b: Id, c: Id, d: Id) -> Raymond {
    Raymond {
        privilege: c,
        nodes: Set::<Id>::empty().insert(a).insert(b).insert(c).insert(d),
        holder: Map::<Id, Id>::empty().insert(a, c).insert(b, a).insert(c, c).insert(d, b),
        queue: Map::<Id, Seq<Id>>::empty().insert(a, Seq::<Id>::empty()).insert(
            b,
            Seq::<Id>::empty(),
        ).insert(c, Seq::<Id>::empty()).insert(d, Seq::<Id>::empty()),
        asked: Map::<Id, bool>::empty().insert(a, false).insert(b, false).insert(
            c,
            false,
        ).insert(d, false),
        using: Map::<Id, bool>::empty().insert(a, false).insert(b, false).insert(
            c,
            false,
        ).insert(d, false),
        requests: Set::<(Id, Id)>::empty(),
    }
}

/// The labels of the routing run: twelve steps from the tree in
/// [`routing_init_state`] to `D` in its critical section with its own original
/// request redelivered.
///
/// Pinning these is what makes the advertised *path* a claim rather than a
/// comment. Reachability alone allows `A`, `B` and `D` to request the token
/// independently and then serve their own queue heads, which reaches the same
/// end state without `D`'s request ever being forwarded through `B` and `A`.
/// Here there is exactly one `RequestCs`, it is `D`'s, and each `MakeRequest`
/// is preceded by the `ReceiveRequest` that put something in that node's queue.
pub open spec fn routing_labels(a: Id, b: Id, c: Id, d: Id) -> Seq<RayStep> {
    seq![
        RayStep::RequestCs { node: d },
        RayStep::MakeRequest { node: d },
        RayStep::ReceiveRequest { at: b, from: d },
        RayStep::MakeRequest { node: b },
        RayStep::ReceiveRequest { at: a, from: b },
        RayStep::MakeRequest { node: a },
        RayStep::ReceiveRequest { at: c, from: a },
        RayStep::AssignPrivilege { node: c, head: a },
        RayStep::AssignPrivilege { node: a, head: b },
        RayStep::AssignPrivilege { node: b, head: d },
        RayStep::EnterCs { node: d },
        RayStep::ReceiveRequest { at: b, from: d },
    ]
}

/// Phase one: the request travels `D -> B -> A -> C`.
///
/// The end state is handed back through an *abstract* characterisation rather
/// than as a literal, so the later phases never have to reason about the
/// `Map`/`Set` nest built here. Replaying all twelve hops in one function made
/// the single SMT query large enough to dominate the whole proof run.
pub proof fn routing_phase_requests(a: Id, b: Id, c: Id, d: Id) -> (res: (
    Raymond,
    Seq<Raymond>,
    Seq<RayStep>,
))
    requires
        a != b,
        a != c,
        a != d,
        b != c,
        b != d,
        c != d,
    ensures
        ray_run(res.1, res.2),
        res.1[0] == routing_init_state(a, b, c, d),
        res.1[res.1.len() - 1] == res.0,
        res.1.len() == 8,
        res.2.len() == 7,
        res.2[0] == (RayStep::RequestCs { node: d }),
        res.2[1] == (RayStep::MakeRequest { node: d }),
        res.2[2] == (RayStep::ReceiveRequest { at: b, from: d }),
        res.2[3] == (RayStep::MakeRequest { node: b }),
        res.2[4] == (RayStep::ReceiveRequest { at: a, from: b }),
        res.2[5] == (RayStep::MakeRequest { node: a }),
        res.2[6] == (RayStep::ReceiveRequest { at: c, from: a }),
        ray_init(routing_init_state(a, b, c, d), c),
        ray_inv(res.0),
        has_token(res.0, c),
        res.0.nodes == routing_init_state(a, b, c, d).nodes,
        res.0.nodes.contains(a),
        res.0.nodes.contains(b),
        res.0.nodes.contains(c),
        res.0.nodes.contains(d),
        res.0.queue[c].len() == 1 && res.0.queue[c][0] == a,
        res.0.queue[a].len() == 1 && res.0.queue[a][0] == b,
        res.0.queue[b].len() == 1 && res.0.queue[b][0] == d,
        res.0.queue[d].len() == 1 && res.0.queue[d][0] == d,
        !res.0.using[a],
        !res.0.using[b],
        !res.0.using[c],
        !res.0.using[d],
        res.0.requests.contains((d, b)),
{
    let r0 = routing_init_state(a, b, c, d);
    assert(r0.holder[a] == c);
    assert(r0.holder[b] == a);
    assert(r0.holder[c] == c);
    assert(r0.holder[d] == b);
    // `ray_init` requires the holder pointers to be acyclic, and the start tree
    // `D -> B -> A -> C` is ranked by its distance from the root `C`.
    let ray_rank = Map::new(
        r0.nodes,
        |k: Id|
            if k == c {
                0nat
            } else if k == a {
                1nat
            } else if k == b {
                2nat
            } else {
                3nat
            },
    );
    assert forall|n: Id| #[trigger] r0.nodes.contains(n) implies ray_rank.contains_key(n) by {
    }
    assert forall|n: Id|
        r0.nodes.contains(n) && #[trigger] r0.holder[n] != n implies ray_rank[r0.holder[n]]
            < ray_rank[n] by {
        assert(n == a || n == b || n == c || n == d);
        assert(n != c);
        if n == a {
            assert(r0.holder[a] == c);
        } else if n == b {
            assert(r0.holder[b] == a);
        } else {
            assert(r0.holder[d] == b);
        }
    }
    assert(ray_ranked_by(r0, ray_rank));
    assert(ray_acyclic(r0));
    assert(ray_init(r0, c));
    theorem_ray_init_inv(r0, c);
    assert(has_token(r0, c));

    // 1. D asks for the token.
    let r1 = Raymond {
        privilege: r0.privilege,
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
        privilege: r1.privilege,
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
        privilege: r2.privilege,
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
        privilege: r3.privilege,
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
        privilege: r4.privilege,
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
        privilege: r5.privilege,
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

    // 7. C receives A's request. The path D -> B -> A -> C is complete.
    let r7 = Raymond {
        privilege: r6.privilege,
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
    assert(r7.requests.contains((d, b)));

    // Collect the seven request steps into the run.
    let tr0 = seq![r0];
    let l0 = Seq::<RayStep>::empty();
    lemma_ray_run_init(r0);
    let s1 = RayStep::RequestCs { node: d };
    let tr1 = tr0.push(r1);
    let l1 = l0.push(s1);
    lemma_ray_run_push(tr0, l0, r1, s1);
    assert(tr1.len() == 2);
    assert(l1.len() == 1);
    assert(tr1[0] == r0);
    assert(tr1[1] == r1);
    assert(l1[0] == s1);
    let s2 = RayStep::MakeRequest { node: d };
    let tr2 = tr1.push(r2);
    let l2 = l1.push(s2);
    lemma_ray_run_push(tr1, l1, r2, s2);
    assert(tr2.len() == 3);
    assert(l2.len() == 2);
    assert(tr2[0] == r0);
    assert(tr2[2] == r2);
    assert(l2[0] == s1);
    assert(l2[1] == s2);
    let s3 = RayStep::ReceiveRequest { at: b, from: d };
    let tr3 = tr2.push(r3);
    let l3 = l2.push(s3);
    lemma_ray_run_push(tr2, l2, r3, s3);
    assert(tr3.len() == 4);
    assert(l3.len() == 3);
    assert(tr3[0] == r0);
    assert(tr3[3] == r3);
    assert(l3[0] == s1);
    assert(l3[1] == s2);
    assert(l3[2] == s3);
    let s4 = RayStep::MakeRequest { node: b };
    let tr4 = tr3.push(r4);
    let l4 = l3.push(s4);
    lemma_ray_run_push(tr3, l3, r4, s4);
    assert(tr4.len() == 5);
    assert(l4.len() == 4);
    assert(tr4[0] == r0);
    assert(tr4[4] == r4);
    assert(l4[0] == s1);
    assert(l4[1] == s2);
    assert(l4[2] == s3);
    assert(l4[3] == s4);
    let s5 = RayStep::ReceiveRequest { at: a, from: b };
    let tr5 = tr4.push(r5);
    let l5 = l4.push(s5);
    lemma_ray_run_push(tr4, l4, r5, s5);
    assert(tr5.len() == 6);
    assert(l5.len() == 5);
    assert(tr5[0] == r0);
    assert(tr5[5] == r5);
    assert(l5[0] == s1);
    assert(l5[1] == s2);
    assert(l5[2] == s3);
    assert(l5[3] == s4);
    assert(l5[4] == s5);
    let s6 = RayStep::MakeRequest { node: a };
    let tr6 = tr5.push(r6);
    let l6 = l5.push(s6);
    lemma_ray_run_push(tr5, l5, r6, s6);
    assert(tr6.len() == 7);
    assert(l6.len() == 6);
    assert(tr6[0] == r0);
    assert(tr6[6] == r6);
    assert(l6[0] == s1);
    assert(l6[1] == s2);
    assert(l6[2] == s3);
    assert(l6[3] == s4);
    assert(l6[4] == s5);
    assert(l6[5] == s6);
    let s7 = RayStep::ReceiveRequest { at: c, from: a };
    let tr7 = tr6.push(r7);
    let l7 = l6.push(s7);
    lemma_ray_run_push(tr6, l6, r7, s7);
    assert(tr7.len() == 8);
    assert(l7.len() == 7);
    assert(tr7[0] == r0);
    assert(tr7[7] == r7);
    assert(l7[0] == s1);
    assert(l7[1] == s2);
    assert(l7[2] == s3);
    assert(l7[3] == s4);
    assert(l7[4] == s5);
    assert(l7[5] == s6);
    assert(l7[6] == s7);
    assert(ray_run(tr7, l7));
    (r7, tr7, l7)
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
/// [`crate::raymond::model::ray_holder_closed`]: reduced to a single transition, it
/// still exceeded the solver's resource limit, which is how a cost that scales
/// with nothing in the proof became visible.
pub proof fn routing_one_hop(r: Raymond, n: Id, head: Id) -> (r2: Raymond)
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
        privilege: head,
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
    tr: Seq<Raymond>,
    labels: Seq<RayStep>,
    r7: Raymond,
    a: Id,
    b: Id,
    c: Id,
    d: Id,
) -> (res: (Raymond, Seq<Raymond>, Seq<RayStep>))
    requires
        a != b,
        a != c,
        a != d,
        b != c,
        b != d,
        c != d,
        ray_run(tr, labels),
        tr[tr.len() - 1] == r7,
        labels.len() == 7,
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
        ray_run(res.1, res.2),
        res.1[0] == tr[0],
        res.1[res.1.len() - 1] == res.0,
        res.1.len() == 11,
        res.2.len() == 10,
        forall|i: int| 0 <= i < 7 ==> #[trigger] res.2[i] == labels[i],
        res.2[7] == (RayStep::AssignPrivilege { node: c, head: a }),
        res.2[8] == (RayStep::AssignPrivilege { node: a, head: b }),
        res.2[9] == (RayStep::AssignPrivilege { node: b, head: d }),
        ray_inv(res.0),
        has_token(res.0, d),
        res.0.nodes == r7.nodes,
        res.0.queue[d].len() == 1 && res.0.queue[d][0] == d,
        !res.0.using[d],
        res.0.requests.contains((d, b)),
{
    // 8. C hands the token to A.
    let r8 = routing_one_hop(r7, c, a);
    assert(r8.queue[a] == r7.queue[a]);
    assert(r8.queue[b] == r7.queue[b]);
    assert(r8.queue[d] == r7.queue[d]);

    // 9. A hands the token to B.
    let r9 = routing_one_hop(r8, a, b);
    assert(r9.queue[b] == r8.queue[b]);
    assert(r9.queue[d] == r8.queue[d]);

    // 10. B hands the token to D. The path C -> A -> B -> D is complete.
    let r10 = routing_one_hop(r9, b, d);
    assert(r10.queue[d] == r9.queue[d]);

    // `requests` is untouched by every hop, so D's request to B - sent back at
    // step 2, against holder pointers that no longer exist - is still there.
    assert(r10.requests.contains((d, b)));

    // Collect the three token hops into the run.
    assert(tr.len() == 8);
    let h8 = RayStep::AssignPrivilege { node: c, head: a };
    let tr8 = tr.push(r8);
    let l8 = labels.push(h8);
    lemma_ray_run_push(tr, labels, r8, h8);
    assert(tr8.len() == 9);
    assert(l8.len() == 8);
    assert(tr8[0] == tr[0]);
    assert(tr8[8] == r8);
    assert(l8[7] == h8);
    assert(forall|i: int| 0 <= i < 7 ==> #[trigger] l8[i] == labels[i]);
    let h9 = RayStep::AssignPrivilege { node: a, head: b };
    let tr9 = tr8.push(r9);
    let l9 = l8.push(h9);
    lemma_ray_run_push(tr8, l8, r9, h9);
    assert(tr9.len() == 10);
    assert(l9.len() == 9);
    assert(tr9[0] == tr[0]);
    assert(tr9[9] == r9);
    assert(l9[7] == h8);
    assert(l9[8] == h9);
    assert forall|i: int| 0 <= i < 7 implies #[trigger] l9[i] == labels[i] by {
        assert(l8[i] == labels[i]);
    }
    let h10 = RayStep::AssignPrivilege { node: b, head: d };
    let tr10 = tr9.push(r10);
    let l10 = l9.push(h10);
    lemma_ray_run_push(tr9, l9, r10, h10);
    assert(tr10.len() == 11);
    assert(l10.len() == 10);
    assert(tr10[0] == tr[0]);
    assert(tr10[10] == r10);
    assert(l10[7] == h8);
    assert(l10[8] == h9);
    assert(l10[9] == h10);
    assert forall|i: int| 0 <= i < 7 implies #[trigger] l10[i] == labels[i] by {
        assert(l9[i] == labels[i]);
    }
    assert(ray_run(tr10, l10));
    (r10, tr10, l10)
}

/// Phase three: `D` enters the critical section, and `D`'s *original* request to
/// `B` is redelivered afterwards - when the holder pointers it was routed
/// against are long gone.
///
/// Note how little this phase needs to know: the whole eleven-hop history is
/// compressed into six preconditions. That is the point of splitting - the
/// solver never sees the `Map`/`Set` nest the earlier phases built.
pub proof fn routing_phase_delivery(
    tr: Seq<Raymond>,
    labels: Seq<RayStep>,
    r10: Raymond,
    b: Id,
    d: Id,
) -> (res: (Raymond, Seq<Raymond>, Seq<RayStep>))
    requires
        b != d,
        ray_run(tr, labels),
        tr[tr.len() - 1] == r10,
        labels.len() == 10,
        ray_inv(r10),
        has_token(r10, d),
        r10.nodes.contains(b),
        r10.queue[d].len() == 1 && r10.queue[d][0] == d,
        !r10.using[d],
        r10.requests.contains((d, b)),
    ensures
        ray_run(res.1, res.2),
        res.1[0] == tr[0],
        res.1[res.1.len() - 1] == res.0,
        res.1.len() == 13,
        res.2.len() == 12,
        forall|i: int| 0 <= i < 10 ==> #[trigger] res.2[i] == labels[i],
        res.2[10] == (RayStep::EnterCs { node: d }),
        res.2[11] == (RayStep::ReceiveRequest { at: b, from: d }),
        ray_inv(res.0),
        has_token(res.0, d),
        res.0.using[d],
        res.0.nodes == r10.nodes,
        forall|m: Id| #[trigger] has_token(res.0, m) ==> m == d,
        // The state the delayed redelivery fires in, at the index it occupies:
        // `D` already holds the token and is inside its critical section, and
        // its own original request to `B` - sent eleven steps earlier, against
        // holder pointers that no longer exist - is still outstanding.
        ray_inv(res.1[11]),
        has_token(res.1[11], d),
        res.1[11].using[d],
        res.1[11].requests.contains((d, b)),
        res.1[11].nodes == r10.nodes,
{
    // 11. D, at the head of its own queue, enters the critical section.
    let r11 = Raymond {
        privilege: r10.privilege,
        nodes: r10.nodes,
        holder: r10.holder,
        queue: r10.queue.insert(d, r10.queue[d].drop_first()),
        asked: r10.asked,
        using: r10.using.insert(d, true),
        requests: r10.requests,
    };
    assert(ray_step(r10, r11, RayStep::EnterCs { node: d }));
    lemma_ray_step_preserves_inv(r10, r11, RayStep::EnterCs { node: d });
    assert(has_token(r11, d));

    // 12. The adversarial tail: D's original request to B, sent back at step 2,
    // is redelivered now - after the token has travelled the whole path and
    // `holder[d]` has become `d`, so the topology it was routed against is long
    // gone. It is still deliverable, because `requests` records what was sent.
    assert(r11.holder[d] == d);
    assert(r11.requests.contains((d, b)));
    let r12 = Raymond {
        privilege: r11.privilege,
        nodes: r11.nodes,
        holder: r11.holder,
        queue: r11.queue.insert(b, r11.queue[b].push(d)),
        asked: r11.asked,
        using: r11.using,
        requests: r11.requests,
    };
    assert(ray_step(r11, r12, RayStep::ReceiveRequest { at: b, from: d }));
    theorem_delayed_request_delivery_is_safe(r11, r12, b, d);

    assert(has_token(r12, d));
    assert(r12.using[d]);
    assert(r12.nodes == r10.nodes);
    assert forall|m: Id| #[trigger] has_token(r12, m) implies m == d by {
        theorem_ray_at_most_one_token(r12, m, d);
    }
    assert(ray_inv(r11));
    assert(has_token(r11, d));
    assert(r11.using[d]);
    assert(r11.requests.contains((d, b)));
    assert(r11.nodes == r10.nodes);

    // Collect the last two steps into the run.
    assert(tr.len() == 11);
    let h11 = RayStep::EnterCs { node: d };
    let tr11 = tr.push(r11);
    let l11 = labels.push(h11);
    lemma_ray_run_push(tr, labels, r11, h11);
    assert(tr11.len() == 12);
    assert(l11.len() == 11);
    assert(tr11[0] == tr[0]);
    assert(tr11[11] == r11);
    assert(l11[10] == h11);
    assert(forall|i: int| 0 <= i < 10 ==> #[trigger] l11[i] == labels[i]);
    let h12 = RayStep::ReceiveRequest { at: b, from: d };
    let tr12 = tr11.push(r12);
    let l12 = l11.push(h12);
    lemma_ray_run_push(tr11, l11, r12, h12);
    assert(tr12.len() == 13);
    assert(l12.len() == 12);
    assert(tr12[0] == tr11[0]);
    assert(tr12[11] == tr11[11]);
    assert(tr12[12] == r12);
    assert(l12[10] == h11);
    assert(l12[11] == h12);
    assert forall|i: int| 0 <= i < 10 implies #[trigger] l12[i] == labels[i] by {
        assert(l11[i] == labels[i]);
    }
    assert(ray_run(tr12, l12));
    (r12, tr12, l12)
}

/// Requests route `D -> B -> A -> C`, then the token routes `C -> A -> B -> D`.
pub proof fn scenario_request_and_token_routing(a: Id, b: Id, c: Id, d: Id)
    requires
        a != b,
        a != c,
        a != d,
        b != c,
        b != d,
        c != d,
    ensures
        // One run, twelve steps, every one of them named.
        //
        // Pinning the start state was not enough. `ray_reachable_from` hides
        // which transitions were taken, so from this very tree a run in which
        // `A`, `B` and `D` each call `RequestCs` independently, deliver those
        // requests, and then serve their own queue heads reaches the same end
        // state - without `D`'s request ever being forwarded `B -> A -> C`,
        // which is the thing the scenario is named for.
        //
        // `labels == routing_labels(a, b, c, d)` is that claim. There is one
        // `RequestCs` in the run and it is `D`'s, so every later queue entry
        // traces back to it: `MakeRequest { node: b }` at index 3 can only fire
        // because `ReceiveRequest { at: b, from: d }` at index 2 put something
        // in `B`'s queue, and likewise for `A` at 5 and `C` at 6.
        exists|tr: Seq<Raymond>, labels: Seq<RayStep>|
            {
                &&& #[trigger] ray_run(tr, labels)
                &&& tr[0] == routing_init_state(a, b, c, d)
                &&& ray_init(tr[0], c)
                &&& has_token(tr[0], c)
                &&& labels == routing_labels(a, b, c, d)
                &&& tr.len() == 13
                // The delayed redelivery, at the index it occupies: `D` is in
                // its critical section holding the token, and the request it
                // sent at index 1 - against holder pointers that three
                // `AssignPrivilege` steps have since overwritten - is still
                // deliverable.
                &&& ray_inv(tr[11])
                &&& has_token(tr[11], d)
                &&& tr[11].using[d]
                &&& tr[11].requests.contains((d, b))
                &&& ray_inv(tr[12])
                &&& has_token(tr[12], d)
                &&& tr[12].using[d]
                &&& forall|m: Id| has_token(tr[12], m) ==> m == d
            },
{
    let (after_requests, tr_r, l_r) = routing_phase_requests(a, b, c, d);
    let (after_hops, tr_h, l_h) = routing_phase_token_hops(
        tr_r,
        l_r,
        after_requests,
        a,
        b,
        c,
        d,
    );
    let (fin, tr, labels) = routing_phase_delivery(tr_h, l_h, after_hops, b, d);

    assert(tr.len() == 13);
    assert(labels.len() == 12);
    assert(tr[0] == tr_h[0]);
    assert(tr_h[0] == tr_r[0]);
    assert(tr[0] == routing_init_state(a, b, c, d));
    assert(ray_init(tr[0], c));
    assert(has_token(tr[0], c));

    // Phase one's seven labels, carried through two phases of appending.
    assert forall|i: int| 0 <= i < 7 implies #[trigger] labels[i] == l_r[i] by {
        assert(l_h[i] == l_r[i]);
    }
    assert(labels[0] == (RayStep::RequestCs { node: d }));
    assert(labels[1] == (RayStep::MakeRequest { node: d }));
    assert(labels[2] == (RayStep::ReceiveRequest { at: b, from: d }));
    assert(labels[3] == (RayStep::MakeRequest { node: b }));
    assert(labels[4] == (RayStep::ReceiveRequest { at: a, from: b }));
    assert(labels[5] == (RayStep::MakeRequest { node: a }));
    assert(labels[6] == (RayStep::ReceiveRequest { at: c, from: a }));
    // Phase two's three, carried through one.
    assert forall|i: int| 7 <= i < 10 implies #[trigger] labels[i] == l_h[i] by {
    }
    assert(labels[7] == (RayStep::AssignPrivilege { node: c, head: a }));
    assert(labels[8] == (RayStep::AssignPrivilege { node: a, head: b }));
    assert(labels[9] == (RayStep::AssignPrivilege { node: b, head: d }));
    assert(labels[10] == (RayStep::EnterCs { node: d }));
    assert(labels[11] == (RayStep::ReceiveRequest { at: b, from: d }));

    let expected = routing_labels(a, b, c, d);
    assert(expected.len() == 12);
    assert_seqs_equal!(labels == expected);

    assert(tr[12] == fin);
    assert(ray_inv(fin));
    assert(has_token(fin, d));
    assert(fin.using[d]);
}

} // verus!
