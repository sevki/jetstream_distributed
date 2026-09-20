//! A concrete end-to-end composed execution.
//!
//! The composed theorems in [`crate::proofs::composed`] are all of the form
//! "every reachable composed state satisfies ...". Such statements are worth
//! nothing if no interesting composed state is reachable — if `composed_init`
//! were unsatisfiable, or if the guards on `PassToken` / `AcquireUnderToken`
//! were jointly unsatisfiable, every one of them would hold vacuously.
//!
//! This module rules that out by construction. It builds a complete handover
//! driven through *both* layers at once:
//!
//! ```text
//! init                     X: Unowned(41, A)      token: A       (A is the Raymond root)
//! Own(IssueGrant)          network += Grant(X, A, 41)
//! AcquireUnderToken(A)     X: Owned(A, 41)        token: A       A owns and holds the token
//! Own(BeginTransfer A->B)  X: Transferring(A, B, 41, 42)
//! Own(HandleRevoke A)      network += Released(X, A, 42)
//! Own(CompleteRelease)     X: Unowned(42, B)      network += Grant(X, B, 42)
//! Ray(RequestCs B)         B queues itself
//! Ray(MakeRequest B)       B routes a request to its holder, A
//! Ray(ReceiveRequest A<-B) A queues B
//! PassToken(A -> B)        token: B               (legal only because X is Unowned)
//! AcquireUnderToken(B)     X: Owned(B, 42)        token: B       B owns and holds the token
//! ```
//!
//! The end state is reachable, satisfies the composed invariant, and has `B`
//! holding both ownership at epoch 42 and the Raymond token — while `A` still
//! physically holds its epoch-41 token and has no authority at all.
#![allow(unused_imports)]

use vstd::assert_seqs_equal;
use vstd::prelude::*;

use crate::composed::*;
use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::composed::*;
use crate::proofs::raymond::*;
use crate::raymond::*;

verus! {

// ---------------------------------------------------------------------------
// The states the handover passes through
// ---------------------------------------------------------------------------
//
// Each phase ends in one of these and the next begins from it. Naming them
// keeps the phase contracts short enough to read, and states each hand-off
// condition once rather than once on each side of the boundary.

/// After phase one: the actor has been released at epoch 42, and `A` still
/// holds the token.
pub open spec fn handover_released_state(c: Composed, x: ActorId, a: NodeId, b: NodeId) -> bool {
    &&& c.actor == x
    &&& c.own.actors[x] == (OwnershipState::Unowned { epoch: 42, intended_owner: b })
    &&& c.own.live.contains(a)
    &&& c.own.live.contains(b)
    &&& c.own.network.contains(Message::Grant { actor: x, to: b, epoch: 42 })
    &&& c.own.issued.contains(Token { actor: x, epoch: 41, holder: a })
    &&& c.ray.nodes.contains(a)
    &&& c.ray.nodes.contains(b)
    &&& c.ray.holder[b] == a
    &&& has_token(c.ray, a)
    &&& c.ray.queue[a].len() == 0
    &&& c.ray.queue[b].len() == 0
    &&& !c.ray.asked[b]
    &&& !c.ray.using[a]
}

/// After phase two: `B`'s request has reached `A`, which now has `B` at the
/// head of its queue. The ownership layer is untouched by the whole phase.
pub open spec fn handover_requested_state(c: Composed, x: ActorId, a: NodeId, b: NodeId) -> bool {
    &&& c.actor == x
    &&& c.own.actors[x] == (OwnershipState::Unowned { epoch: 42, intended_owner: b })
    &&& c.own.live.contains(a)
    &&& c.own.live.contains(b)
    &&& c.own.network.contains(Message::Grant { actor: x, to: b, epoch: 42 })
    &&& c.own.issued.contains(Token { actor: x, epoch: 41, holder: a })
    &&& c.ray.nodes.contains(a)
    &&& c.ray.nodes.contains(b)
    &&& has_token(c.ray, a)
    &&& !c.ray.using[a]
    &&& c.ray.queue[a].len() == 1
    &&& c.ray.queue[a][0] == b
}

/// After phase three: the token is at `B`, and the actor is still unowned - the
/// routing layer moved first and conferred nothing by moving.
pub open spec fn handover_passed_state(c: Composed, x: ActorId, a: NodeId, b: NodeId) -> bool {
    &&& c.actor == x
    &&& c.own.actors[x] == (OwnershipState::Unowned { epoch: 42, intended_owner: b })
    &&& c.own.live.contains(b)
    &&& c.own.network.contains(Message::Grant { actor: x, to: b, epoch: 42 })
    &&& c.own.issued.contains(Token { actor: x, epoch: 41, holder: a })
    &&& has_token(c.ray, b)
}

/// The labels of the handover run, as a sequence: ten steps from
/// `composed_init` to `B` owning at epoch 42 while holding the token.
///
/// Written out as one spec function so that the phases and the scenario agree
/// on it by construction, and so the scenario's postcondition can say "the run
/// is *this*" in a single clause.
pub open spec fn handover_labels(x: ActorId, a: NodeId, b: NodeId) -> Seq<ComposedStep> {
    seq![
        ComposedStep::Own { own_step: Step::IssueGrant { actor: x } },
        ComposedStep::AcquireUnderToken { node: a },
        ComposedStep::Own { own_step: Step::BeginTransfer { actor: x, from: a, to: b } },
        ComposedStep::Own {
            own_step: Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
        },
        ComposedStep::Own { own_step: Step::CompleteRelease { actor: x } },
        ComposedStep::Ray { ray_step: RayStep::RequestCs { node: b } },
        ComposedStep::Ray { ray_step: RayStep::MakeRequest { node: b } },
        ComposedStep::Ray { ray_step: RayStep::ReceiveRequest { at: a, from: b } },
        ComposedStep::PassToken { node: a, head: b },
        ComposedStep::AcquireUnderToken { node: b },
    ]
}

/// Phase one of the handover: from `composed_init` to the point where the actor
/// has been released at epoch 42 and `A` still holds the token.
///
/// Returning the state with an *abstract* characterisation rather than letting
/// the caller keep the literal is what keeps the proof tractable: each phase
/// reasons about a handful of `insert`s over an opaque base instead of a dozen
/// nested `Map`/`Set` literals, which is what exhausted the solver before.
pub proof fn handover_phase_release(x: ActorId, a: NodeId, b: NodeId) -> (res: (
    Composed,
    Seq<Composed>,
    Seq<ComposedStep>,
))
    requires
        a != b,
    ensures
        // The run so far, with its labels. Every phase hands on the run it has
        // built rather than just the state it reached, which is what keeps the
        // finished scenario from being satisfiable by a different execution
        // that merely ends somewhere similar.
        composed_labelled_execution(res.1, res.2),
        res.1[res.1.len() - 1] == res.0,
        composed_inv(res.0),
        handover_released_state(res.0, x, a, b),
        res.2.len() == 5,
        res.2[0] == (ComposedStep::Own { own_step: Step::IssueGrant { actor: x } }),
        res.2[1] == (ComposedStep::AcquireUnderToken { node: a }),
        res.2[2] == (ComposedStep::Own {
            own_step: Step::BeginTransfer { actor: x, from: a, to: b },
        }),
        res.2[3] == (ComposedStep::Own {
            own_step: Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
        }),
        res.2[4] == (ComposedStep::Own { own_step: Step::CompleteRelease { actor: x } }),
        res.1.len() == 6,
        // The epochs the scenario is named for, at the indices they occur at.
        // The labels alone do not carry them: `BeginTransfer` names the actor
        // and the two nodes, and takes its epochs from the state it fires in,
        // so a run with this exact label sequence could transfer 39 -> 40.
        res.1[3].own.actors[x] == (OwnershipState::Transferring {
            from: a,
            to: b,
            old_epoch: 41,
            new_epoch: 42,
        }),
        res.1[4].own.actors[x] == (OwnershipState::Transferring {
            from: a,
            to: b,
            old_epoch: 41,
            new_epoch: 42,
        }),
        res.1[5] == res.0,
{
    let nodes = Set::<NodeId>::empty().insert(a).insert(b);
    let stale = Token { actor: x, epoch: 41, holder: a };
    let empty_q = Seq::<NodeId>::empty();

    let own0 = System {
        actors: Map::<ActorId, OwnershipState>::empty().insert(
            x,
            OwnershipState::Unowned { epoch: 41, intended_owner: a },
        ),
        nodes: nodes,
        live: nodes,
        issued: Set::<Token>::empty(),
        network: Set::<Message>::empty(),
    };
    let ray0 = Raymond {
        privilege: a,
        nodes: nodes,
        holder: Map::<NodeId, NodeId>::empty().insert(a, a).insert(b, a),
        queue: Map::<NodeId, Seq<NodeId>>::empty().insert(a, empty_q).insert(b, empty_q),
        asked: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        using: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        requests: Set::<(NodeId, NodeId)>::empty(),
    };
    assert(ray0.holder[a] == a);
    assert(ray0.holder[b] == a);
    // `ray_init` requires the holder pointers to be acyclic; `A` is the root and
    // `B` is its only child, so ranking `A` below `B` witnesses it.
    let ray_rank = Map::new(ray0.nodes, |k: NodeId| if k == a { 0nat } else { 1nat });
    assert forall|n: NodeId| #[trigger] ray0.nodes.contains(n) implies ray_rank.contains_key(n) by {
    }
    assert forall|n: NodeId|
        ray0.nodes.contains(n) && #[trigger] ray0.holder[n] != n implies ray_rank[ray0.holder[n]]
            < ray_rank[n] by {
        assert(n == a || n == b);
        assert(n != a);
        assert(ray0.holder[b] == a);
    }
    assert(ray_ranked_by(ray0, ray_rank));
    assert(ray_acyclic(ray0));
    assert(ray_init(ray0, a));

    let c0 = Composed { own: own0, ray: ray0, actor: x, seized: Set::<NodeId>::empty() };
    assert(own0.actors.contains_key(x));
    assert(init(own0));
    assert(own0.nodes == ray0.nodes);
    assert(composed_init(c0));
    lemma_composed_reachable_init(c0);
    lemma_composed_init_inv(c0);
    assert(has_token(c0.ray, a));

    // 1. publish the grant for epoch 41
    let grant_41 = Message::Grant { actor: x, to: a, epoch: 41 };
    let c1 = Composed {
        own: System {
            actors: own0.actors,
            nodes: own0.nodes,
            live: own0.live,
            issued: own0.issued,
            network: own0.network.insert(grant_41),
        },
        ray: c0.ray,
        actor: x,
        seized: c0.seized,
    };
    let s1 = ComposedStep::Own { own_step: Step::IssueGrant { actor: x } };
    assert(step(c0.own, c1.own, Step::IssueGrant { actor: x }));
    assert(composed_step(c0, c1, s1));
    lemma_composed_reachable_step(c0, c1, s1);
    theorem_composed_step_preserves_inv(c0, c1, s1);

    // 2. A takes ownership - permitted only because it holds the token
    let c2 = Composed {
        own: System {
            actors: c1.own.actors.insert(x, OwnershipState::Owned { owner: a, epoch: 41 }),
            nodes: c1.own.nodes,
            live: c1.own.live,
            issued: c1.own.issued.insert(stale),
            network: c1.own.network,
        },
        ray: c1.ray,
        actor: x,
        seized: c1.seized,
    };
    let s2 = ComposedStep::AcquireUnderToken { node: a };
    assert(c1.own.live.contains(a));
    assert(c1.own.network.contains(grant_41));
    assert(has_token(c1.ray, a));
    assert(tr_acquire(c1.own, c2.own, x, a));
    assert(composed_step(c1, c2, s2));
    lemma_composed_reachable_step(c1, c2, s2);
    theorem_composed_step_preserves_inv(c1, c2, s2);
    assert(may_mutate(c2.own.actors[x], a, 41));

    // 3. the handover begins; A is fenced out immediately
    let revoke = Message::Revoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 };
    let c3 = Composed {
        own: System {
            actors: c2.own.actors.insert(
                x,
                OwnershipState::Transferring { from: a, to: b, old_epoch: 41, new_epoch: 42 },
            ),
            nodes: c2.own.nodes,
            live: c2.own.live,
            issued: c2.own.issued,
            network: c2.own.network.insert(revoke),
        },
        ray: c2.ray,
        actor: x,
        seized: c2.seized,
    };
    let s3 = ComposedStep::Own { own_step: Step::BeginTransfer { actor: x, from: a, to: b } };
    assert(c2.own.nodes.contains(b));
    assert(step(c2.own, c3.own, Step::BeginTransfer { actor: x, from: a, to: b }));
    assert(composed_step(c2, c3, s3));
    lemma_composed_reachable_step(c2, c3, s3);
    theorem_composed_step_preserves_inv(c2, c3, s3);

    // 4. A acknowledges
    let released = Message::Released { actor: x, from: a, new_epoch: 42 };
    let c4 = Composed {
        own: System {
            actors: c3.own.actors,
            nodes: c3.own.nodes,
            live: c3.own.live,
            issued: c3.own.issued,
            network: c3.own.network.insert(released),
        },
        ray: c3.ray,
        actor: x,
        seized: c3.seized,
    };
    let s4 = ComposedStep::Own {
        own_step: Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
    };
    assert(c3.own.live.contains(a));
    assert(c3.own.network.contains(revoke));
    assert(composed_step(c3, c4, s4));
    lemma_composed_reachable_step(c3, c4, s4);
    theorem_composed_step_preserves_inv(c3, c4, s4);

    // 5. the actor becomes unowned at 42 - only now may the token move
    let grant_42 = Message::Grant { actor: x, to: b, epoch: 42 };
    let c5 = Composed {
        own: System {
            actors: c4.own.actors.insert(
                x,
                OwnershipState::Unowned { epoch: 42, intended_owner: b },
            ),
            nodes: c4.own.nodes,
            live: c4.own.live,
            issued: c4.own.issued,
            network: c4.own.network.insert(grant_42),
        },
        ray: c4.ray,
        actor: x,
        seized: c4.seized,
    };
    let s5 = ComposedStep::Own { own_step: Step::CompleteRelease { actor: x } };
    assert(c4.own.network.contains(released));
    assert(step(c4.own, c5.own, Step::CompleteRelease { actor: x }));
    assert(composed_step(c4, c5, s5));
    lemma_composed_reachable_step(c4, c5, s5);
    theorem_composed_step_preserves_inv(c4, c5, s5);
    assert(is_unowned(c5.own.actors[x]));
    assert(has_token(c5.ray, a));
    // Nothing in this phase crashes anyone, so `A` is still live and can hand
    // the token on itself - which `cs_pass_token` now requires.
    assert(c5.own.live.contains(a));
    assert(c5.own.live.contains(b));
    assert(is_transferring(c4.own.actors[x]));

    // Collect the five steps into the run.
    let tr0 = seq![c0];
    let l0 = Seq::<ComposedStep>::empty();
    lemma_composed_run_init(c0);
    let tr1 = tr0.push(c1);
    let l1 = l0.push(s1);
    lemma_composed_run_push(tr0, l0, c1, s1);
    assert(tr1.len() == 2);
    assert(l1.len() == 1);
    assert(tr1[0] == c0);
    assert(tr1[1] == c1);
    assert(l1[0] == s1);
    let tr2 = tr1.push(c2);
    let l2 = l1.push(s2);
    lemma_composed_run_push(tr1, l1, c2, s2);
    assert(tr2.len() == 3);
    assert(l2.len() == 2);
    assert(tr2[0] == c0);
    assert(tr2[2] == c2);
    assert(l2[0] == s1);
    assert(l2[1] == s2);
    let tr3 = tr2.push(c3);
    let l3 = l2.push(s3);
    lemma_composed_run_push(tr2, l2, c3, s3);
    assert(tr3.len() == 4);
    assert(l3.len() == 3);
    assert(tr3[0] == c0);
    assert(tr3[3] == c3);
    assert(l3[0] == s1);
    assert(l3[1] == s2);
    assert(l3[2] == s3);
    let tr4 = tr3.push(c4);
    let l4 = l3.push(s4);
    lemma_composed_run_push(tr3, l3, c4, s4);
    assert(tr4.len() == 5);
    assert(l4.len() == 4);
    assert(tr4[0] == c0);
    assert(tr4[4] == c4);
    assert(l4[0] == s1);
    assert(l4[1] == s2);
    assert(l4[2] == s3);
    assert(l4[3] == s4);
    let tr5 = tr4.push(c5);
    let l5 = l4.push(s5);
    lemma_composed_run_push(tr4, l4, c5, s5);
    assert(tr5.len() == 6);
    assert(l5.len() == 5);
    assert(tr5[0] == c0);
    assert(tr5[5] == c5);
    assert(l5[0] == s1);
    assert(l5[1] == s2);
    assert(l5[2] == s3);
    assert(l5[3] == s4);
    assert(l5[4] == s5);
    assert(composed_init(tr5[0]));
    assert(composed_labelled_execution(tr5, l5));
    assert(handover_released_state(c5, x, a, b));
    assert(tr5[3] == c3);
    assert(tr5[4] == c4);
    (c5, tr5, l5)
}

/// Phase two: `B` asks for the token and the request reaches `A`.
///
/// Routing only - `own` is untouched, which is what lets phase three take the
/// ownership side abstractly. The mid state is handed on as a characterisation
/// rather than a literal, so no single query ever carries the whole handover.
pub proof fn handover_phase_request(
    tr: Seq<Composed>,
    labels: Seq<ComposedStep>,
    c: Composed,
    x: ActorId,
    a: NodeId,
    b: NodeId,
) -> (res: (Composed, Seq<Composed>, Seq<ComposedStep>))
    requires
        a != b,
        composed_labelled_execution(tr, labels),
        tr[tr.len() - 1] == c,
        labels.len() == 5,
        composed_inv(c),
        handover_released_state(c, x, a, b),
    ensures
        composed_labelled_execution(res.1, res.2),
        res.1[res.1.len() - 1] == res.0,
        composed_inv(res.0),
        handover_requested_state(res.0, x, a, b),
        res.0.own == c.own,
        res.2.len() == 8,
        // The phase appends to the run it was given; it does not start a new
        // one. This is what carries phase one's `CompleteRelease` forward into
        // the finished scenario's label sequence.
        forall|i: int| 0 <= i < 5 ==> #[trigger] res.2[i] == labels[i],
        res.2[5] == (ComposedStep::Ray { ray_step: RayStep::RequestCs { node: b } }),
        res.2[6] == (ComposedStep::Ray { ray_step: RayStep::MakeRequest { node: b } }),
        res.2[7] == (ComposedStep::Ray { ray_step: RayStep::ReceiveRequest { at: a, from: b } }),
        res.1.len() == 9,
        forall|i: int| 0 <= i < tr.len() ==> #[trigger] res.1[i] == tr[i],
{
    // The run the phase was handed is its own evidence that `c` is
    // reachable; the phase does not need it as a separate hypothesis.
    lemma_composed_labelled_execution_is_execution(tr, labels);
    assert(composed_reachable(c));

    // 6. B asks for the token
    let c6 = Composed {
        own: c.own,
        ray: Raymond {
            privilege: c.ray.privilege,
            nodes: c.ray.nodes,
            holder: c.ray.holder,
            queue: c.ray.queue.insert(b, c.ray.queue[b].push(b)),
            asked: c.ray.asked,
            using: c.ray.using,
            requests: c.ray.requests,
        },
        actor: x,
        seized: c.seized,
    };
    let s6 = ComposedStep::Ray { ray_step: RayStep::RequestCs { node: b } };
    assert(composed_step(c, c6, s6));
    lemma_composed_reachable_step(c, c6, s6);
    theorem_composed_step_preserves_inv(c, c6, s6);

    // 7. B routes the request to its holder, A
    let c7 = Composed {
        own: c6.own,
        ray: Raymond {
            privilege: c6.ray.privilege,
            nodes: c6.ray.nodes,
            holder: c6.ray.holder,
            queue: c6.ray.queue,
            asked: c6.ray.asked.insert(b, true),
            using: c6.ray.using,
            requests: c6.ray.requests.insert((b, c6.ray.holder[b])),
        },
        actor: x,
        seized: c6.seized,
    };
    let s7 = ComposedStep::Ray { ray_step: RayStep::MakeRequest { node: b } };
    assert(c6.ray.holder[b] == a);
    assert(c6.ray.queue[b].len() == 1);
    assert(!c6.ray.asked[b]);
    assert(composed_step(c6, c7, s7));
    lemma_composed_reachable_step(c6, c7, s7);
    theorem_composed_step_preserves_inv(c6, c7, s7);

    // 8. A receives it and queues B
    let c8 = Composed {
        own: c7.own,
        ray: Raymond {
            privilege: c7.ray.privilege,
            nodes: c7.ray.nodes,
            holder: c7.ray.holder,
            queue: c7.ray.queue.insert(a, c7.ray.queue[a].push(b)),
            asked: c7.ray.asked,
            using: c7.ray.using,
            requests: c7.ray.requests,
        },
        actor: x,
        seized: c7.seized,
    };
    let s8 = ComposedStep::Ray { ray_step: RayStep::ReceiveRequest { at: a, from: b } };
    assert(c7.ray.requests.contains((b, a)));
    assert(composed_step(c7, c8, s8));
    lemma_composed_reachable_step(c7, c8, s8);
    theorem_composed_step_preserves_inv(c7, c8, s8);
    assert(c8.ray.queue[a].len() == 1);
    assert(c8.ray.queue[a][0] == b);

    assert(tr.len() == 6);
    let tr6 = tr.push(c6);
    let l6 = labels.push(s6);
    lemma_composed_run_push(tr, labels, c6, s6);
    assert(tr6.len() == tr.len() + 1);
    assert(l6.len() == 6);
    assert(tr6[0] == tr[0]);
    assert(tr6[6] == c6);
    assert(l6[5] == s6);
    assert(forall|i: int| 0 <= i < 5 ==> #[trigger] l6[i] == labels[i]);
    let tr7 = tr6.push(c7);
    let l7 = l6.push(s7);
    lemma_composed_run_push(tr6, l6, c7, s7);
    assert(l7.len() == 7);
    assert(tr7[0] == tr6[0]);
    assert(tr7[7] == c7);
    assert(l7[5] == s6);
    assert(l7[6] == s7);
    assert forall|i: int| 0 <= i < 5 implies #[trigger] l7[i] == labels[i] by {
        assert(l6[i] == labels[i]);
    }
    let tr8 = tr7.push(c8);
    let l8 = l7.push(s8);
    lemma_composed_run_push(tr7, l7, c8, s8);
    assert(l8.len() == 8);
    assert(tr8[0] == tr7[0]);
    assert(tr8[8] == c8);
    assert(l8[5] == s6);
    assert(l8[6] == s7);
    assert(l8[7] == s8);
    assert forall|i: int| 0 <= i < 5 implies #[trigger] l8[i] == labels[i] by {
        assert(l7[i] == labels[i]);
    }
    assert(composed_init(tr8[0]));
    assert forall|i: int| 0 <= i < tr.len() implies #[trigger] tr8[i] == tr[i] by {
        assert(tr7[i] == tr6[i]);
        assert(tr6[i] == tr[i]);
    }
    assert(composed_labelled_execution(tr8, l8));
    assert(handover_requested_state(c8, x, a, b));
    (c8, tr8, l8)
}

/// Phase three: the token moves `A -> B`.
///
/// This is the step the composed machine exists to constrain: `PassToken` is
/// legal only because the actor is `Unowned`, so the token cannot overtake the
/// release. It gets a function to itself because pairing it with the
/// acquisition put two `composed_inv` re-establishments over freshly built
/// `Map`/`Set` literals into one query, which alone exceeded the solver budget.
pub proof fn handover_phase_pass_token(
    tr: Seq<Composed>,
    labels: Seq<ComposedStep>,
    c: Composed,
    x: ActorId,
    a: NodeId,
    b: NodeId,
) -> (res: (Composed, Seq<Composed>, Seq<ComposedStep>))
    requires
        a != b,
        composed_labelled_execution(tr, labels),
        tr[tr.len() - 1] == c,
        labels.len() == 8,
        composed_inv(c),
        handover_requested_state(c, x, a, b),
    ensures
        composed_labelled_execution(res.1, res.2),
        res.1[res.1.len() - 1] == res.0,
        composed_inv(res.0),
        handover_passed_state(res.0, x, a, b),
        res.0.own == c.own,
        res.2.len() == 9,
        forall|i: int| 0 <= i < 8 ==> #[trigger] res.2[i] == labels[i],
        res.2[8] == (ComposedStep::PassToken { node: a, head: b }),
        res.1.len() == 10,
        forall|i: int| 0 <= i < tr.len() ==> #[trigger] res.1[i] == tr[i],
{
    // The run the phase was handed is its own evidence that `c` is
    // reachable; the phase does not need it as a separate hypothesis.
    lemma_composed_labelled_execution_is_execution(tr, labels);
    assert(composed_reachable(c));

    let c9 = Composed {
        own: c.own,
        ray: Raymond {
            privilege: b,
            nodes: c.ray.nodes,
            holder: c.ray.holder.insert(a, b).insert(b, b),
            queue: c.ray.queue.insert(a, c.ray.queue[a].drop_first()),
            asked: c.ray.asked.insert(a, false),
            using: c.ray.using,
            requests: c.ray.requests,
        },
        actor: x,
        seized: c.seized.remove(b),
    };
    let s9 = ComposedStep::PassToken { node: a, head: b };
    assert(is_unowned(c.own.actors[x]));
    assert(c.own.live.contains(a));
    assert(composed_step(c, c9, s9));
    lemma_composed_reachable_step(c, c9, s9);
    theorem_composed_step_preserves_inv(c, c9, s9);
    lemma_composed_pass_token_preserves_inv(c, c9, a, b);
    assert(has_token(c9.ray, b));

    assert(tr.len() == 9);
    let tr9 = tr.push(c9);
    let l9 = labels.push(s9);
    lemma_composed_run_push(tr, labels, c9, s9);
    assert(l9.len() == 9);
    assert(tr9[0] == tr[0]);
    assert(tr9[9] == c9);
    assert(l9[8] == s9);
    assert(forall|i: int| 0 <= i < 8 ==> #[trigger] l9[i] == labels[i]);
    assert(composed_init(tr9[0]));
    assert forall|i: int| 0 <= i < tr.len() implies #[trigger] tr9[i] == tr[i] by {
    }
    assert(composed_labelled_execution(tr9, l9));
    assert(handover_passed_state(c9, x, a, b));
    (c9, tr9, l9)
}

/// Phase four: `B` takes ownership at epoch 42, holding the token.
///
/// `AcquireUnderToken` is legal only because `B` holds the token - authority
/// cannot be taken by a node routing has not elected.
pub proof fn handover_phase_acquire(
    tr: Seq<Composed>,
    labels: Seq<ComposedStep>,
    c: Composed,
    x: ActorId,
    a: NodeId,
    b: NodeId,
) -> (res: (Composed, Seq<Composed>, Seq<ComposedStep>))
    requires
        a != b,
        composed_labelled_execution(tr, labels),
        tr[tr.len() - 1] == c,
        labels.len() == 9,
        composed_inv(c),
        handover_passed_state(c, x, a, b),
    ensures
        composed_labelled_execution(res.1, res.2),
        res.1[res.1.len() - 1] == res.0,
        composed_inv(res.0),
        res.0.actor == x,
        res.0.own.actors[x] == (OwnershipState::Owned { owner: b, epoch: 42 }),
        has_token(res.0.ray, b),
        res.0.own.issued.contains(Token { actor: x, epoch: 41, holder: a }),
        res.2.len() == 10,
        forall|i: int| 0 <= i < 9 ==> #[trigger] res.2[i] == labels[i],
        res.2[9] == (ComposedStep::AcquireUnderToken { node: b }),
        res.1.len() == 11,
        forall|i: int| 0 <= i < tr.len() ==> #[trigger] res.1[i] == tr[i],
{
    // The run the phase was handed is its own evidence that `c` is
    // reachable; the phase does not need it as a separate hypothesis.
    lemma_composed_labelled_execution_is_execution(tr, labels);
    assert(composed_reachable(c));

    let c10 = Composed {
        own: System {
            actors: c.own.actors.insert(x, OwnershipState::Owned { owner: b, epoch: 42 }),
            nodes: c.own.nodes,
            live: c.own.live,
            issued: c.own.issued.insert(Token { actor: x, epoch: 42, holder: b }),
            network: c.own.network,
        },
        ray: c.ray,
        actor: x,
        seized: c.seized,
    };
    let s10 = ComposedStep::AcquireUnderToken { node: b };
    assert(tr_acquire(c.own, c10.own, x, b));
    assert(composed_step(c, c10, s10));
    lemma_composed_reachable_step(c, c10, s10);
    theorem_composed_step_preserves_inv(c, c10, s10);

    assert(tr.len() == 10);
    let tr10 = tr.push(c10);
    let l10 = labels.push(s10);
    lemma_composed_run_push(tr, labels, c10, s10);
    assert(l10.len() == 10);
    assert(tr10[0] == tr[0]);
    assert(tr10[10] == c10);
    assert(l10[9] == s10);
    assert(forall|i: int| 0 <= i < 9 ==> #[trigger] l10[i] == labels[i]);
    assert(composed_init(tr10[0]));
    assert forall|i: int| 0 <= i < tr.len() implies #[trigger] tr10[i] == tr[i] by {
    }
    assert(composed_labelled_execution(tr10, l10));
    (c10, tr10, l10)
}

/// A full ownership handover coordinated across both layers.
///
/// This is the non-vacuity witness for every `composed_reachable` theorem: it
/// exhibits a reachable composed state in which somebody actually owns the actor
/// and actually holds the token.
pub proof fn scenario_composed_handover(x: ActorId, a: NodeId, b: NodeId)
    requires
        a != b,
    ensures
        // One run, ten steps, every one of them named.
        //
        // The previous contract exported a `CompleteRelease` step, a
        // `PassToken` step and an endpoint, tied together by
        // `composed_reachable_from`. Each of those existentials could be
        // satisfied from a *different* execution, so the conjunction did not
        // describe a single run: complete an unrelated `A -> B` transfer at
        // epochs 39 -> 40, then acquire `A@41`, then reach `B@42` by
        // `RevokeOwner`, pass the token and acquire. Every clause held, and
        // the advertised 41 -> 42 release never happened.
        //
        // `labels == handover_labels(x, a, b)` leaves nothing to assemble from
        // elsewhere. There is exactly one run, its steps are fixed, and the
        // release at index 4 is the one whose `BeginTransfer` at index 2 opened
        // the 41 -> 42 transfer and whose `PassToken` at index 8 and
        // `AcquireUnderToken` at index 9 finish it.
        exists|tr: Seq<Composed>, labels: Seq<ComposedStep>|
            {
                &&& #[trigger] composed_labelled_execution(tr, labels)
                &&& labels == handover_labels(x, a, b)
                &&& tr.len() == 11
                // The transfer is opened and closed on the epochs the scenario
                // is named for, in this run.
                &&& tr[3].own.actors[x] == (OwnershipState::Transferring {
                    from: a,
                    to: b,
                    old_epoch: 41,
                    new_epoch: 42,
                })
                &&& is_transferring(tr[4].own.actors[x])
                &&& tr[5].own.actors[x] == (OwnershipState::Unowned {
                    epoch: 42,
                    intended_owner: b,
                })
                // The token is handed on by a live `A`, after the release and
                // not before it.
                &&& tr[8].own.live.contains(a)
                &&& has_token(tr[8].ray, a)
                &&& has_token(tr[9].ray, b)
                // And the outcome.
                &&& tr[10].actor == x
                &&& may_mutate(tr[10].own.actors[x], b, 42)
                &&& !may_mutate(tr[10].own.actors[x], a, 41)
                &&& has_token(tr[10].ray, b)
                &&& tr[10].own.issued.contains(Token { actor: x, epoch: 41, holder: a })
            },
{
    let (released, tr_r, l_r) = handover_phase_release(x, a, b);
    let (requested, tr_q, l_q) = handover_phase_request(tr_r, l_r, released, x, a, b);
    let (passed, tr_p, l_p) = handover_phase_pass_token(tr_q, l_q, requested, x, a, b);
    let (fin, tr, labels) = handover_phase_acquire(tr_p, l_p, passed, x, a, b);

    assert(labels.len() == 10);
    assert(tr.len() == 11);

    // Phase one's five labels, carried through three phases of appending.
    assert forall|i: int| 0 <= i < 5 implies #[trigger] labels[i] == l_r[i] by {
        assert(l_p[i] == l_q[i]);
        assert(l_q[i] == l_r[i]);
    }
    assert(labels[0] == ComposedStep::Own { own_step: Step::IssueGrant { actor: x } });
    assert(labels[1] == ComposedStep::AcquireUnderToken { node: a });
    assert(labels[2] == ComposedStep::Own {
        own_step: Step::BeginTransfer { actor: x, from: a, to: b },
    });
    assert(labels[3] == ComposedStep::Own {
        own_step: Step::HandleRevoke { actor: x, target: a, old_epoch: 41, new_epoch: 42 },
    });
    assert(labels[4] == ComposedStep::Own { own_step: Step::CompleteRelease { actor: x } });

    // Phase two's three, carried through two phases of appending.
    assert forall|i: int| 5 <= i < 8 implies #[trigger] labels[i] == l_q[i] by {
        assert(l_p[i] == l_q[i]);
    }
    assert(labels[5] == ComposedStep::Ray { ray_step: RayStep::RequestCs { node: b } });
    assert(labels[6] == ComposedStep::Ray { ray_step: RayStep::MakeRequest { node: b } });
    assert(labels[7] == ComposedStep::Ray {
        ray_step: RayStep::ReceiveRequest { at: a, from: b },
    });
    // Phase three's one, carried through one.
    assert(labels[8] == l_p[8]);
    assert(labels[8] == ComposedStep::PassToken { node: a, head: b });
    assert(labels[9] == ComposedStep::AcquireUnderToken { node: b });

    let expected = handover_labels(x, a, b);
    assert(expected.len() == 10);
    assert_seqs_equal!(labels == expected);

    // The states, at the indices the postcondition names. Same shape as the
    // labels: each phase preserved the run it was handed, so a fact proved
    // about `tr_r[3]` in phase one is a fact about `tr[3]` at the end.
    assert(tr_q[3] == tr_r[3]);
    assert(tr_p[3] == tr_q[3]);
    assert(tr[3] == tr_p[3]);
    assert(tr_q[4] == tr_r[4]);
    assert(tr_p[4] == tr_q[4]);
    assert(tr[4] == tr_p[4]);
    assert(tr_q[5] == tr_r[5]);
    assert(tr_p[5] == tr_q[5]);
    assert(tr[5] == tr_p[5]);
    assert(tr_r[5] == released);
    assert(is_transferring(tr[4].own.actors[x]));

    // The pass itself: `tr_q` ends at `requested`, which is the state
    // `PassToken` fires in, and `tr_p` ends at `passed`.
    assert(tr_q.len() == 9);
    assert(tr_q[8] == requested);
    assert(tr_p[8] == tr_q[8]);
    assert(tr[8] == tr_p[8]);
    assert(tr_p.len() == 10);
    assert(tr_p[9] == passed);
    assert(tr[9] == tr_p[9]);
    assert(tr[8].own.live.contains(a));
    assert(has_token(tr[8].ray, a));
    assert(has_token(tr[9].ray, b));

    assert(tr[10] == fin);
    assert(may_mutate(fin.own.actors[x], b, 42));
    assert(!may_mutate(fin.own.actors[x], a, 41));
}

/// **A reachable composed state in which a node is inside the critical section.**
///
/// `theorem_composed_admits_critical_section` only shows that an *already
/// assumed* `EnterCs` transition matches `ComposedStep::Ray`; it takes the
/// transition as a hypothesis and its `pre` is not required to be reachable, so
/// on its own it does not establish that any reachable composed state has
/// `using` set. This does: it drives `RequestCs`, `EnterCs` and `ExitCs` from
/// `composed_init` through `lemma_composed_reachable_step`.
pub proof fn scenario_composed_critical_section(x: ActorId, a: NodeId, b: NodeId)
    requires
        a != b,
    ensures
        // The run, with its labels. This scenario's old contract exported a
        // reachable state with `using` set and an `ExitCs` step as two
        // independent existentials; they could come from different executions,
        // and neither said that the node inside the critical section got there
        // by entering it. Three labels say it.
        exists|tr: Seq<Composed>, labels: Seq<ComposedStep>|
            {
                &&& #[trigger] composed_labelled_execution(tr, labels)
                &&& labels.len() == 3
                &&& labels[0] == (ComposedStep::Ray { ray_step: RayStep::RequestCs { node: a } })
                &&& labels[1] == (ComposedStep::Ray { ray_step: RayStep::EnterCs { node: a } })
                &&& labels[2] == (ComposedStep::Ray { ray_step: RayStep::ExitCs { node: a } })
                &&& !tr[0].ray.using[a]
                &&& !tr[1].ray.using[a]
                &&& tr[2].ray.using[a]
                &&& !tr[3].ray.using[a]
                &&& has_token(tr[2].ray, a)
            },
{
    let nodes = Set::<NodeId>::empty().insert(a).insert(b);
    let empty_q = Seq::<NodeId>::empty();

    let own0 = System {
        actors: Map::<ActorId, OwnershipState>::empty().insert(
            x,
            OwnershipState::Unowned { epoch: 41, intended_owner: a },
        ),
        nodes: nodes,
        live: nodes,
        issued: Set::<Token>::empty(),
        network: Set::<Message>::empty(),
    };
    let ray0 = Raymond {
        privilege: a,
        nodes: nodes,
        holder: Map::<NodeId, NodeId>::empty().insert(a, a).insert(b, a),
        queue: Map::<NodeId, Seq<NodeId>>::empty().insert(a, empty_q).insert(b, empty_q),
        asked: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        using: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        requests: Set::<(NodeId, NodeId)>::empty(),
    };
    assert(ray0.holder[a] == a);
    assert(ray0.holder[b] == a);
    // `ray_init` requires the holder pointers to be acyclic; `A` is the root and
    // `B` is its only child, so ranking `A` below `B` witnesses it.
    let ray_rank = Map::new(ray0.nodes, |k: NodeId| if k == a { 0nat } else { 1nat });
    assert forall|n: NodeId| #[trigger] ray0.nodes.contains(n) implies ray_rank.contains_key(n) by {
    }
    assert forall|n: NodeId|
        ray0.nodes.contains(n) && #[trigger] ray0.holder[n] != n implies ray_rank[ray0.holder[n]]
            < ray_rank[n] by {
        assert(n == a || n == b);
        assert(n != a);
        assert(ray0.holder[b] == a);
    }
    assert(ray_ranked_by(ray0, ray_rank));
    assert(ray_acyclic(ray0));
    assert(ray_init(ray0, a));

    let c0 = Composed { own: own0, ray: ray0, actor: x, seized: Set::<NodeId>::empty() };
    assert(own0.actors.contains_key(x));
    assert(init(own0));
    assert(own0.nodes == ray0.nodes);
    assert(composed_init(c0));
    lemma_composed_reachable_init(c0);
    lemma_composed_init_inv(c0);
    assert(has_token(c0.ray, a));

    // 1. A queues itself.
    let c1 = Composed {
        own: c0.own,
        ray: Raymond {
            privilege: c0.ray.privilege,
            nodes: c0.ray.nodes,
            holder: c0.ray.holder,
            queue: c0.ray.queue.insert(a, c0.ray.queue[a].push(a)),
            asked: c0.ray.asked,
            using: c0.ray.using,
            requests: c0.ray.requests,
        },
        actor: x,
        seized: c0.seized,
    };
    let s1 = ComposedStep::Ray { ray_step: RayStep::RequestCs { node: a } };
    assert(composed_step(c0, c1, s1));
    lemma_composed_reachable_step(c0, c1, s1);
    theorem_composed_step_preserves_inv(c0, c1, s1);

    // 2. A is at the head of its own queue and holds the token, so it enters.
    let c2 = Composed {
        own: c1.own,
        ray: Raymond {
            privilege: c1.ray.privilege,
            nodes: c1.ray.nodes,
            holder: c1.ray.holder,
            queue: c1.ray.queue.insert(a, c1.ray.queue[a].drop_first()),
            asked: c1.ray.asked,
            using: c1.ray.using.insert(a, true),
            requests: c1.ray.requests,
        },
        actor: x,
        seized: c1.seized,
    };
    let s2 = ComposedStep::Ray { ray_step: RayStep::EnterCs { node: a } };
    assert(has_token(c1.ray, a));
    assert(!c1.ray.using[a]);
    assert(c1.ray.queue[a].len() == 1);
    assert(c1.ray.queue[a][0] == a);
    assert(composed_step(c1, c2, s2));
    lemma_composed_reachable_step(c1, c2, s2);
    theorem_composed_step_preserves_inv(c1, c2, s2);

    // A reachable composed state with `using` actually set.
    assert(composed_reachable(c2));
    assert(c2.ray.using[a]);

    // 3. And A can leave again.
    let c3 = Composed {
        own: c2.own,
        ray: Raymond {
            privilege: c2.ray.privilege,
            nodes: c2.ray.nodes,
            holder: c2.ray.holder,
            queue: c2.ray.queue,
            asked: c2.ray.asked,
            using: c2.ray.using.insert(a, false),
            requests: c2.ray.requests,
        },
        actor: x,
        seized: c2.seized,
    };
    let s3 = ComposedStep::Ray { ray_step: RayStep::ExitCs { node: a } };
    assert(c2.ray.using[a]);
    assert(composed_step(c2, c3, s3));
    lemma_composed_reachable_step(c2, c3, s3);
    theorem_composed_step_preserves_inv(c2, c3, s3);

    assert(composed_reachable(c3));
    assert(c2.ray.using[a]);
    assert(!c3.ray.using[a]);

    let tr = seq![c0, c1, c2, c3];
    let labels = seq![s1, s2, s3];
    assert(tr.len() == 4);
    assert(labels.len() == 3);
    assert(tr[0] == c0);
    assert(tr[1] == c1);
    assert(tr[2] == c2);
    assert(tr[3] == c3);
    assert(labels[0] == s1);
    assert(labels[1] == s2);
    assert(labels[2] == s3);
    assert forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() implies composed_step(tr[i], tr[i + 1], labels[i]) by {
        if i == 0 {
            assert(composed_step(c0, c1, s1));
        } else if i == 1 {
            assert(composed_step(c1, c2, s2));
        } else {
            assert(i == 2);
            assert(composed_step(c2, c3, s3));
        }
    }
    assert(composed_run(tr, labels));
    assert(composed_init(tr[0]));
    assert(composed_labelled_execution(tr, labels));
    assert(!c0.ray.using[a]);
    assert(!c1.ray.using[a]);
    assert(has_token(c2.ray, a));
}

/// **Crash-driven takeover, in the composed machine.**
///
/// This is the execution the composed layer could not represent before
/// `ComposedStep::SeizeToken` existed, and it is the one the ownership layer
/// has epochs *for*:
///
/// ```text
/// init                   X: Unowned(41, A)     token: A    live: {A, B}
/// Own(IssueGrant)        network += Grant(X, A, 41)
/// AcquireUnderToken(A)   X: Owned(A, 41)       token: A    A owns and holds the token
/// Own(Crash A)                                             live: {B}
/// Own(RevokeOwner X->B)  X: Unowned(42, B)     network += Grant(X, B, 42)
/// SeizeToken(A -> B)     token: B                          A never acts again
/// AcquireUnderToken(B)   X: Owned(B, 42)       token: B
/// ```
///
/// The point is the last three steps. `A` crashes and takes **no further step**
/// - it is not in `live`, and nothing after the crash is an `A` action. The
/// coordinator burns the epoch, the token is seized, and `B` takes over. Under
/// the old machine this was not reachable: the only token movement was
/// `PassToken`, which requires `has_token(pre.ray, A)` and models `A` handing
/// the privilege on, so the composed theorems were quantified over executions
/// in which the dead node cooperates.
///
/// `A`'s epoch-41 token is still in `issued` at the end, and still confers
/// nothing.
pub proof fn scenario_composed_crash_takeover(x: ActorId, a: NodeId, b: NodeId)
    requires
        a != b,
    ensures
        // The whole run, with every step named.
        //
        // Earlier versions of this contract exported the seizure and the
        // takeover as separate existentials tied together by
        // `composed_reachable_from`. That is weaker than it reads: the steps a
        // `composed_reachable_from` run took are hidden inside
        // `composed_next`, so nothing forced the epoch to have been burned by
        // a *revocation*. The run
        // `Acquire(A@41) -> BeginTransfer -> HandleRevoke -> CompleteRelease
        // -> Crash(A) -> SeizeToken -> Acquire(B@42)` satisfied every clause
        // while `A` gave the actor up voluntarily before crashing, which is
        // the opposite of the scenario this theorem is named for.
        //
        // Exhibiting `labels` settles it. The run is these eight steps and
        // nothing else: `Crash` at index 2 and `RevokeOwner` at index 3 are
        // *in* it, and there is no `CompleteRelease` anywhere in it to let a
        // voluntary release stand in for the crash.
        exists|tr: Seq<Composed>, labels: Seq<ComposedStep>|
            {
                &&& #[trigger] composed_labelled_execution(tr, labels)
                &&& labels.len() == 8
                &&& labels[0] == ComposedStep::Own {
                    own_step: Step::IssueGrant { actor: x },
                }
                &&& labels[1] == ComposedStep::AcquireUnderToken { node: a }
                &&& labels[2] == ComposedStep::Own { own_step: Step::Crash { node: a } }
                &&& labels[3] == ComposedStep::Own {
                    own_step: Step::RevokeOwner { actor: x, next: b },
                }
                &&& labels[4] == ComposedStep::SeizeToken { from: a, to: b }
                &&& labels[5] == ComposedStep::AcquireUnderToken { node: b }
                &&& labels[6] == ComposedStep::Reconcile { node: a }
                &&& labels[7] == ComposedStep::Own { own_step: Step::Recover { node: a } }
                &&& tr[0].actor == x
                // The state the seizure fires from: `A` has crashed, its epoch
                // has been burned by the revocation at index 3, and it still
                // holds the token. These are facts about `tr` at the index the
                // seizure actually occupies, not about some other state of the
                // same shape.
                &&& !tr[4].own.live.contains(a)
                &&& is_unowned(tr[4].own.actors[x])
                &&& has_token(tr[4].ray, a)
                &&& has_token(tr[5].ray, b)
                // `A` is marked as having had its token seized, and has to
                // reconcile before it may come back.
                &&& tr[6].seized.contains(a)
                &&& !tr[7].seized.contains(a)
                // The end of the run: `B` owns at 42 and holds the token, `A`
                // is back with its epoch-41 token still issued and still
                // worthless.
                &&& tr[8].actor == x
                &&& may_mutate(tr[8].own.actors[x], b, 42)
                &&& !may_mutate(tr[8].own.actors[x], a, 41)
                &&& tr[8].own.issued.contains(Token { actor: x, epoch: 41, holder: a })
                &&& has_token(tr[8].ray, b)
                &&& !has_token(tr[8].ray, a)
                &&& tr[8].own.live.contains(a)
                &&& !tr[8].seized.contains(a)
            },
{
    let nodes = Set::<NodeId>::empty().insert(a).insert(b);
    let empty_q = Seq::<NodeId>::empty();
    let stale = Token { actor: x, epoch: 41, holder: a };

    let own0 = System {
        actors: Map::<ActorId, OwnershipState>::empty().insert(
            x,
            OwnershipState::Unowned { epoch: 41, intended_owner: a },
        ),
        nodes: nodes,
        live: nodes,
        issued: Set::<Token>::empty(),
        network: Set::<Message>::empty(),
    };
    let ray0 = Raymond {
        privilege: a,
        nodes: nodes,
        holder: Map::<NodeId, NodeId>::empty().insert(a, a).insert(b, a),
        queue: Map::<NodeId, Seq<NodeId>>::empty().insert(a, empty_q).insert(b, empty_q),
        asked: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        using: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        requests: Set::<(NodeId, NodeId)>::empty(),
    };
    assert(ray0.holder[a] == a);
    assert(ray0.holder[b] == a);
    // `ray_init` requires the holder pointers to be acyclic; `A` is the root and
    // `B` is its only child, so ranking `A` below `B` witnesses it.
    let ray_rank = Map::new(ray0.nodes, |k: NodeId| if k == a { 0nat } else { 1nat });
    assert forall|n: NodeId| #[trigger] ray0.nodes.contains(n) implies ray_rank.contains_key(n) by {
    }
    assert forall|n: NodeId|
        ray0.nodes.contains(n) && #[trigger] ray0.holder[n] != n implies ray_rank[ray0.holder[n]]
            < ray_rank[n] by {
        assert(n == a || n == b);
        assert(n != a);
        assert(ray0.holder[b] == a);
    }
    assert(ray_ranked_by(ray0, ray_rank));
    assert(ray_acyclic(ray0));
    assert(ray_init(ray0, a));

    let c0 = Composed { own: own0, ray: ray0, actor: x, seized: Set::<NodeId>::empty() };
    assert(own0.actors.contains_key(x));
    assert(init(own0));
    assert(own0.nodes == ray0.nodes);
    assert(composed_init(c0));
    lemma_composed_reachable_init(c0);
    lemma_composed_init_inv(c0);
    assert(has_token(c0.ray, a));

    // 1. The coordinator offers X to A at epoch 41.
    let grant_41 = Message::Grant { actor: x, to: a, epoch: 41 };
    let c1 = Composed {
        own: System {
            actors: c0.own.actors,
            nodes: c0.own.nodes,
            live: c0.own.live,
            issued: c0.own.issued,
            network: c0.own.network.insert(grant_41),
        },
        ray: c0.ray,
        actor: x,
        seized: c0.seized,
    };
    let s1 = ComposedStep::Own { own_step: Step::IssueGrant { actor: x } };
    assert(composed_step(c0, c1, s1));
    lemma_composed_reachable_step(c0, c1, s1);
    theorem_composed_step_preserves_inv(c0, c1, s1);

    // 2. A takes ownership at 41, holding the token.
    let c2 = Composed {
        own: System {
            actors: c1.own.actors.insert(x, OwnershipState::Owned { owner: a, epoch: 41 }),
            nodes: c1.own.nodes,
            live: c1.own.live,
            issued: c1.own.issued.insert(stale),
            network: c1.own.network,
        },
        ray: c1.ray,
        actor: x,
        seized: c1.seized,
    };
    let s2 = ComposedStep::AcquireUnderToken { node: a };
    assert(has_token(c1.ray, a));
    assert(tr_acquire(c1.own, c2.own, x, a));
    assert(composed_step(c1, c2, s2));
    lemma_composed_reachable_step(c1, c2, s2);
    theorem_composed_step_preserves_inv(c1, c2, s2);
    assert(c2.own.issued.contains(stale));

    // 3. A crashes. It keeps its epoch-41 token, and takes no further step.
    let c3 = Composed {
        own: System {
            actors: c2.own.actors,
            nodes: c2.own.nodes,
            live: c2.own.live.remove(a),
            issued: c2.own.issued,
            network: c2.own.network,
        },
        ray: c2.ray,
        actor: x,
        seized: c2.seized,
    };
    let s3 = ComposedStep::Own { own_step: Step::Crash { node: a } };
    assert(c2.own.live.contains(a));
    assert(composed_step(c2, c3, s3));
    lemma_composed_reachable_step(c2, c3, s3);
    theorem_composed_step_preserves_inv(c2, c3, s3);
    assert(!c3.own.live.contains(a));
    assert(c3.own.live.contains(b));

    // 4. The failure detector fires: the epoch is burned and X is offered to B.
    let grant_42 = Message::Grant { actor: x, to: b, epoch: 42 };
    let c4 = Composed {
        own: System {
            actors: c3.own.actors.insert(
                x,
                OwnershipState::Unowned { epoch: 42, intended_owner: b },
            ),
            nodes: c3.own.nodes,
            live: c3.own.live,
            issued: c3.own.issued,
            network: c3.own.network.insert(grant_42),
        },
        ray: c3.ray,
        actor: x,
        seized: c3.seized,
    };
    let s4 = ComposedStep::Own { own_step: Step::RevokeOwner { actor: x, next: b } };
    assert(c3.own.actors[x] == (OwnershipState::Owned { owner: a, epoch: 41 }));
    assert(composed_step(c3, c4, s4));
    lemma_composed_reachable_step(c3, c4, s4);
    theorem_composed_step_preserves_inv(c3, c4, s4);
    assert(is_unowned(c4.own.actors[x]));
    assert(has_token(c4.ray, a));

    // 5. The token is seized from the crashed node. A does not act.
    let c5 = Composed {
        own: c4.own,
        // Seizure now touches only `b`. `A`'s holder, asked and using entries
        // are left exactly as they were, which is what makes it a stale holder
        // rather than a node the coordinator silently corrected.
        ray: Raymond {
            privilege: b,
            nodes: c4.ray.nodes,
            holder: c4.ray.holder.insert(b, b),
            queue: c4.ray.queue,
            asked: c4.ray.asked,
            using: c4.ray.using,
            requests: c4.ray.requests,
        },
        actor: x,
        seized: c4.seized.insert(a).remove(b),
    };
    let s5 = ComposedStep::SeizeToken { from: a, to: b };
    assert(!c4.own.live.contains(a));
    assert(ray_seize(c4.ray, c5.ray, a, b));
    assert(composed_step(c4, c5, s5));
    lemma_composed_reachable_step(c4, c5, s5);
    theorem_composed_step_preserves_inv(c4, c5, s5);
    lemma_composed_seize_preserves_inv(c4, c5, a, b);
    assert(has_token(c5.ray, b));

    // 6. B takes over at epoch 42, holding the token.
    let c6 = Composed {
        own: System {
            actors: c5.own.actors.insert(x, OwnershipState::Owned { owner: b, epoch: 42 }),
            nodes: c5.own.nodes,
            live: c5.own.live,
            issued: c5.own.issued.insert(Token { actor: x, epoch: 42, holder: b }),
            network: c5.own.network,
        },
        ray: c5.ray,
        actor: x,
        seized: c5.seized,
    };
    let s6 = ComposedStep::AcquireUnderToken { node: b };
    assert(c5.own.live.contains(b));
    assert(c5.own.network.contains(grant_42));
    assert(tr_acquire(c5.own, c6.own, x, b));
    assert(composed_step(c5, c6, s6));
    lemma_composed_reachable_step(c5, c6, s6);
    theorem_composed_step_preserves_inv(c5, c6, s6);

    assert(composed_reachable(c6));
    assert(c6.actor == x);
    assert(!c6.own.live.contains(a));
    assert(may_mutate(c6.own.actors[x], b, 42));
    assert(has_token(c6.ray, b));
    assert(c6.own.issued.contains(stale));
    assert(!may_mutate(c6.own.actors[x], a, 41));
    assert(c6.seized.contains(a));

    // 7. A reconciles. This is where its stale belief is actually dropped: the
    // seizure at step 5 left `holder[A] == A` and `using[A]` exactly as they
    // were, because nobody can reach into a crashed node, so until now `A` has
    // been a stale holder - believing it holds the privilege, holding nothing.
    assert(is_stale_holder(c6.ray, a));
    let c7 = Composed {
        own: c6.own,
        ray: Raymond {
            privilege: c6.ray.privilege,
            nodes: c6.ray.nodes,
            holder: c6.ray.holder.insert(a, c6.ray.privilege),
            queue: c6.ray.queue,
            asked: c6.ray.asked.insert(a, false),
            using: c6.ray.using.insert(a, false),
            requests: c6.ray.requests,
        },
        actor: x,
        seized: c6.seized.remove(a),
    };
    let s7 = ComposedStep::Reconcile { node: a };
    assert(c6.seized.contains(a));
    assert(ray_reconcile(c6.ray, c7.ray, a));
    assert(composed_step(c6, c7, s7));
    lemma_composed_reachable_step(c6, c7, s7);
    theorem_composed_step_preserves_inv(c6, c7, s7);
    assert(!c7.seized.contains(a));
    assert(!is_stale_holder(c7.ray, a));

    // 8. Only now may A come back - and it comes back with no authority, its
    // epoch-41 token still issued and still worthless, and no token.
    let c8 = Composed {
        own: System {
            actors: c7.own.actors,
            nodes: c7.own.nodes,
            live: c7.own.live.insert(a),
            issued: c7.own.issued,
            network: c7.own.network,
        },
        ray: c7.ray,
        actor: x,
        seized: c7.seized,
    };
    let s8 = ComposedStep::Own { own_step: Step::Recover { node: a } };
    assert(c7.own.nodes.contains(a));
    assert(!c7.own.live.contains(a));
    assert(!recovers_a_seized_node(c7, Step::Recover { node: a }));
    assert(composed_step(c7, c8, s8));
    lemma_composed_reachable_step(c7, c8, s8);
    theorem_composed_step_preserves_inv(c7, c8, s8);

    assert(composed_reachable(c8));
    assert(c8.own.live.contains(a));
    assert(!has_token(c8.ray, a));
    assert(has_token(c8.ray, b));
    assert(c8.own.issued.contains(stale));
    assert(!may_mutate(c8.own.actors[x], a, 41));

    // The run itself, states and labels side by side. Every `composed_step`
    // below was already proved above, one per step; all this does is collect
    // them into the single object the postcondition exports, so that the
    // scenario's evidence is the run rather than a handful of endpoints that
    // some other run could also produce.
    let tr = seq![c0, c1, c2, c3, c4, c5, c6, c7, c8];
    let labels = seq![s1, s2, s3, s4, s5, s6, s7, s8];
    assert(tr.len() == 9);
    assert(labels.len() == 8);
    assert(tr[0] == c0);
    assert(tr[1] == c1);
    assert(tr[2] == c2);
    assert(tr[3] == c3);
    assert(tr[4] == c4);
    assert(tr[5] == c5);
    assert(tr[6] == c6);
    assert(tr[7] == c7);
    assert(tr[8] == c8);
    assert(labels[0] == s1);
    assert(labels[1] == s2);
    assert(labels[2] == s3);
    assert(labels[3] == s4);
    assert(labels[4] == s5);
    assert(labels[5] == s6);
    assert(labels[6] == s7);
    assert(labels[7] == s8);
    assert forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() implies composed_step(tr[i], tr[i + 1], labels[i]) by {
        if i == 0 {
            assert(composed_step(c0, c1, s1));
        } else if i == 1 {
            assert(composed_step(c1, c2, s2));
        } else if i == 2 {
            assert(composed_step(c2, c3, s3));
        } else if i == 3 {
            assert(composed_step(c3, c4, s4));
        } else if i == 4 {
            assert(composed_step(c4, c5, s5));
        } else if i == 5 {
            assert(composed_step(c5, c6, s6));
        } else if i == 6 {
            assert(composed_step(c6, c7, s7));
        } else {
            assert(i == 7);
            assert(composed_step(c7, c8, s8));
        }
    }
    assert(composed_run(tr, labels));
    assert(composed_init(tr[0]));
    assert(composed_labelled_execution(tr, labels));
}

} // verus!
