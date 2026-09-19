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

use vstd::prelude::*;

use crate::composed::*;
use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::composed::*;
use crate::proofs::raymond::*;
use crate::raymond::*;

verus! {

/// A full ownership handover coordinated across both layers.
///
/// This is the non-vacuity witness for every `composed_reachable` theorem: it
/// exhibits a reachable composed state in which somebody actually owns the actor
/// and actually holds the token.
/// Phase one of the handover: from `composed_init` to the point where the actor
/// has been released at epoch 42 and `A` still holds the token.
///
/// Returning the state with an *abstract* characterisation rather than letting
/// the caller keep the literal is what keeps the proof tractable: each phase
/// reasons about a handful of `insert`s over an opaque base instead of a dozen
/// nested `Map`/`Set` literals, which is what exhausted the solver before.
pub proof fn handover_phase_release(x: ActorId, a: NodeId, b: NodeId) -> (c: Composed)
    requires
        a != b,
    ensures
        composed_reachable(c),
        composed_inv(c),
        c.actor == x,
        c.own.actors[x] == (OwnershipState::Unowned { epoch: 42, intended_owner: b }),
        c.own.live.contains(b),
        c.own.network.contains(Message::Grant { actor: x, to: b, epoch: 42 }),
        c.own.issued.contains(Token { actor: x, epoch: 41, holder: a }),
        c.ray.nodes.contains(a),
        c.ray.nodes.contains(b),
        c.ray.holder[b] == a,
        has_token(c.ray, a),
        c.ray.queue[a].len() == 0,
        c.ray.queue[b].len() == 0,
        !c.ray.asked[b],
        !c.ray.using[a],
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
        nodes: nodes,
        holder: Map::<NodeId, NodeId>::empty().insert(a, a).insert(b, a),
        queue: Map::<NodeId, Seq<NodeId>>::empty().insert(a, empty_q).insert(b, empty_q),
        asked: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        using: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        requests: Set::<(NodeId, NodeId)>::empty(),
    };
    assert(ray0.holder[a] == a);
    assert(ray0.holder[b] == a);
    assert(ray_init(ray0, a));

    let c0 = Composed { own: own0, ray: ray0, actor: x };
    assert(own0.actors.contains_key(x));
    assert(init(own0));
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
    };
    let s5 = ComposedStep::Own { own_step: Step::CompleteRelease { actor: x } };
    assert(c4.own.network.contains(released));
    assert(step(c4.own, c5.own, Step::CompleteRelease { actor: x }));
    assert(composed_step(c4, c5, s5));
    lemma_composed_reachable_step(c4, c5, s5);
    theorem_composed_step_preserves_inv(c4, c5, s5);
    assert(is_unowned(c5.own.actors[x]));
    assert(has_token(c5.ray, a));
    c5
}

/// Phase two: `B` requests the token, it moves `A -> B`, and `B` takes
/// ownership at epoch 42.
///
/// Takes the mid state abstractly, so the solver never sees the literals built
/// in phase one.
pub proof fn handover_phase_acquire(c: Composed, x: ActorId, a: NodeId, b: NodeId) -> (r: Composed)
    requires
        a != b,
        composed_reachable(c),
        composed_inv(c),
        c.actor == x,
        c.own.actors[x] == (OwnershipState::Unowned { epoch: 42, intended_owner: b }),
        c.own.live.contains(b),
        c.own.network.contains(Message::Grant { actor: x, to: b, epoch: 42 }),
        c.own.issued.contains(Token { actor: x, epoch: 41, holder: a }),
        c.ray.nodes.contains(a),
        c.ray.nodes.contains(b),
        c.ray.holder[b] == a,
        has_token(c.ray, a),
        c.ray.queue[a].len() == 0,
        c.ray.queue[b].len() == 0,
        !c.ray.asked[b],
        !c.ray.using[a],
    ensures
        composed_reachable(r),
        composed_inv(r),
        r.actor == x,
        r.own.actors[x] == (OwnershipState::Owned { owner: b, epoch: 42 }),
        has_token(r.ray, b),
        r.own.issued.contains(Token { actor: x, epoch: 41, holder: a }),
{
    // 6. B asks for the token
    let c6 = Composed {
        own: c.own,
        ray: Raymond {
            nodes: c.ray.nodes,
            holder: c.ray.holder,
            queue: c.ray.queue.insert(b, c.ray.queue[b].push(b)),
            asked: c.ray.asked,
            using: c.ray.using,
            requests: c.ray.requests,
        },
        actor: x,
    };
    let s6 = ComposedStep::Ray { ray_step: RayStep::RequestCs { node: b } };
    assert(composed_step(c, c6, s6));
    lemma_composed_reachable_step(c, c6, s6);
    theorem_composed_step_preserves_inv(c, c6, s6);

    // 7. B routes the request to its holder, A
    let c7 = Composed {
        own: c6.own,
        ray: Raymond {
            nodes: c6.ray.nodes,
            holder: c6.ray.holder,
            queue: c6.ray.queue,
            asked: c6.ray.asked.insert(b, true),
            using: c6.ray.using,
            requests: c6.ray.requests.insert((b, c6.ray.holder[b])),
        },
        actor: x,
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
            nodes: c7.ray.nodes,
            holder: c7.ray.holder,
            queue: c7.ray.queue.insert(a, c7.ray.queue[a].push(b)),
            asked: c7.ray.asked,
            using: c7.ray.using,
            requests: c7.ray.requests,
        },
        actor: x,
    };
    let s8 = ComposedStep::Ray { ray_step: RayStep::ReceiveRequest { at: a, from: b } };
    assert(c7.ray.requests.contains((b, a)));
    assert(composed_step(c7, c8, s8));
    lemma_composed_reachable_step(c7, c8, s8);
    theorem_composed_step_preserves_inv(c7, c8, s8);

    // 9. the token moves A -> B. Legal only because X is Unowned
    let c9 = Composed {
        own: c8.own,
        ray: Raymond {
            nodes: c8.ray.nodes,
            holder: c8.ray.holder.insert(a, b).insert(b, b),
            queue: c8.ray.queue.insert(a, c8.ray.queue[a].drop_first()),
            asked: c8.ray.asked.insert(a, false),
            using: c8.ray.using,
            requests: c8.ray.requests,
        },
        actor: x,
    };
    let s9 = ComposedStep::PassToken { node: a, head: b };
    assert(has_token(c8.ray, a));
    assert(!c8.ray.using[a]);
    assert(c8.ray.queue[a].len() == 1);
    assert(c8.ray.queue[a][0] == b);
    assert(is_unowned(c8.own.actors[x]));
    assert(composed_step(c8, c9, s9));
    lemma_composed_reachable_step(c8, c9, s9);
    theorem_composed_step_preserves_inv(c8, c9, s9);
    lemma_composed_pass_token_preserves_inv(c8, c9, a, b);
    assert(has_token(c9.ray, b));

    // 10. B takes ownership at epoch 42, holding the token
    let c10 = Composed {
        own: System {
            actors: c9.own.actors.insert(x, OwnershipState::Owned { owner: b, epoch: 42 }),
            nodes: c9.own.nodes,
            live: c9.own.live,
            issued: c9.own.issued.insert(Token { actor: x, epoch: 42, holder: b }),
            network: c9.own.network,
        },
        ray: c9.ray,
        actor: x,
    };
    let s10 = ComposedStep::AcquireUnderToken { node: b };
    assert(c9.own.live.contains(b));
    assert(c9.own.actors[x] == (OwnershipState::Unowned { epoch: 42, intended_owner: b }));
    assert(c9.own.network.contains(Message::Grant { actor: x, to: b, epoch: 42 }));
    assert(has_token(c9.ray, b));
    assert(tr_acquire(c9.own, c10.own, x, b));
    assert(composed_step(c9, c10, s10));
    lemma_composed_reachable_step(c9, c10, s10);
    theorem_composed_step_preserves_inv(c9, c10, s10);
    c10
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
        exists|c: Composed|
            {
                &&& #[trigger] composed_reachable(c)
                &&& may_mutate(c.own.actors[c.actor], b, 42)
                &&& has_token(c.ray, b)
                &&& c.own.issued.contains(Token { actor: x, epoch: 41, holder: a })
                &&& !may_mutate(c.own.actors[c.actor], a, 41)
            },
{
    let mid = handover_phase_release(x, a, b);
    let fin = handover_phase_acquire(mid, x, a, b);
    assert(composed_reachable(fin));
    assert(may_mutate(fin.own.actors[fin.actor], b, 42));
    assert(has_token(fin.ray, b));
    assert(fin.own.issued.contains(Token { actor: x, epoch: 41, holder: a }));
    assert(!may_mutate(fin.own.actors[fin.actor], a, 41));
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
        exists|c: Composed| #[trigger] composed_reachable(c) && c.ray.using[a],
        exists|c: Composed| #[trigger] composed_reachable(c) && !c.ray.using[a],
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
        nodes: nodes,
        holder: Map::<NodeId, NodeId>::empty().insert(a, a).insert(b, a),
        queue: Map::<NodeId, Seq<NodeId>>::empty().insert(a, empty_q).insert(b, empty_q),
        asked: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        using: Map::<NodeId, bool>::empty().insert(a, false).insert(b, false),
        requests: Set::<(NodeId, NodeId)>::empty(),
    };
    assert(ray0.holder[a] == a);
    assert(ray0.holder[b] == a);
    assert(ray_init(ray0, a));

    let c0 = Composed { own: own0, ray: ray0, actor: x };
    assert(own0.actors.contains_key(x));
    assert(init(own0));
    assert(composed_init(c0));
    lemma_composed_reachable_init(c0);
    lemma_composed_init_inv(c0);
    assert(has_token(c0.ray, a));

    // 1. A queues itself.
    let c1 = Composed {
        own: c0.own,
        ray: Raymond {
            nodes: c0.ray.nodes,
            holder: c0.ray.holder,
            queue: c0.ray.queue.insert(a, c0.ray.queue[a].push(a)),
            asked: c0.ray.asked,
            using: c0.ray.using,
            requests: c0.ray.requests,
        },
        actor: x,
    };
    let s1 = ComposedStep::Ray { ray_step: RayStep::RequestCs { node: a } };
    assert(composed_step(c0, c1, s1));
    lemma_composed_reachable_step(c0, c1, s1);
    theorem_composed_step_preserves_inv(c0, c1, s1);

    // 2. A is at the head of its own queue and holds the token, so it enters.
    let c2 = Composed {
        own: c1.own,
        ray: Raymond {
            nodes: c1.ray.nodes,
            holder: c1.ray.holder,
            queue: c1.ray.queue.insert(a, c1.ray.queue[a].drop_first()),
            asked: c1.ray.asked,
            using: c1.ray.using.insert(a, true),
            requests: c1.ray.requests,
        },
        actor: x,
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
            nodes: c2.ray.nodes,
            holder: c2.ray.holder,
            queue: c2.ray.queue,
            asked: c2.ray.asked,
            using: c2.ray.using.insert(a, false),
            requests: c2.ray.requests,
        },
        actor: x,
    };
    let s3 = ComposedStep::Ray { ray_step: RayStep::ExitCs { node: a } };
    assert(c2.ray.using[a]);
    assert(composed_step(c2, c3, s3));
    lemma_composed_reachable_step(c2, c3, s3);
    theorem_composed_step_preserves_inv(c2, c3, s3);

    assert(composed_reachable(c3));
    assert(!c3.ray.using[a]);
}

} // verus!
