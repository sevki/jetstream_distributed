//! The composed steps' records are the composed model.
//!
//! [`crate::composed::exec`] takes the two layers' records and the set of nodes
//! that owe a reconciliation and performs the composed machine's steps on them.
//! These theorems say each function's contract is the model's `cs_*` step:
//! given a composed state the records stand for, a function that fires leaves
//! records that stand for the state the model's step leads to, and one that
//! refuses was a step the model could not take.
//!
//! # The relation
//!
//! [`stands_for_composed`]: the ownership record stands for `c.own` for `c.actor`
//! ([`crate::ownership::proofs::registry::stands_for`] — grants included), the
//! routing table's view *is* `c.ray`, and the debts are `c.seized`.
//!
//! # What is not here
//!
//! The model's steps also require that the nodes involved are live
//! (`own.live.contains(..)`), a fact about connections the records do not hold;
//! the theorems take it as a hypothesis. The service's identity lookup speaks only
//! for the *caller*; the recipient of a passed privilege (the head of a queue) and
//! the target of a seizure are not callers, so for them nothing in the service
//! establishes it.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;

use crate::composed::exec::*;
use crate::composed::model::*;
use crate::composed::proofs::refinement::*;
use crate::composed::steps::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::proofs::refinement::*;
use crate::ownership::proofs::registry::*;
use crate::ownership::registry::*;
use crate::ownership::spec::*;
use crate::ownership::steps::*;
use crate::raymond::exec::*;
use crate::raymond::model::*;

verus! {

/// The records stand for the composed state.
pub open spec fn stands_for_composed(
    own: RegistryCore,
    ray: RayTable,
    seized: NodeSet,
    c: Composed,
) -> bool {
    &&& stands_for(own, c.own, c.actor)
    &&& ray@ == c.ray
    &&& seized@ == c.seized
}

/// **`pass_token` is `cs_pass_token`.**
pub proof fn theorem_pass_token_is_cs_pass_token(
    own: RegistryCore,
    ray: RayTable,
    ray2: RayTable,
    seized: NodeSet,
    seized2: NodeSet,
    c: Composed,
    me: HostId,
    head: HostId,
)
    requires
        stands_for_composed(own, ray, seized, c),
        c.own.live.contains(me),
        c.own.live.contains(head),
        is_unowned(own.state.view()),
        ray_assign_privilege(ray@, ray2@, me, head),
        seized2@ == seized@.remove(head),
    ensures
        cs_pass_token(
            c,
            Composed { own: c.own, ray: ray2@, actor: c.actor, seized: seized2@ },
            me,
            head,
        ),
{
}

/// **A refused `pass_token` is a step the model could not take**, for any head.
pub proof fn theorem_refused_pass_token_is_disabled(
    own: RegistryCore,
    ray: RayTable,
    seized: NodeSet,
    c: Composed,
    post: Composed,
    me: HostId,
    head: HostId,
)
    requires
        stands_for_composed(own, ray, seized, c),
        !is_unowned(own.state.view()) || forall|p: Raymond, h: HostId|
            !ray_assign_privilege(ray@, p, me, h),
    ensures
        !cs_pass_token(c, post, me, head),
{
}

/// **`seize_token` is `cs_seize_token`.** Only `to` acts; the old holder owes a
/// reconciliation and `to` no longer does.
pub proof fn theorem_seize_token_is_cs_seize_token(
    own: RegistryCore,
    ray: RayTable,
    ray2: RayTable,
    seized: NodeSet,
    seized2: NodeSet,
    c: Composed,
    from: HostId,
    to: HostId,
)
    requires
        stands_for_composed(own, ray, seized, c),
        c.own.live.contains(to),
        is_unowned(own.state.view()),
        ray_seize(ray@, ray2@, from, to),
        seized2@ == seized@.insert(from).remove(to),
    ensures
        cs_seize_token(
            c,
            Composed { own: c.own, ray: ray2@, actor: c.actor, seized: seized2@ },
            from,
            to,
        ),
{
}

/// **A refused `seize_token` is a step the model could not take.**
pub proof fn theorem_refused_seize_token_is_disabled(
    own: RegistryCore,
    ray: RayTable,
    seized: NodeSet,
    c: Composed,
    post: Composed,
    to: HostId,
)
    requires
        stands_for_composed(own, ray, seized, c),
        !is_unowned(own.state.view()) || forall|p: Raymond|
            !ray_seize(ray@, p, ray.privilege, to),
    ensures
        !cs_seize_token(c, post, ray.privilege, to),
{
}

/// **`acquire_under_token` is `cs_acquire_under_token`**: the ownership layer's
/// acquire, for the node holding the privilege, routing untouched.
pub proof fn theorem_acquire_under_token_is_cs_acquire_under_token(
    own: RegistryCore,
    own2: RegistryCore,
    ray: RayTable,
    seized: NodeSet,
    c: Composed,
    node: HostId,
    epoch: u64,
)
    requires
        stands_for_composed(own, ray, seized, c),
        c.own.live.contains(node),
        has_token(ray@, node),
        acquire_fires(own.state.view(), node, epoch as nat, own.has_grant(node, epoch as nat)),
        own2.state.view() == acquire_next(own.state.view(), node),
        grants_same(own, own2),
    ensures
        cs_acquire_under_token(
            c,
            Composed {
                own: acquire_post(c.own, c.actor, node),
                ray: c.ray,
                actor: c.actor,
                seized: c.seized,
            },
            node,
        ),
        stands_for(own2, acquire_post(c.own, c.actor, node), c.actor),
{
    theorem_acquire_is_tr_acquire(own, own2, c.own, c.actor, node, epoch);
}

/// **A node without the privilege cannot acquire**, in the model either.
pub proof fn theorem_acquire_without_the_privilege_is_disabled(
    own: RegistryCore,
    ray: RayTable,
    seized: NodeSet,
    c: Composed,
    post: Composed,
    node: HostId,
)
    requires
        stands_for_composed(own, ray, seized, c),
        !has_token(ray@, node),
    ensures
        !cs_acquire_under_token(c, post, node),
{
}

/// **`reconcile` is `cs_reconcile`.**
pub proof fn theorem_reconcile_is_cs_reconcile(
    own: RegistryCore,
    ray: RayTable,
    ray2: RayTable,
    seized: NodeSet,
    seized2: NodeSet,
    c: Composed,
    node: HostId,
)
    requires
        stands_for_composed(own, ray, seized, c),
        seized@.contains(node),
        ray_reconcile(ray@, ray2@, node),
        seized2@ == seized@.remove(node),
    ensures
        cs_reconcile(
            c,
            Composed { own: c.own, ray: ray2@, actor: c.actor, seized: seized2@ },
            node,
        ),
{
}

/// **A refused `reconcile` is a step the model could not take.**
pub proof fn theorem_refused_reconcile_is_disabled(
    own: RegistryCore,
    ray: RayTable,
    seized: NodeSet,
    c: Composed,
    post: Composed,
    node: HostId,
)
    requires
        stands_for_composed(own, ray, seized, c),
        !seized@.contains(node) || forall|p: Raymond| !ray_reconcile(ray@, p, node),
    ensures
        !cs_reconcile(c, post, node),
{
}

} // verus!
