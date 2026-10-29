//! **What `couples` buys: routing cannot manufacture authority.**
//!
//! `couples(r, s)` says every node that may mutate in the ownership state `s` holds
//! the privilege in the routing state `r`. It is about both layers, so it is defined
//! with the composed machine ([`crate::composed::model::couples`]); these are the
//! theorems that use it on its own, before the machine turns it into an invariant
//! ([`super::coupling`]).
//!
//! They were stated in `raymond::proofs::routing_layer`, which made the Raymond
//! protocol import the ownership protocol for the sake of five theorems about
//! neither alone. They are here, unchanged, and Raymond imports nothing of ownership.
//!
//! * token transfer preserves ownership safety;
//! * routing cannot manufacture ownership;
//! * a stale holder confers no authority;
//! * taking ownership while holding the privilege establishes the coupling;
//! * under the coupling, two nodes that may mutate are the same node.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::composed::model::*;
use crate::id::Id;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::raymond::model::*;
use crate::raymond::proofs::routing_layer::*;

verus! {

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
