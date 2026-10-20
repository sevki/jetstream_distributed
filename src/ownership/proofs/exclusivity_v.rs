//! **Claim 1 - Exclusive mutable ownership.**
//!
//! For every actor and every reachable system state, if nodes `A` and `B` are
//! both permitted to mutate that actor then `A == B`.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::ownership::proofs::invariant::*;

verus! {

/// **Exclusive mutable ownership, for any reachable state.**
///
/// There is never a pair of independently valid mutable owners: two nodes that
/// are both permitted to mutate the same actor are the same node, and they are
/// permitted at the same (unique) epoch.
pub proof fn theorem_exclusive_mutable_ownership(
    sys: OwnershipSystem,
    a: Id,
    node_a: Id,
    epoch_a: Epoch,
    node_b: Id,
    epoch_b: Epoch,
)
    requires
        reachable(sys),
        can_mutate(sys, a, node_a, epoch_a),
        can_mutate(sys, a, node_b, epoch_b),
    ensures
        node_a == node_b,
        epoch_a == epoch_b,
{
    lemma_exclusive_owner(sys.actors[a], node_a, epoch_a, node_b, epoch_b);
}

/// The same statement without the reachability hypothesis: exclusivity is a
/// structural property of [`may_mutate`], so it cannot be broken by *any*
/// state, reachable or not. Reachability is what the fencing and token claims
/// need, not this one.
pub proof fn theorem_exclusive_mutable_ownership_structural(
    s: OwnershipState,
    node_a: Id,
    epoch_a: Epoch,
    node_b: Id,
    epoch_b: Epoch,
)
    requires
        may_mutate(s, node_a, epoch_a),
        may_mutate(s, node_b, epoch_b),
    ensures
        node_a == node_b,
        epoch_a == epoch_b,
{
}

/// **Exclusive authority via tokens.**
///
/// The interesting form of exclusivity: two *capability tokens* that both
/// currently confer authority over the same actor are the same token. A stale
/// physical token held by a partitioned node cannot become a second authority.
pub proof fn theorem_authorized_token_unique(sys: OwnershipSystem, t1: Token, t2: Token)
    requires
        reachable(sys),
        token_authorized(sys, t1),
        token_authorized(sys, t2),
        t1.actor == t2.actor,
    ensures
        t1 == t2,
{
    theorem_reachable_inv(sys);
    lemma_exclusive_owner(sys.actors[t1.actor], t1.holder, t1.epoch, t2.holder, t2.epoch);
}

/// A node that holds no authority over an actor cannot mutate it, regardless of
/// what tokens it physically holds.
pub proof fn theorem_holding_a_token_is_not_authority(sys: OwnershipSystem, t: Token)
    requires
        reachable(sys),
        token_held(sys, t),
        sys.actors.contains_key(t.actor),
        !is_owned_by(sys.actors[t.actor], t.holder),
    ensures
        !token_authorized(sys, t),
        !can_mutate(sys, t.actor, t.holder, t.epoch),
{
}

} // verus!
