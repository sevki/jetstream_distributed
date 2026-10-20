//! The composed machine's coupling guards, executable and verified.
//!
//! [`crate::ownership::steps`] decides what the registry does with the actor;
//! [`crate::raymond::steps`] decides what a node does with its routing entries.
//! Neither knows about the other, and that is the point of the composed machine
//! ([`crate::composed::model`]): the coupling is a **guard**, and it is the only
//! thing the composition adds. This file is those guards, as small functions
//! whose postconditions are stated in terms of the model, and
//! [`crate::composed::proofs::refinement`] ties them to `cs_pass_token`,
//! `cs_seize_token`, `cs_acquire_under_token` and `cs_reconcile`.
//!
//! # What each guard reads
//!
//! Booleans the caller has already established — whether the actor is
//! `Unowned` — and the one authoritative fact the routing layer owns, which node
//! holds the privilege. A step here reads no record; it only combines the
//! answers the two layers' own steps give.
//!
//! # Liveness, and what a service can and cannot know
//!
//! The model guards `cs_pass_token` and `cs_ray` on `own.live`, which is
//! **ground truth**: whether a node has crashed is not something any process can
//! evaluate, and the model says so itself — liveness may guard the nodes a step
//! makes *act*, and may not guard the ones it does not.
//!
//! So the guards below do not read it, and the service has no `Crash` or
//! `Recover`. That is a statement about **which executions the service
//! refines**: those of the composed machine in which no node ever crashes, where
//! every node is live and every liveness guard is vacuously true. The refinement
//! theorems say so out loud — `live.contains(..)` is a hypothesis of each, not
//! something silently dropped. The ownership `Registry` makes the same cut for
//! the same reason.
//!
//! What this does **not** lose is the case the composed machine exists for.
//! [`seize_fires`] has no liveness guard on `from` in the model either, so
//! taking the privilege from a holder that is merely unreachable — the
//! wrongly-suspected node a real coordinator cannot tell from a dead one — is in
//! the fragment the service covers.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

verus! {

/// Why a step did not fire. The coupling's reasons only — the layers' own
/// refusals are [`crate::ownership::steps::Refusal`] and
/// [`crate::raymond::steps::RayRefusal`].
#[derive(Clone, Copy)]
pub enum CoupledRefusal {
    /// The actor is not `Unowned`, so the privilege may not move: the release
    /// has to have *completed* first.
    ActorNotReleased,
    /// Authority over the actor may only be taken by the node holding the
    /// privilege, and this node does not.
    NotPrivileged,
    /// Nobody else holds the privilege to seize: the named holder is not the
    /// holder, or the target already is.
    NothingToSeize,
    /// The named node is not a node.
    NotANode,
    /// This node is not carrying an unacknowledged seizure.
    NotSeized,
    /// This node's belief is not stale: it does not believe it holds the
    /// privilege, or it really does.
    NotStale,
}

/// `cs_pass_token`'s guard, beyond the routing layer's own: the actor has been
/// released.
///
/// `is_unowned`, not `!is_owned` — `Transferring` satisfies the weaker form, and
/// the outgoing owner has not acknowledged the revoke yet. See the model.
pub open spec fn pass_token_fires(actor_unowned: bool) -> bool {
    actor_unowned
}

/// `cs_seize_token`'s guard, with `ray_seize`'s folded in.
///
/// Nothing is said about `from`'s liveness, deliberately: it is a node the step
/// does *not* make act, so a guard on it would be an oracle. `from` is the node
/// that holds the privilege, which is the one fact the routing layer owns.
pub open spec fn seize_fires(
    actor_unowned: bool,
    from: Id,
    privilege: Id,
    to: Id,
    to_is_node: bool,
) -> bool {
    &&& actor_unowned
    &&& privilege == from
    &&& to_is_node
    &&& to != from
}

/// `cs_acquire_under_token`'s guard, beyond the ownership layer's own: the
/// node holds the privilege.
pub open spec fn acquire_under_token_fires(privilege: Id, node: Id) -> bool {
    privilege == node
}

/// `cs_reconcile`'s guard: the node owes a reconciliation and its belief really
/// is stale (`is_stale_holder`).
pub open spec fn reconcile_fires(seized: bool, believes_holds: bool, has_token: bool) -> bool {
    &&& seized
    &&& believes_holds
    &&& !has_token
}

/// May the privilege move? Only once the actor has been released.
pub fn pass_token_step(actor_unowned: bool) -> (r: Result<(), CoupledRefusal>)
    ensures
        match r {
            Ok(_) => pass_token_fires(actor_unowned),
            Err(_) => !pass_token_fires(actor_unowned),
        },
{
    if actor_unowned {
        Ok(())
    } else {
        Err(CoupledRefusal::ActorNotReleased)
    }
}

/// May the privilege be seized from `from` and re-established at `to`?
pub fn seize_step(
    actor_unowned: bool,
    from: Id,
    privilege: Id,
    to: Id,
    to_is_node: bool,
) -> (r: Result<(), CoupledRefusal>)
    ensures
        match r {
            Ok(_) => seize_fires(actor_unowned, from, privilege, to, to_is_node),
            Err(_) => !seize_fires(
                actor_unowned,
                from,
                privilege,
                to,
                to_is_node,
            ),
        },
{
    if !actor_unowned {
        Err(CoupledRefusal::ActorNotReleased)
    } else if !to_is_node {
        Err(CoupledRefusal::NotANode)
    } else if privilege != from || to == from {
        Err(CoupledRefusal::NothingToSeize)
    } else {
        Ok(())
    }
}

/// May `node` take authority over the actor?
pub fn acquire_under_token_step(privilege: Id, node: Id) -> (r: Result<(), CoupledRefusal>)
    ensures
        match r {
            Ok(_) => acquire_under_token_fires(privilege, node),
            Err(_) => !acquire_under_token_fires(privilege, node),
        },
{
    if privilege == node {
        Ok(())
    } else {
        Err(CoupledRefusal::NotPrivileged)
    }
}

/// May `node` reconcile?
pub fn reconcile_step(seized: bool, believes_holds: bool, has_token: bool) -> (r: Result<
    (),
    CoupledRefusal,
>)
    ensures
        match r {
            Ok(_) => reconcile_fires(seized, believes_holds, has_token),
            Err(_) => !reconcile_fires(seized, believes_holds, has_token),
        },
{
    if !seized {
        Err(CoupledRefusal::NotSeized)
    } else if !believes_holds || has_token {
        Err(CoupledRefusal::NotStale)
    } else {
        Ok(())
    }
}

} // verus!
