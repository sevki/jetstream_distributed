//! **Claim 6 - Token uniqueness.**
//!
//! At most one valid ownership capability exists per `(ActorId, Epoch)`. Stale
//! physical tokens may exist after crashes or partitions, but they confer no
//! authority.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;
use crate::proofs::invariant::*;

verus! {

/// **Token uniqueness (authority form).** At most one token confers authority
/// for a given `(actor, epoch)`.
pub proof fn theorem_valid_token_unique_per_actor_epoch(sys: System, t1: Token, t2: Token)
    requires
        token_authorized(sys, t1),
        token_authorized(sys, t2),
        t1.actor == t2.actor,
        t1.epoch == t2.epoch,
    ensures
        t1 == t2,
{
    lemma_exclusive_owner(sys.actors[t1.actor], t1.holder, t1.epoch, t2.holder, t2.epoch);
}

/// **Token uniqueness (physical form).** In a reachable state, at most one
/// token was ever *issued* for a given `(actor, epoch)` - the protocol does not
/// even mint duplicates, let alone honour them.
pub proof fn theorem_issued_token_unique_per_actor_epoch(sys: System, t1: Token, t2: Token)
    requires
        reachable(sys),
        token_held(sys, t1),
        token_held(sys, t2),
        t1.actor == t2.actor,
        t1.epoch == t2.epoch,
    ensures
        t1 == t2,
{
    theorem_reachable_inv(sys);
    assert(inv_tokens_unique(sys));
}

/// **Stale tokens carry no authority.** A token from a superseded epoch is
/// still physically held - it survived the crash, the partition and the
/// recovery - but it cannot authorise a mutation.
pub proof fn theorem_stale_token_has_no_authority(sys: System, t: Token)
    requires
        sys.actors.contains_key(t.actor),
        is_stale(sys.actors[t.actor], t.epoch),
    ensures
        !token_authorized(sys, t),
        !can_mutate(sys, t.actor, t.holder, t.epoch),
{
    lemma_stale_epoch_cannot_mutate(sys.actors[t.actor], t.holder, t.epoch);
}

/// Tokens cannot be minted for the future: in a reachable state no issued token
/// has an epoch beyond the actor's current epoch.
pub proof fn theorem_no_future_tokens(sys: System, t: Token)
    requires
        reachable(sys),
        token_held(sys, t),
    ensures
        sys.actors.contains_key(t.actor),
        t.epoch <= current_epoch(sys.actors[t.actor]),
{
    theorem_reachable_inv(sys);
    assert(token_inv(sys, t));
}

/// A token at the actor's current epoch can only be held by the actor's
/// current owner: authority cannot be forged for a third party.
pub proof fn theorem_current_epoch_token_is_owner(sys: System, t: Token)
    requires
        reachable(sys),
        token_held(sys, t),
        sys.actors.contains_key(t.actor),
        t.epoch == current_epoch(sys.actors[t.actor]),
    ensures
        is_owned_by(sys.actors[t.actor], t.holder) || !is_owned(sys.actors[t.actor]),
{
    theorem_reachable_inv(sys);
    assert(token_inv(sys, t));
}

} // verus!
