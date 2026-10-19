//! The executable steps agree with the model.
//!
//! The obligations [`crate::raft::proofs::refinement`] discharges for the Raft
//! steps, in the shape SWIM's single transition leaves room for: when a step
//! computes a record, the model's `tr_gossip` fires to exactly that record.
//!
//! There is no second half. The other refinement suites prove that a step which
//! *refuses* corresponds to a model transition that is *not enabled*; here
//! [`crate::swim::steps::merge_step`] has no refusal — `tr_gossip` is enabled
//! for every incoming record, and merging never fails — so there is no refusal
//! to correspond to. [`crate::swim::steps::refute_step`] does refuse, but only
//! at the top of the `u64` space, which is the implementation's limit and not
//! the model's: the model counts in `nat`, where the refusal has no
//! counterpart. That asymmetry is the same one `Exhausted` is for the term and
//! the epoch.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;
use crate::swim::model::*;
use crate::swim::proofs::merge::*;
use crate::swim::steps::*;

verus! {

/// The record a node publishes to refute an accusation at incarnation
/// `accused`: alive, one incarnation higher.
pub open spec fn refutation(accused: nat) -> MemberRecord {
    MemberRecord { incarnation: accused + 1, status: Status::Alive }
}

/// **`merge_step` is `tr_gossip`.**
///
/// When a node whose record for `n` is `local` merges `incoming` and writes the
/// result back, the model's gossip transition fires — to exactly that
/// cluster. `local.view() == record_of(pre, n)` is the coupling: it says the
/// executable record is the model's record, which is the one thing the service
/// has to keep true by holding its table under a lock.
pub proof fn theorem_merge_step_is_a_gossip_step(
    pre: Cluster,
    post: Cluster,
    n: HostId,
    local: ExecRecord,
    incoming: ExecRecord,
    result: ExecRecord,
)
    requires
        local.view() == record_of(pre, n),
        result.view() == merge(local.view(), incoming.view()),
        post.members == pre.members.insert(n, result.view()),
    ensures
        tr_gossip(pre, post, n, incoming.view()),
        swim_next(pre, post),
{
    assert(tr_gossip(pre, post, n, incoming.view()));
    let s = SwimStep::Gossip { node: n, incoming: incoming.view() };
    assert(swim_step(pre, post, s));
}

/// **A refutation out-ranks the accusation it answers, and everything the
/// accused node could have held when it was made.**
///
/// A higher incarnation wins at any status, so `Alive` at `accused + 1` beats
/// `Suspect` and `Dead` at `accused` alike. And a node's own record never
/// exceeds the incarnation of an accusation it is answering — it answers the
/// highest one it has heard — so the refutation also beats whatever the node
/// itself was holding.
pub proof fn theorem_a_refutation_outranks_what_it_answers(accused: nat, held: MemberRecord)
    requires
        held.incarnation <= accused,
    ensures
        key_geq(refutation(accused), held),
        !key_geq(held, refutation(accused)),
        merge(held, refutation(accused)) == refutation(accused),
{
    assert(refutation(accused).incarnation > held.incarnation);
    assert(key_geq(refutation(accused), held));
    assert(!key_geq(held, refutation(accused)));
}

/// **A refutation is a gossip step, not a new kind of step.**
///
/// The model has one transition. A refutation is it, applied to a record the
/// node made up itself — and that it takes effect (`post` holds the refutation,
/// not something merged away) is [`theorem_a_refutation_outranks_what_it_answers`].
pub proof fn theorem_a_refutation_is_a_gossip_step(
    pre: Cluster,
    post: Cluster,
    n: HostId,
    accused: nat,
)
    requires
        record_of(pre, n).incarnation <= accused,
        post.members == pre.members.insert(n, refutation(accused)),
    ensures
        tr_gossip(pre, post, n, refutation(accused)),
        record_of(post, n) == refutation(accused),
{
    theorem_a_refutation_outranks_what_it_answers(accused, record_of(pre, n));
    assert(post.members.contains_key(n));
    assert(record_of(post, n) == refutation(accused));
}

/// The executable refutation is the model's.
pub proof fn theorem_refute_step_is_the_refutation(accused: u64, result: ExecRecord)
    requires
        result.view() == (MemberRecord { incarnation: accused as nat + 1, status: Status::Alive }),
    ensures
        result.view() == refutation(accused as nat),
{
}

} // verus!
