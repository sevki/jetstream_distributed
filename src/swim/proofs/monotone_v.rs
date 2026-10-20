//! **The merge algebra, lifted through a step and then through a run.**
//!
//! [`crate::swim::proofs::merge`] is arithmetic about two records. This module
//! is the reason that arithmetic is worth having: every transition this
//! protocol has is a call to `merge`, so the one fact
//! [`lemma_merge_key_dominates_local`] proves about `merge` in isolation
//! becomes, by induction over an execution, a statement about the whole
//! run — [`theorem_a_record_key_never_falls_across_a_run`] — with no further
//! case analysis needed at the run level at all.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;
use crate::swim::model::*;
use crate::swim::proofs::merge::*;

verus! {

/// **`merge(a, b)`'s key is at least `a`'s.**
///
/// The one fact this whole module needs from the algebra: whichever of the
/// two branches `merge` takes, the result is no less authoritative than the
/// local record it started from. Taking the `incoming` branch needs exactly
/// the hypothesis `key_geq(incoming, local)` that branch is guarded by;
/// taking the `local` branch needs nothing beyond `key_geq` being reflexive.
pub proof fn lemma_merge_key_dominates_local(a: MemberRecord, b: MemberRecord)
    ensures
        key_geq(merge(a, b), a),
{
    if key_geq(b, a) {
        assert(merge(a, b) == b);
    } else {
        assert(merge(a, b) == a);
        assert(key_geq(a, a));
    }
}

/// **One gossip transition never lowers what either side of it believes.**
///
/// For the member the transition is about, [`lemma_merge_key_dominates_local`]
/// applies directly; for every other member, `tr_gossip` does not touch its
/// entry in `members` at all, so its record is unchanged and `key_geq` is
/// reflexive.
pub proof fn theorem_tr_gossip_never_lowers_a_record(
    pre: Cluster,
    post: Cluster,
    node: Id,
    incoming: MemberRecord,
    n: Id,
)
    requires
        tr_gossip(pre, post, node, incoming),
    ensures
        key_geq(record_of(post, n), record_of(pre, n)),
{
    if n == node {
        assert(post.members.contains_key(n));
        assert(record_of(post, n) == merge(record_of(pre, n), incoming));
        lemma_merge_key_dominates_local(record_of(pre, n), incoming);
    } else {
        assert(post.members.contains_key(n) == pre.members.contains_key(n));
        if pre.members.contains_key(n) {
            assert(post.members[n] == pre.members[n]);
        }
        assert(record_of(post, n) == record_of(pre, n));
        assert(key_geq(record_of(pre, n), record_of(pre, n)));
    }
}

/// The same, for the unlabelled step relation — one `choose` to recover which
/// `SwimStep` fired, then the theorem above, mirroring
/// [`crate::raft::proofs::terms::lemma_raft_next_preserves_terms`]'s own
/// reason for existing as a separate lemma: trigger inference on a `choose`
/// cannot see through the sequence indexing at the call site, so it needs
/// binding into a plain variable first, which is exactly what a call to this
/// lemma does on the caller's behalf.
pub proof fn theorem_swim_next_never_lowers_a_record(pre: Cluster, post: Cluster, n: Id)
    requires
        swim_next(pre, post),
    ensures
        key_geq(record_of(post, n), record_of(pre, n)),
{
    let s = choose|s: SwimStep| swim_step(pre, post, s);
    match s {
        SwimStep::Gossip { node, incoming } => {
            assert(tr_gossip(pre, post, node, incoming));
            theorem_tr_gossip_never_lowers_a_record(pre, post, node, incoming, n);
        },
    }
}

/// **No node's record about any peer ever moves backward, across a whole
/// run.**
///
/// SWIM's convergence argument, reduced to what it actually needs: not that
/// gossip arrives in order, not that it arrives exactly once, only that
/// whatever arrives can only move a view of the world forward relative to
/// where it already was. Everything the probe scheduler, the indirect-ping
/// fallback and the dissemination piggyback will eventually add sits on top
/// of this; none of it can be sound if this is false.
pub proof fn theorem_a_record_key_never_falls_across_a_run(
    tr: Seq<Cluster>,
    a: int,
    b: int,
    n: Id,
)
    requires
        swim_execution(tr),
        0 <= a <= b < tr.len(),
    ensures
        key_geq(record_of(tr[b], n), record_of(tr[a], n)),
    decreases b - a,
{
    if a == b {
        assert(key_geq(record_of(tr[a], n), record_of(tr[a], n)));
    } else {
        theorem_a_record_key_never_falls_across_a_run(tr, a, b - 1, n);

        // Bound into plain variables before using them, for the same reason
        // `lemma_raft_next_preserves_hist` gives: trigger inference on
        // `swim_next` cannot see through `tr[b - 1 + 1]` at the call site.
        assert(swim_next(tr[b - 1], tr[b - 1 + 1]));
        assert(tr[b - 1 + 1] == tr[b]);
        theorem_swim_next_never_lowers_a_record(tr[b - 1], tr[b], n);

        // Two adjacent `key_geq` facts — [a, b - 1] from the induction
        // hypothesis, [b - 1, b] from the step just taken — chain into one
        // over [a, b] by `key_geq`'s own transitivity, not by anything
        // specific to a run.
        lemma_key_geq_transitive(record_of(tr[b], n), record_of(tr[b - 1], n), record_of(tr[a], n));
    }
}

} // verus!
