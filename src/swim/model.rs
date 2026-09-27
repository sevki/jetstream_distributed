//! SWIM's anti-entropy core: one record per member, and the rule for merging
//! two of them.
//!
//! Like [`crate::raft::model`], this defines *only* the state and the
//! transition relation. It does not import the specification layer, so a
//! specification cannot be quietly tuned until it comes out true.
//!
//! # The record, and why it is exactly two fields
//!
//! memberlist's `state.go` remembers, for every peer, an **incarnation
//! number** and a **status** — `Alive`, `Suspect` or `Dead` — and nothing
//! else is needed to decide whether an incoming gossip message should
//! overwrite what a node already believes. The incarnation is a peer's own
//! epoch: only *that peer* increments it, by refuting a suspicion of itself,
//! and every other node's information about it is stamped with the
//! incarnation that was current when the information was produced. The
//! status is where in `Alive -> Suspect -> Dead` the peer sits as far as the
//! sender of the message knows.
//!
//! # `key_geq`: the total order the whole module rests on
//!
//! Two records compare first by incarnation — a higher incarnation is
//! *always* more authoritative, because it can only have been produced by
//! the peer itself refuting something — and, at equal incarnations, by how
//! dead the status says the peer is. That second clause is what lets a
//! `Suspect` message overwrite an `Alive` record at the same incarnation
//! (the usual case: a probe just timed out) while never letting a `Suspect`
//! message undo a `Dead` one at that same incarnation (the peer has already
//! been declared gone at this epoch; a later, weaker report of it changes
//! nothing until the peer itself speaks again with a higher incarnation).
//!
//! `status_rank` is what turns "how dead" into a number `key_geq` can compare,
//! and it has to be **injective** — no two statuses may share a rank — for
//! the algebra in [`crate::swim::proofs`] to hold at all:
//! [`lemma_rank_is_injective`] is where that fact is spent, and every
//! commutativity or associativity proof downstream needs it, because without
//! it two records could compare equal by key while disagreeing on status,
//! and "merge picks the record with the larger key" would stop meaning
//! "merge picks *a* record" at all.
#![allow(unused_imports)]

use vstd::prelude::*;

verus! {

pub type NodeId = nat;

/// Where SWIM's gossip currently says a node stands, ordered by how dead it
/// is. The order — not the declaration order, which Rust does not expose to
/// spec code anyway — is fixed by [`status_rank`].
///
/// memberlist also has a `StateLeft`, for a node that announced its own
/// departure rather than being suspected or declared dead by others, and
/// gives it different precedence and join-handling rules from `StateDead`.
/// That distinction is deliberately not modeled here: this increment covers
/// only failure detection — a peer that stops responding — not voluntary
/// membership changes. A `Left` variant, and the precedence rule for it,
/// belongs with whatever future increment models graceful leave and rejoin.
pub enum Status {
    Alive,
    Suspect,
    Dead,
}

/// The rank [`Status`] compares by: `Alive` < `Suspect` < `Dead`.
///
/// Injective by construction — three variants, three distinct naturals — and
/// [`lemma_rank_is_injective`] is that fact made available to a proof rather
/// than left for one to rediscover by matching on both arguments itself.
pub open spec fn status_rank(s: Status) -> nat {
    match s {
        Status::Alive => 0,
        Status::Suspect => 1,
        Status::Dead => 2,
    }
}

/// **`status_rank` is injective.**
///
/// The fact that makes a record recoverable from its key. Two statuses that
/// rank the same are the same status — there is no pair of distinct
/// variants sharing a rank — which is what lets
/// [`crate::swim::proofs::merge::theorem_merge_is_commutative`] conclude two
/// same-key records are literally the same record rather than merely
/// interchangeable for the theorem's purposes.
pub proof fn lemma_rank_is_injective(a: Status, b: Status)
    requires
        status_rank(a) == status_rank(b),
    ensures
        a == b,
{
    match a {
        Status::Alive => {
            match b {
                Status::Alive => {},
                Status::Suspect => { assert(false); },
                Status::Dead => { assert(false); },
            }
        },
        Status::Suspect => {
            match b {
                Status::Alive => { assert(false); },
                Status::Suspect => {},
                Status::Dead => { assert(false); },
            }
        },
        Status::Dead => {
            match b {
                Status::Alive => { assert(false); },
                Status::Suspect => { assert(false); },
                Status::Dead => {},
            }
        },
    }
}

/// **Ghost, in the state-machine sense a real node keeps in memory, not in
/// the history-variable sense the other three protocols in this repository
/// use the word.** Every node holds one of these per peer, in real
/// memberlist as much as here.
pub struct MemberRecord {
    pub incarnation: nat,
    pub status: Status,
}

/// A freshly-joined, never-yet-gossiped-about peer: incarnation zero, and
/// presumed alive because nothing has said otherwise.
pub open spec fn fresh_record() -> MemberRecord {
    MemberRecord { incarnation: 0, status: Status::Alive }
}

/// **`a`'s key is at least `b`'s** — a higher incarnation wins outright, and
/// at equal incarnations the more-dead status wins.
///
/// The whole of SWIM's anti-entropy rule is this comparison and
/// [`merge`]'s one-line use of it. Read `key_geq(a, b)` as "the record `a`
/// is at least as authoritative as `b`", not as an arithmetic fact about two
/// numbers — the arithmetic is the *proof* of that authority, not the point
/// of it.
pub open spec fn key_geq(a: MemberRecord, b: MemberRecord) -> bool {
    ||| a.incarnation > b.incarnation
    ||| (a.incarnation == b.incarnation && status_rank(a.status) >= status_rank(b.status))
}

/// **The merge rule.** Keep whichever of `local` and `incoming` has the
/// larger key, `incoming` breaking a tie.
///
/// This is `state.go`'s `aliveNode`, `suspectNode` and `deadNode` in one
/// function: each of those three real transitions is a call to this one with
/// a different `incoming` record, and none of them needs its own merge logic
/// because the comparison never looks at *why* `incoming` arrived, only at
/// what it claims.
///
/// The tie-break is not a design choice with an alternative worth naming: by
/// [`lemma_rank_is_injective`], two records with equal incarnation and equal
/// rank have equal status, and a record is exactly its incarnation and its
/// status — so a tie is never a tie between two *different* records, and
/// which side `merge` picks on one is unobservable. See
/// [`crate::swim::proofs::merge::theorem_merge_is_commutative`] for where
/// that fact is spent.
pub open spec fn merge(local: MemberRecord, incoming: MemberRecord) -> MemberRecord {
    if key_geq(incoming, local) {
        incoming
    } else {
        local
    }
}

/// The whole cluster, as one node sees it: a partial map from peer to record.
/// Fixed membership is not assumed here the way it is in
/// [`crate::raft::model::Cluster`] — a node absent from `members` is exactly
/// a node this view has never heard of, which [`record_of`] treats as
/// [`fresh_record`] rather than as an error.
pub struct Cluster {
    pub members: Map<NodeId, MemberRecord>,
}

/// What this view believes about `n`: its record if it has one, `fresh_record`
/// otherwise. Every transition and every proof below goes through this rather
/// than through `members` directly, so "no entry yet" and "entry is the
/// initial one" are the same case everywhere rather than a distinction some
/// call site forgets to make.
pub open spec fn record_of(c: Cluster, n: NodeId) -> MemberRecord {
    if c.members.contains_key(n) {
        c.members[n]
    } else {
        fresh_record()
    }
}

/// **A gossip message, a probe timeout and a self-refutation are one
/// transition.** All three deliver a candidate `MemberRecord` about `n` and
/// ask the local view to adopt it if it is at least as authoritative as what
/// is already there — which is exactly [`merge`]. A probe timeout's
/// candidate is `{ incarnation: record_of(pre, n).incarnation, status:
/// Suspect }`; a self-refutation's is `{ incarnation: record_of(pre,
/// n).incarnation + 1, status: Alive }`, sent by `n` about itself. This
/// transition does not distinguish those callers, on purpose: the merge rule
/// is supposed to be indifferent to where a record came from, and giving the
/// three cases three transitions would let that indifference be broken by
/// accident in one of them without any theorem here noticing.
pub open spec fn tr_gossip(pre: Cluster, post: Cluster, n: NodeId, incoming: MemberRecord) -> bool {
    post.members == pre.members.insert(n, merge(record_of(pre, n), incoming))
}

/// The one labelled transition this module has so far. A real deployment's
/// probe scheduler, indirect-ping fallback and dissemination piggybacking all
/// produce a `Gossip` eventually; none of them needs a step of their own
/// *here*, because none of them is a merge rule of its own.
pub enum SwimStep {
    Gossip { node: NodeId, incoming: MemberRecord },
}

pub open spec fn swim_step(pre: Cluster, post: Cluster, s: SwimStep) -> bool {
    match s {
        SwimStep::Gossip { node, incoming } => tr_gossip(pre, post, node, incoming),
    }
}

pub open spec fn swim_next(pre: Cluster, post: Cluster) -> bool {
    exists|s: SwimStep| swim_step(pre, post, s)
}

/// Nothing heard from anybody yet.
pub open spec fn swim_init(c: Cluster) -> bool {
    forall|n: NodeId| !(#[trigger] c.members.contains_key(n))
}

/// `tr` is a finite execution of the cluster.
///
/// The multi-trigger on both adjacent states is
/// [`crate::raft::model::raft_execution`]'s, for the same reason: a trigger
/// on `tr[i]` alone introduces `tr[i + 1]`, which matches again and walks off
/// the end of the sequence.
pub open spec fn swim_execution(tr: Seq<Cluster>) -> bool {
    &&& tr.len() > 0
    &&& swim_init(tr[0])
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> swim_next(tr[i], tr[i + 1]))
}

pub open spec fn swim_reachable(c: Cluster) -> bool {
    exists|tr: Seq<Cluster>| swim_execution(tr) && tr[tr.len() - 1] == c
}

} // verus!
