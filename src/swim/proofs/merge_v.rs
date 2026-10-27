//! **The merge algebra.** Facts about [`merge`], none of which mentions
//! a cluster, a step or a run — the point of proving them at this level is
//! that [`crate::swim::proofs::monotone`] then gets to lift them without
//! re-deriving any arithmetic.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::swim::model::*;

verus! {

/// **Merging a record with itself is a no-op.**
///
/// The base case every other theorem here eventually reduces to: `key_geq`
/// is reflexive (equal incarnation, equal rank, `>=` holds), so `merge`'s
/// condition is true and it returns the incoming copy — which is `a` again.
pub proof fn theorem_merge_is_idempotent(a: MemberRecord)
    ensures
        merge(a, a) == a,
{
}

/// **Merging in the same message twice has no more effect than merging it in
/// once.**
///
/// This is the fact that makes gossip's actual delivery model — at-least-once,
/// unordered, arbitrarily duplicated — survive contact with `merge` at all:
/// whatever `b` did to a view the first time, replaying it changes nothing
/// further.
pub proof fn theorem_merge_absorbs_a_repeat(a: MemberRecord, b: MemberRecord)
    ensures
        merge(merge(a, b), b) == merge(a, b),
{
    if key_geq(b, a) {
        // merge(a, b) == b, and merge(b, b) == b by idempotence.
        assert(merge(a, b) == b);
        assert(key_geq(b, b));
        assert(merge(b, b) == b);
    } else {
        // merge(a, b) == a, and the same condition that made it so the first
        // time — !key_geq(b, a) — is unchanged the second time.
        assert(merge(a, b) == a);
        assert(merge(a, b) == a);
    }
}

/// **A record that does not out-rank the local one cannot change it.**
///
/// The safety half of the algebra, and the one with an operational name: a
/// stale or weaker gossip message — a `Suspect` report about a peer this
/// view already knows is `Dead` at the same incarnation, say — is accepted
/// nowhere. `merge`'s condition is `key_geq(incoming, local)`, and the
/// hypothesis here is exactly its negation.
pub proof fn theorem_merge_never_regresses(a: MemberRecord, b: MemberRecord)
    requires
        !key_geq(b, a),
    ensures
        merge(a, b) == a,
{
}

/// **`merge` does not care which record is called `local` and which is
/// called `incoming`.**
///
/// Not true of the *rule* `key_geq(incoming, local)` read literally — that
/// expression is asymmetric, and swapping its arguments is a different
/// comparison — but true of what `merge` returns, because on the one case
/// where the asymmetry could show up, the tie, [`lemma_rank_is_injective`]
/// says the two records being tied between are the same record.
///
/// The case split is on incarnation first, because a strict incarnation
/// difference settles the comparison outright regardless of status; only the
/// equal-incarnation case needs the tie-breaking argument at all.
pub proof fn theorem_merge_is_commutative(a: MemberRecord, b: MemberRecord)
    ensures
        merge(a, b) == merge(b, a),
{
    if a.incarnation > b.incarnation {
        assert(key_geq(a, b));
        assert(!key_geq(b, a));
        assert(merge(a, b) == a);
        assert(merge(b, a) == a);
    } else if a.incarnation < b.incarnation {
        assert(key_geq(b, a));
        assert(!key_geq(a, b));
        assert(merge(a, b) == b);
        assert(merge(b, a) == b);
    } else {
        // Equal incarnations: the comparison is entirely on rank.
        assert(a.incarnation == b.incarnation);
        if status_rank(a.status) > status_rank(b.status) {
            assert(key_geq(a, b));
            assert(!key_geq(b, a));
            assert(merge(a, b) == a);
            assert(merge(b, a) == a);
        } else if status_rank(a.status) < status_rank(b.status) {
            assert(key_geq(b, a));
            assert(!key_geq(a, b));
            assert(merge(a, b) == b);
            assert(merge(b, a) == b);
        } else {
            // Equal incarnation and equal rank: by injectivity, the same
            // status too, and a record is exactly its incarnation and its
            // status — so `a` and `b` are the same record, and it does not
            // matter which one either side of the equation names.
            lemma_rank_is_injective(a.status, b.status);
            assert(a.status == b.status);
            assert(a =~= b);
            assert(key_geq(a, b));
            assert(key_geq(b, a));
            assert(merge(a, b) == b);
            assert(merge(b, a) == a);
        }
    }
}

/// **`key_geq` is total.**
///
/// Every two records compare, one way or the other: a strict incarnation
/// difference decides it outright, and at equal incarnations, `nat`'s own
/// totality on `status_rank`'s four possible values decides it. Needed
/// below because [`theorem_merge_is_associative`]'s case split has to know
/// that failing to establish `key_geq(x, y)` still leaves `key_geq(y, x)`
/// available, rather than leaving a case where neither holds.
pub proof fn lemma_key_geq_total(a: MemberRecord, b: MemberRecord)
    ensures
        key_geq(a, b) || key_geq(b, a),
{
    if a.incarnation > b.incarnation {
        assert(key_geq(a, b));
    } else if a.incarnation < b.incarnation {
        assert(key_geq(b, a));
    } else {
        assert(a.incarnation == b.incarnation);
        if status_rank(a.status) >= status_rank(b.status) {
            assert(key_geq(a, b));
        } else {
            assert(key_geq(b, a));
        }
    }
}

/// **`key_geq` is antisymmetric — up to record equality, not just key
/// equality.**
///
/// If `a` is at least as authoritative as `b` and `b` is at least as
/// authoritative as `a`, the two are not merely tied in key: by
/// [`lemma_rank_is_injective`], a tie in key is a tie in status too, and a
/// record is exactly its incarnation and its status. Needed below for the
/// one case [`theorem_merge_is_associative`] cannot settle by strict
/// domination alone.
pub proof fn lemma_key_geq_antisymmetric(a: MemberRecord, b: MemberRecord)
    requires
        key_geq(a, b),
        key_geq(b, a),
    ensures
        a == b,
{
    if a.incarnation > b.incarnation {
        assert(false);
    } else if a.incarnation < b.incarnation {
        assert(false);
    } else {
        assert(a.incarnation == b.incarnation);
        assert(status_rank(a.status) >= status_rank(b.status));
        assert(status_rank(b.status) >= status_rank(a.status));
        assert(status_rank(a.status) == status_rank(b.status));
        lemma_rank_is_injective(a.status, b.status);
        assert(a.status == b.status);
        assert(a =~= b);
    }
}

/// **`merge` does not care how three records are grouped.**
///
/// The fact `S4`'s commutativity alone does not give: with three or more
/// records in play — the case gossip is actually in, since a node's view is
/// built by folding in one record after another — order-independence needs
/// more than "swapping two arguments doesn't matter." It needs that
/// grouping doesn't matter either, and that is exactly what associativity
/// says. Both together are what let [`crate::swim::proofs::monotone`]'s
/// run-level argument, and any future fold over an arbitrary delivery
/// order, treat `merge` as commutative-monoid-style accumulation rather
/// than as an operation sensitive to the shape of the expression it
/// appears in.
///
/// The proof is a case split on which of the three records' keys
/// dominates, using [`lemma_key_geq_total`] to be sure every case is
/// covered and [`lemma_key_geq_antisymmetric`] for the one case — two
/// records tied in key — that domination alone cannot settle.
pub proof fn theorem_merge_is_associative(a: MemberRecord, b: MemberRecord, c: MemberRecord)
    ensures
        merge(merge(a, b), c) == merge(a, merge(b, c)),
{
    lemma_key_geq_total(a, b);
    lemma_key_geq_total(b, c);
    lemma_key_geq_total(a, c);

    if key_geq(b, a) {
        assert(merge(a, b) == b);
        if key_geq(c, b) {
            assert(merge(b, c) == c);
            lemma_key_geq_transitive(c, b, a);
            assert(merge(a, c) == c);
            assert(merge(merge(a, b), c) == c);
            assert(merge(a, merge(b, c)) == c);
        } else {
            assert(key_geq(b, c));
            assert(merge(b, c) == b);
            assert(merge(merge(a, b), c) == b);
            assert(merge(a, merge(b, c)) == b);
        }
    } else {
        assert(merge(a, b) == a);
        if key_geq(c, b) {
            assert(merge(b, c) == c);
            if key_geq(c, a) {
                assert(merge(a, c) == c);
                assert(merge(merge(a, b), c) == c);
                assert(merge(a, merge(b, c)) == c);
            } else {
                assert(key_geq(a, c));
                assert(merge(a, c) == a);
                assert(merge(merge(a, b), c) == a);
                assert(merge(a, merge(b, c)) == a);
            }
        } else {
            assert(key_geq(b, c));
            assert(merge(b, c) == b);
            assert(key_geq(a, b));
            lemma_key_geq_transitive(a, b, c);
            if key_geq(c, a) {
                lemma_key_geq_antisymmetric(a, c);
                assert(a == c);
                assert(merge(a, c) == a);
            } else {
                assert(merge(a, c) == a);
            }
            assert(merge(merge(a, b), c) == a);
            assert(merge(a, merge(b, c)) == a);
        }
    }
}

/// **`key_geq` is transitive.**
///
/// Not needed by anything in this file — every theorem above is about one
/// application of `merge` — but needed the moment
/// [`crate::swim::proofs::monotone::theorem_a_record_key_never_falls_across_a_run`]
/// chains one step's "did not fall" onto the previous steps' "did not
/// fall": each step gives `key_geq` between adjacent states, and turning a
/// chain of those into a `key_geq` between the ends is exactly this.
pub proof fn lemma_key_geq_transitive(a: MemberRecord, b: MemberRecord, c: MemberRecord)
    requires
        key_geq(a, b),
        key_geq(b, c),
    ensures
        key_geq(a, c),
{
    if a.incarnation > b.incarnation {
        // Either disjunct of key_geq(b, c) gives b.incarnation >= c.incarnation.
        assert(b.incarnation >= c.incarnation);
        assert(a.incarnation > c.incarnation);
        assert(key_geq(a, c));
    } else {
        // key_geq(a, b)'s first disjunct is false, so its second must hold.
        assert(a.incarnation == b.incarnation);
        assert(status_rank(a.status) >= status_rank(b.status));
        if b.incarnation > c.incarnation {
            assert(a.incarnation > c.incarnation);
            assert(key_geq(a, c));
        } else {
            assert(b.incarnation == c.incarnation);
            assert(status_rank(b.status) >= status_rank(c.status));
            assert(a.incarnation == c.incarnation);
            assert(status_rank(a.status) >= status_rank(c.status));
            assert(key_geq(a, c));
        }
    }
}

/// **No report at the same or an older incarnation can undo a departure.**
///
/// A node that has left stays left against everything that was already in
/// flight when it left: a suspicion timer started before the departure, a
/// `Dead` verdict that arrives late, an `Alive` record from before. All of them
/// carry an incarnation no higher than the departure's, and `Left` is the
/// highest rank, so `merge` returns the departure unchanged.
///
/// The one record at the same incarnation that *is* `Left` is the departure
/// itself, and by [`lemma_rank_is_injective`] it is the same record, so merging
/// it in again changes nothing either.
pub proof fn theorem_a_departure_outlasts_every_report_at_or_below_it(
    left: MemberRecord,
    r: MemberRecord,
)
    requires
        left.status == Status::Left,
        r.incarnation <= left.incarnation,
    ensures
        merge(left, r) == left,
{
    if r.incarnation < left.incarnation {
        assert(!key_geq(r, left));
    } else if r.status == Status::Left {
        assert(r == left);
        assert(key_geq(r, left));
    } else {
        assert(status_rank(r.status) < status_rank(left.status));
        assert(!key_geq(r, left));
    }
}

/// **Only a higher incarnation brings a departed member back.**
///
/// The converse of the theorem above, and the form a service uses: if hearing
/// a record changed what a node believed about a member that had left, then the
/// record carried a higher incarnation. In the crash-fault model only that member
/// produces one, by refuting; the theorem does not say so, and a member that lies
/// about a third party (which the service believes) can forge one.
pub proof fn theorem_only_a_higher_incarnation_revives_a_departure(
    left: MemberRecord,
    r: MemberRecord,
)
    requires
        left.status == Status::Left,
        merge(left, r) != left,
    ensures
        r.incarnation > left.incarnation,
{
    if r.incarnation <= left.incarnation {
        theorem_a_departure_outlasts_every_report_at_or_below_it(left, r);
    }
}

} // verus!
