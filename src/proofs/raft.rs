//! **Election Safety**: at most one leader per term.
//!
//! The whole argument is three sentences long, and it is worth reading before
//! the code because everything below is bookkeeping around it:
//!
//! 1. a leader won a *majority* of its term's votes;
//! 2. any two majorities of the same cluster share a member;
//! 3. a member votes at most once per term.
//!
//! So two leaders in one term would need a server that voted for both.
//!
//! # Where this differs from the ownership proof next door
//!
//! `proofs::exclusivity` proves the same shape of statement — at most one
//! authoritative party per generation — and proves it a completely different
//! way. There, exclusivity is *structural*: `may_mutate` is true in exactly one
//! shape, `Owned { owner, epoch }`, so two owners is not a state the model can
//! represent. The work is all in showing the transitions never reach a bad
//! state, and it rests on the registry being updated atomically.
//!
//! Here nothing is structural. `Cluster` can perfectly well hold two servers
//! both believing themselves leader at term 7; that state is representable, and
//! ruling it out is a *counting* argument over a set that no single participant
//! can see. That is what consensus buys and what it costs.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::*;

verus! {

// ---------------------------------------------------------------------------
// The counting argument
// ---------------------------------------------------------------------------

/// **Any two majorities of the same cluster share a member.**
///
/// The one piece of real mathematics in this module, and the reason Raft needs
/// no coordinator: `|a| + |b| > |members|` cannot hold if `a` and `b` are
/// disjoint subsets of `members`, because then `|a ∪ b| = |a| + |b|` would
/// exceed a set it is contained in.
pub proof fn lemma_quorums_intersect(c: Cluster, a: Set<ServerId>, b: Set<ServerId>)
    requires
        is_quorum(c, a),
        is_quorum(c, b),
    ensures
        exists|n: ServerId| a.contains(n) && b.contains(n),
{
    // `a ∪ b` is still inside the cluster, so it cannot be larger than it.
    assert forall|n: ServerId| a.union(b).contains(n) implies c.members.contains(n) by {}
    assert(a.union(b).subset_of(c.members));
    lemma_len_subset(a.union(b), c.members);

    // Inclusion–exclusion: |a ∪ b| + |a ∩ b| == |a| + |b|.
    lemma_set_intersect_union_lens(a, b);

    // Two majorities: 2|a| > m and 2|b| > m, so |a| + |b| > m >= |a ∪ b|, and
    // the intersection has to absorb the difference.
    assert(a.intersect(b).len() > 0);

    // `lemma_set_empty_equivalency_len` is the one that turns a non-zero
    // cardinality into an element: `s.len() != 0 ==> exists|x| s.contains(x)`.
    lemma_set_empty_equivalency_len(a.intersect(b));
    let n = choose|n: ServerId| a.intersect(b).contains(n);
    assert(a.contains(n) && b.contains(n));
}

// ---------------------------------------------------------------------------
// The inductive invariant
// ---------------------------------------------------------------------------

/// **A server votes at most once per term.** Sentence 3 of the argument.
pub open spec fn inv_votes_unique(c: Cluster) -> bool {
    forall|v1: Vote, v2: Vote|
        #![trigger c.votes.contains(v1), c.votes.contains(v2)]
        c.votes.contains(v1) && c.votes.contains(v2) && v1.voter == v2.voter && v1.term
            == v2.term ==> v1.candidate == v2.candidate
}

/// **A cast vote is never ahead of its voter's term.**
///
/// Not part of the headline argument, and the clause without which the rest
/// does not survive induction: it is what makes a fresh candidacy safe. When a
/// server times out into term `t + 1` it votes for itself there, and that vote
/// can only be its *first* in that term because this invariant says any earlier
/// vote of its own would have dragged its term up to meet it.
pub open spec fn inv_vote_implies_term(c: Cluster) -> bool {
    forall|v: Vote|
        #![trigger c.votes.contains(v)]
        c.votes.contains(v) && c.servers.contains_key(v.voter) ==> c.servers[v.voter].current_term
            >= v.term
}

/// **A leader won a majority of its own term.** Sentence 1 of the argument.
pub open spec fn inv_leader_quorum(c: Cluster) -> bool {
    forall|n: ServerId|
        #![trigger c.servers[n]]
        c.servers.contains_key(n) && is_leader(c.servers[n]) ==> won_election(
            c,
            n,
            c.servers[n].current_term,
        )
}

/// The invariant every transition maintains.
pub open spec fn raft_inv(c: Cluster) -> bool {
    &&& inv_votes_unique(c)
    &&& inv_vote_implies_term(c)
    &&& inv_leader_quorum(c)
}

// ---------------------------------------------------------------------------
// Frame lemmas
// ---------------------------------------------------------------------------

/// **A majority, once won, stays won.** Votes only accumulate, so a tally can
/// only grow, and the cluster's size does not change.
///
/// This is the counterpart of `proofs::properties::theorem_issued_monotone`:
/// the reason a leader elected at term 7 is still, as a matter of record, the
/// winner of term 7 no matter what happens afterwards.
pub proof fn lemma_quorum_survives(pre: Cluster, post: Cluster, cand: ServerId, term: Term)
    requires
        post.members == pre.members,
        pre.votes.subset_of(post.votes),
        won_election(pre, cand, term),
    ensures
        won_election(post, cand, term),
{
    assert forall|n: ServerId| voters_for(pre, cand, term).contains(n) implies voters_for(
        post,
        cand,
        term,
    ).contains(n) by {
        assert(pre.members.contains(n));
        assert(pre.votes.contains(Vote { voter: n, term: term, candidate: cand }));
    }
    assert(voters_for(pre, cand, term).subset_of(voters_for(post, cand, term)));
    lemma_len_subset(voters_for(pre, cand, term), voters_for(post, cand, term));
    assert forall|n: ServerId| voters_for(post, cand, term).contains(n) implies post.members
        .contains(n) by {}
    assert(voters_for(post, cand, term).subset_of(post.members));
}

/// Every leader other than the one this step touched is untouched, so its
/// majority survives.
proof fn lemma_other_leaders_keep_quorums(pre: Cluster, post: Cluster, touched: ServerId)
    requires
        raft_inv(pre),
        post.members == pre.members,
        pre.votes.subset_of(post.votes),
        forall|m: ServerId|
            #![trigger post.servers[m]]
            m != touched ==> post.servers.contains_key(m) == pre.servers.contains_key(m)
                && post.servers[m] == pre.servers[m],
        !is_leader(post.servers[touched]) || post.servers[touched] == pre.servers[touched],
    ensures
        inv_leader_quorum(post),
{
    assert forall|m: ServerId| post.servers.contains_key(m) && is_leader(post.servers[m]) implies
    won_election(post, m, post.servers[m].current_term) by {
        assert(pre.servers.contains_key(m));
        assert(pre.servers[m] == post.servers[m]);
        assert(won_election(pre, m, pre.servers[m].current_term));
        lemma_quorum_survives(pre, post, m, pre.servers[m].current_term);
    }
}

// ---------------------------------------------------------------------------
// Preservation, one transition at a time
// ---------------------------------------------------------------------------

proof fn lemma_timeout_preserves_inv(pre: Cluster, post: Cluster, n: ServerId)
    requires
        raft_inv(pre),
        tr_timeout(pre, post, n),
    ensures
        raft_inv(post),
{
    let t = (pre.servers[n].current_term + 1) as nat;
    let fresh = Vote { voter: n, term: t, candidate: n };

    // Uniqueness. The only new vote is `n`'s for itself at `t`, and `n` cannot
    // already have voted at `t`: `inv_vote_implies_term` says such a vote would
    // have put `n`'s term at `t` or above, and it was at `t - 1`.
    assert forall|v1: Vote, v2: Vote|
        post.votes.contains(v1) && post.votes.contains(v2) && v1.voter == v2.voter && v1.term
            == v2.term implies v1.candidate == v2.candidate by {
        if pre.votes.contains(v1) && pre.votes.contains(v2) {
        } else if !pre.votes.contains(v1) && !pre.votes.contains(v2) {
            assert(v1 == fresh);
            assert(v2 == fresh);
        } else if !pre.votes.contains(v1) {
            assert(v1 == fresh);
            assert(pre.votes.contains(v2));
            assert(v2.voter == n && v2.term == t);
            assert(pre.servers.contains_key(n));
            assert(pre.servers[n].current_term >= t);
        } else {
            assert(v2 == fresh);
            assert(pre.votes.contains(v1));
            assert(v1.voter == n && v1.term == t);
            assert(pre.servers.contains_key(n));
            assert(pre.servers[n].current_term >= t);
        }
    }

    // Terms. `n` moved up to `t` and its new vote is at `t`; every other
    // server, and every other vote, is untouched.
    assert forall|v: Vote| post.votes.contains(v) && post.servers.contains_key(v.voter) implies
    post.servers[v.voter].current_term >= v.term by {
        if v.voter == n {
            assert(post.servers[n].current_term == t);
            if pre.votes.contains(v) {
                assert(pre.servers[n].current_term >= v.term);
            } else {
                assert(v == fresh);
            }
        } else {
            assert(post.servers[v.voter] == pre.servers[v.voter]);
            assert(pre.votes.contains(v));
        }
    }

    // Leaders. `n` is a candidate now, so it is not one of them.
    assert(!is_leader(post.servers[n]));
    lemma_other_leaders_keep_quorums(pre, post, n);
}

proof fn lemma_grant_vote_preserves_inv(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
)
    requires
        raft_inv(pre),
        tr_grant_vote(pre, post, voter, cand, term),
    ensures
        raft_inv(post),
{
    let fresh = Vote { voter: voter, term: term, candidate: cand };

    // Uniqueness, straight from the guard: `!has_voted(pre, voter, term)` says
    // no vote of `voter`'s at `term` is on record, so the new one cannot
    // collide with an old one.
    assert forall|v1: Vote, v2: Vote|
        post.votes.contains(v1) && post.votes.contains(v2) && v1.voter == v2.voter && v1.term
            == v2.term implies v1.candidate == v2.candidate by {
        if pre.votes.contains(v1) && pre.votes.contains(v2) {
        } else if !pre.votes.contains(v1) && !pre.votes.contains(v2) {
            assert(v1 == fresh);
            assert(v2 == fresh);
        } else if !pre.votes.contains(v1) {
            assert(v1 == fresh);
            assert(pre.votes.contains(v2));
            assert(v2.voter == voter && v2.term == term);
            assert(pre.votes.contains(
                Vote { voter: voter, term: term, candidate: v2.candidate },
            ));
            assert(has_voted(pre, voter, term));
        } else {
            assert(v2 == fresh);
            assert(pre.votes.contains(v1));
            assert(v1.voter == voter && v1.term == term);
            assert(pre.votes.contains(
                Vote { voter: voter, term: term, candidate: v1.candidate },
            ));
            assert(has_voted(pre, voter, term));
        }
    }

    // Terms. Granting a vote adopts the term, and the guard says the term is
    // not behind, so every older vote of this voter's is still covered.
    assert forall|v: Vote| post.votes.contains(v) && post.servers.contains_key(v.voter) implies
    post.servers[v.voter].current_term >= v.term by {
        if v.voter == voter {
            assert(post.servers[voter].current_term == term);
            if pre.votes.contains(v) {
                assert(pre.servers[voter].current_term >= v.term);
            } else {
                assert(v == fresh);
            }
        } else {
            assert(post.servers[v.voter] == pre.servers[v.voter]);
            assert(pre.votes.contains(v));
        }
    }

    // Leaders. The voter is a follower now.
    assert(!is_leader(post.servers[voter]));
    lemma_other_leaders_keep_quorums(pre, post, voter);
}

proof fn lemma_become_leader_preserves_inv(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
)
    requires
        raft_inv(pre),
        tr_become_leader(pre, post, n, term),
    ensures
        raft_inv(post),
{
    // Neither the votes nor the terms move, so the first two clauses are the
    // same statement about the same sets.
    assert forall|v: Vote| post.votes.contains(v) && post.servers.contains_key(v.voter) implies
    post.servers[v.voter].current_term >= v.term by {
        if v.voter == n {
            assert(post.servers[n].current_term == pre.servers[n].current_term);
        } else {
            assert(post.servers[v.voter] == pre.servers[v.voter]);
        }
    }

    // The new leader's majority is the step's own guard.
    assert forall|m: ServerId| post.servers.contains_key(m) && is_leader(post.servers[m]) implies
    won_election(post, m, post.servers[m].current_term) by {
        if m == n {
            assert(won_election(pre, n, term));
            lemma_quorum_survives(pre, post, n, term);
            assert(post.servers[n].current_term == term);
        } else {
            assert(pre.servers[m] == post.servers[m]);
            assert(won_election(pre, m, pre.servers[m].current_term));
            lemma_quorum_survives(pre, post, m, pre.servers[m].current_term);
        }
    }
}

proof fn lemma_step_down_preserves_inv(pre: Cluster, post: Cluster, n: ServerId, term: Term)
    requires
        raft_inv(pre),
        tr_step_down(pre, post, n, term),
    ensures
        raft_inv(post),
{
    // Terms only go up, and no vote is cast.
    assert forall|v: Vote| post.votes.contains(v) && post.servers.contains_key(v.voter) implies
    post.servers[v.voter].current_term >= v.term by {
        if v.voter == n {
            assert(post.servers[n].current_term == term);
            assert(pre.servers[n].current_term >= v.term);
        } else {
            assert(post.servers[v.voter] == pre.servers[v.voter]);
        }
    }

    assert(!is_leader(post.servers[n]));
    lemma_other_leaders_keep_quorums(pre, post, n);
}

/// Every transition preserves the invariant.
pub proof fn lemma_raft_step_preserves_inv(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_inv(pre),
        raft_step(pre, post, s),
    ensures
        raft_inv(post),
{
    match s {
        RaftStep::Timeout { server } => lemma_timeout_preserves_inv(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term } => lemma_grant_vote_preserves_inv(
            pre,
            post,
            voter,
            candidate,
            term,
        ),
        RaftStep::BecomeLeader { server, term } => lemma_become_leader_preserves_inv(
            pre,
            post,
            server,
            term,
        ),
        RaftStep::StepDown { server, term } => lemma_step_down_preserves_inv(
            pre,
            post,
            server,
            term,
        ),
        // Neither servers nor votes move; the invariant says nothing about
        // messages, which is why replay is free.
        RaftStep::Replay { msg: _ } => {},
        RaftStep::Stutter => {},
    }
}

pub proof fn lemma_raft_next_preserves_inv(pre: Cluster, post: Cluster)
    requires
        raft_inv(pre),
        raft_next(pre, post),
    ensures
        raft_inv(post),
{
    let s = choose|s: RaftStep| raft_step(pre, post, s);
    lemma_raft_step_preserves_inv(pre, post, s);
}

/// Initial states satisfy it vacuously: nothing has voted and nobody leads.
pub proof fn lemma_raft_init_inv(c: Cluster)
    requires
        raft_init(c),
    ensures
        raft_inv(c),
{
}

/// Every state of an execution satisfies the invariant.
pub proof fn lemma_raft_execution_inv(tr: Seq<Cluster>, i: int)
    requires
        raft_execution(tr),
        0 <= i < tr.len(),
    ensures
        raft_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_raft_init_inv(tr[0]);
    } else {
        let j = i - 1;
        lemma_raft_execution_inv(tr, j);
        // `raft_execution`'s multi-trigger needs a `tr[_ + 1]` term, which
        // `tr[i]` on its own does not provide.
        assert(raft_next(tr[j], tr[j + 1]));
        assert(tr[j + 1] == tr[i]);
        lemma_raft_next_preserves_inv(tr[j], tr[i]);
    }
}

/// **Every reachable cluster state satisfies the invariant.**
pub proof fn theorem_reachable_raft_inv(c: Cluster)
    requires
        raft_reachable(c),
    ensures
        raft_inv(c),
{
    let tr = choose|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c;
    lemma_raft_execution_inv(tr, tr.len() - 1);
}

// ---------------------------------------------------------------------------
// Election Safety
// ---------------------------------------------------------------------------

/// **At most one leader per term**, in any state satisfying the invariant.
pub proof fn theorem_election_safety(c: Cluster, n1: ServerId, n2: ServerId)
    requires
        raft_inv(c),
        c.servers.contains_key(n1),
        c.servers.contains_key(n2),
        is_leader(c.servers[n1]),
        is_leader(c.servers[n2]),
        c.servers[n1].current_term == c.servers[n2].current_term,
    ensures
        n1 == n2,
{
    let t = c.servers[n1].current_term;
    assert(won_election(c, n1, t));
    assert(won_election(c, n2, t));

    lemma_quorums_intersect(c, voters_for(c, n1, t), voters_for(c, n2, t));
    let v = choose|v: ServerId|
        voters_for(c, n1, t).contains(v) && voters_for(c, n2, t).contains(v);

    // `voters_for` is a filter, so membership unfolds straight to the vote.
    assert(c.votes.contains(Vote { voter: v, term: t, candidate: n1 }));
    assert(c.votes.contains(Vote { voter: v, term: t, candidate: n2 }));
}

/// **At most one leader per term, in any reachable state.** The headline, with
/// the invariant discharged rather than assumed.
pub proof fn theorem_election_safety_reachable(c: Cluster, n1: ServerId, n2: ServerId)
    requires
        raft_reachable(c),
        c.servers.contains_key(n1),
        c.servers.contains_key(n2),
        is_leader(c.servers[n1]),
        is_leader(c.servers[n2]),
        c.servers[n1].current_term == c.servers[n2].current_term,
    ensures
        n1 == n2,
{
    theorem_reachable_raft_inv(c);
    theorem_election_safety(c, n1, n2);
}

// ---------------------------------------------------------------------------
// Supporting properties
// ---------------------------------------------------------------------------

/// **No server's term ever decreases.** The Raft counterpart of
/// `proofs::fencing::theorem_epoch_monotone_step`, and for the same reason: an
/// argument that rests on "later means higher" is worth nothing if a
/// participant can go back.
pub proof fn theorem_term_monotone_step(pre: Cluster, post: Cluster, s: RaftStep, n: ServerId)
    requires
        raft_step(pre, post, s),
        pre.servers.contains_key(n),
    ensures
        post.servers.contains_key(n),
        post.servers[n].current_term >= pre.servers[n].current_term,
{
}

/// **A vote is never retracted.** Votes are physical facts, like
/// `model::System::issued`: a crash does not un-cast one, which is exactly why
/// a returning server must not vote again in a term it has already voted in.
pub proof fn theorem_votes_monotone_step(pre: Cluster, post: Cluster, s: RaftStep, v: Vote)
    requires
        raft_step(pre, post, s),
        pre.votes.contains(v),
    ensures
        post.votes.contains(v),
{
}

/// **A candidate cannot win a term by voting for itself in a cluster of more
/// than one.** Not deep, but it is the claim that the quorum threshold is doing
/// work rather than being decorative — with `>=` in place of `>` in
/// [`is_quorum`], a single server could elect itself in any cluster.
pub proof fn theorem_a_lone_vote_is_not_a_majority(c: Cluster, n: ServerId, term: Term)
    requires
        c.members.len() >= 2,
        voters_for(c, n, term).subset_of(Set::empty().insert(n)),
    ensures
        !won_election(c, n, term),
{
    // `lemma_set_empty_len` and `lemma_set_insert_len` are both in vstd's
    // default broadcast group, so the singleton's size needs no argument.
    let just_n = Set::<ServerId>::empty().insert(n);
    assert(just_n.len() == 1);
    lemma_len_subset(voters_for(c, n, term), just_n);
}

} // verus!
