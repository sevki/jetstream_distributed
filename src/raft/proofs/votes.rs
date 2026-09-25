//! **What a vote was a judgement of** — the third and last of the three records
//! `crate::raft::proofs::terms` named as missing.
//!
//! # Why the state could not say it
//!
//! [`tr_grant_vote`]'s guard is `at_least_as_up_to_date(cand_last_term,
//! cand_last_index, pre.servers[voter].log)`. That is a comparison against a log
//! **at an instant**, and by the time any later theorem asks what the comparison
//! was, the voter has extended, truncated or replaced the log it was about.
//! `Cluster::votes` records that a vote happened; it cannot record what the vote
//! was a judgement *of*.
//!
//! [`Cluster::voted_with`] records both sides of the judgement: the voter's log
//! as it stood, and the candidate summary it was weighed against. Storing only
//! one side would leave the other to be reconstructed from a state that no
//! longer holds it, which is the problem the record exists to solve.
//!
//! The self-vote in [`tr_timeout`] is recorded too. It never constrains
//! anything — a candidate is trivially as up to date as itself — but leaving it
//! out would make [`inv_every_vote_has_its_log`] false exactly where the
//! counting argument needs the record whole.
//!
//! # What is proved here
//!
//! * [`inv_every_vote_has_its_log`] — every vote in `votes` has its judgement on
//!   the record. Without it the record could be *silently partial*, and a
//!   theorem quantified over `voted_with` would say nothing about the votes it
//!   had missed.
//! * [`inv_a_vote_was_up_to_date`] — **every recorded vote went to a candidate
//!   at least as up to date as the voter's log at that moment.** The guard,
//!   promoted from a side-condition on one transition to a fact about every
//!   state.
//! * [`inv_a_recorded_log_is_shaped`] — a recorded log is sorted by term, which
//!   it is because it was some server's log when `inv_log_shape` held of it.
//! * [`theorem_a_voter_saw_nothing_later_than_the_candidate`] — **a candidate
//!   that won a vote was at least as late, in terms, as every entry in that
//!   voter's log.** C43 read off the record rather than off a live state, and
//!   the form the induction's step 3 consumes.
//! * [`theorem_a_winner_shares_a_judged_voter_with_any_quorum`] — **quorum
//!   intersection with the judgement attached.** Any quorum at all meets the
//!   winner's voters in a server whose log at vote time the winner's summary
//!   dominated. Instantiate the quorum with the one that held a committed entry
//!   and this is the induction's step 1 and step 3 joined at the voter.
//!
//! # All three records are now in place. The induction is not.
//!
//! What remains is the **strong induction over terms** itself, and it is worth
//! being exact about why these theorems do not amount to it. Each is a statement
//! about *one* state. The induction relates a commit in term `T` to an election
//! in a later term `T'`, and it needs the quorum that held the entry at commit
//! time and the quorum that voted at election time to be compared **across the
//! run between them** — which is what
//! [`crate::raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`]
//! is for, and that theorem's hypothesis is discharged only by the induction
//! hypothesis at the intervening terms.
//!
//! So: the materials are all here, and the argument that assembles them is not.
//! That is a smaller gap than it was three pushes ago, and it is still a gap.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::proofs::commit::*;
use crate::raft::proofs::election::*;
use crate::raft::proofs::history::*;
use crate::raft::proofs::terms::*;

verus! {

// ---------------------------------------------------------------------------
// The invariants
// ---------------------------------------------------------------------------

/// **Every vote has its judgement on the record.**
///
/// The clause that makes quantifying over `voted_with` mean something. Without
/// it the record could be partial, and a theorem about every recorded vote would
/// be silent about the votes that had not been recorded — which is the failure
/// mode of a ghost field that is written in some arms and not others.
pub open spec fn inv_every_vote_has_its_log(c: Cluster) -> bool {
    forall|v: Vote|
        #[trigger]
        c.votes.contains(v) ==> exists|lg: Seq<Entry>, ct: Term, ci: nat|
            #[trigger]
            c.voted_with.contains(
                VoteLog {
                    voter: v.voter,
                    term: v.term,
                    candidate: v.candidate,
                    voter_log: lg,
                    cand_last_term: ct,
                    cand_last_index: ci,
                },
            )
}

/// **Every recorded vote went to a candidate at least as up to date as the
/// voter's log at that moment.**
///
/// [`tr_grant_vote`]'s guard, promoted from a side-condition on one transition
/// to a fact about every reachable state. This is the clause the rest of the
/// module spends.
pub open spec fn inv_a_vote_was_up_to_date(c: Cluster) -> bool {
    forall|r: VoteLog|
        #[trigger]
        c.voted_with.contains(r) ==> at_least_as_up_to_date(
            r.cand_last_term,
            r.cand_last_index,
            r.voter_log,
        )
}

/// A recorded log's terms are sorted.
///
/// True because a recorded log *was* some server's log at the moment it was
/// recorded, and [`inv_log_shape`] held of it then. The record is a snapshot of
/// a well-shaped thing, so it stays well-shaped — which a live state cannot say
/// on its behalf, since the server has moved on.
pub open spec fn inv_a_recorded_log_is_shaped(c: Cluster) -> bool {
    forall|r: VoteLog| #[trigger] c.voted_with.contains(r) ==> terms_sorted(r.voter_log)
}

/// The vote-record invariant, carrying [`raft_commit_inv`] — and so the commit
/// record, the term structure, Log Matching and Election Safety — with it.
pub open spec fn raft_vote_inv(c: Cluster) -> bool {
    &&& raft_commit_inv(c)
    &&& inv_every_vote_has_its_log(c)
    &&& inv_a_vote_was_up_to_date(c)
    &&& inv_a_recorded_log_is_shaped(c)
}

/// **A step that casts no vote keeps all three clauses.** Seven of the nine
/// transitions; the two that vote are the two that write.
pub proof fn lemma_unvoting_steps_keep_the_record(pre: Cluster, post: Cluster)
    requires
        inv_every_vote_has_its_log(pre),
        inv_a_vote_was_up_to_date(pre),
        inv_a_recorded_log_is_shaped(pre),
        post.votes == pre.votes,
        post.voted_with == pre.voted_with,
    ensures
        inv_every_vote_has_its_log(post),
        inv_a_vote_was_up_to_date(post),
        inv_a_recorded_log_is_shaped(post),
{
}

// ---------------------------------------------------------------------------
// Preservation, one transition at a time
// ---------------------------------------------------------------------------

/// **Standing for election**, which casts the self-vote.
///
/// The record it writes is `at_least_as_up_to_date(last_term(L), L.len(), L)`,
/// which holds by the second disjunct: equal last terms and a log at least as
/// long as itself. Nothing is constrained, and the record is complete.
pub proof fn lemma_timeout_preserves_votes(pre: Cluster, post: Cluster, n: ServerId)
    requires
        raft_vote_inv(pre),
        tr_timeout(pre, post, n),
    ensures
        raft_vote_inv(post),
{
    lemma_timeout_preserves_commit(pre, post, n);

    let lg = pre.servers[n].log;
    let fresh = VoteLog {
        voter: n,
        term: (pre.servers[n].current_term + 1) as nat,
        candidate: n,
        voter_log: lg,
        cand_last_term: last_term(lg),
        cand_last_index: lg.len(),
    };
    assert(post.voted_with == pre.voted_with.insert(fresh));
    assert(at_least_as_up_to_date(last_term(lg), lg.len(), lg));
    assert(terms_sorted(lg));

    assert forall|v: Vote| post.votes.contains(v) implies exists|
        lg2: Seq<Entry>,
        ct: Term,
        ci: nat,
    |
        #[trigger]
        post.voted_with.contains(
            VoteLog {
                voter: v.voter,
                term: v.term,
                candidate: v.candidate,
                voter_log: lg2,
                cand_last_term: ct,
                cand_last_index: ci,
            },
        ) by {
        if pre.votes.contains(v) {
            let w = choose|lg2: Seq<Entry>, ct: Term, ci: nat|
                pre.voted_with.contains(
                    VoteLog {
                        voter: v.voter,
                        term: v.term,
                        candidate: v.candidate,
                        voter_log: lg2,
                        cand_last_term: ct,
                        cand_last_index: ci,
                    },
                );
            assert(post.voted_with.contains(
                VoteLog {
                    voter: v.voter,
                    term: v.term,
                    candidate: v.candidate,
                    voter_log: w.0,
                    cand_last_term: w.1,
                    cand_last_index: w.2,
                },
            ));
        } else {
            assert(post.voted_with.contains(fresh));
        }
    }
}

/// **Granting a vote.** The record's `at_least_as_up_to_date` clause is the
/// transition's own guard, verbatim — which is the whole point of the record.
pub proof fn lemma_grant_vote_preserves_votes(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        raft_vote_inv(pre),
        tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
    ensures
        raft_vote_inv(post),
{
    lemma_grant_vote_preserves_commit(
        pre,
        post,
        voter,
        cand,
        term,
        cand_last_term,
        cand_last_index,
    );

    let fresh = VoteLog {
        voter: voter,
        term: term,
        candidate: cand,
        voter_log: pre.servers[voter].log,
        cand_last_term: cand_last_term,
        cand_last_index: cand_last_index,
    };
    assert(post.voted_with == pre.voted_with.insert(fresh));
    assert(at_least_as_up_to_date(cand_last_term, cand_last_index, pre.servers[voter].log));
    assert(terms_sorted(pre.servers[voter].log));

    assert forall|v: Vote| post.votes.contains(v) implies exists|
        lg2: Seq<Entry>,
        ct: Term,
        ci: nat,
    |
        #[trigger]
        post.voted_with.contains(
            VoteLog {
                voter: v.voter,
                term: v.term,
                candidate: v.candidate,
                voter_log: lg2,
                cand_last_term: ct,
                cand_last_index: ci,
            },
        ) by {
        if pre.votes.contains(v) {
            let w = choose|lg2: Seq<Entry>, ct: Term, ci: nat|
                pre.voted_with.contains(
                    VoteLog {
                        voter: v.voter,
                        term: v.term,
                        candidate: v.candidate,
                        voter_log: lg2,
                        cand_last_term: ct,
                        cand_last_index: ci,
                    },
                );
            assert(post.voted_with.contains(
                VoteLog {
                    voter: v.voter,
                    term: v.term,
                    candidate: v.candidate,
                    voter_log: w.0,
                    cand_last_term: w.1,
                    cand_last_index: w.2,
                },
            ));
        } else {
            assert(post.voted_with.contains(fresh));
        }
    }
}

/// **Every transition preserves the vote-record invariant.**
pub proof fn lemma_raft_step_preserves_votes(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_vote_inv(pre),
        raft_step(pre, post, s),
    ensures
        raft_vote_inv(post),
{
    match s {
        RaftStep::Timeout { server } => lemma_timeout_preserves_votes(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term, cand_last_term, cand_last_index } =>
            lemma_grant_vote_preserves_votes(
                pre,
                post,
                voter,
                candidate,
                term,
                cand_last_term,
                cand_last_index,
            ),
        RaftStep::BecomeLeader { server, term } => {
            lemma_become_leader_preserves_commit(pre, post, server, term);
            lemma_unvoting_steps_keep_the_record(pre, post);
        },
        RaftStep::StepDown { server, term } => {
            lemma_step_down_preserves_commit(pre, post, server, term);
            lemma_unvoting_steps_keep_the_record(pre, post);
        },
        RaftStep::ClientRequest { server, value } => {
            lemma_client_request_preserves_commit(pre, post, server, value);
            lemma_unvoting_steps_keep_the_record(pre, post);
        },
        RaftStep::AppendEntries { leader, follower, prefix } => {
            lemma_append_entries_preserves_terms(pre, post, leader, follower, prefix);
            lemma_untouched_records_keep_commit(pre, post);
            lemma_unvoting_steps_keep_the_record(pre, post);
        },
        RaftStep::AdvanceCommit { server, upto } => {
            lemma_advance_commit_preserves_commit(pre, post, server, upto);
            lemma_unvoting_steps_keep_the_record(pre, post);
        },
        RaftStep::Replay { msg } => {
            lemma_quiet_steps_preserve_commit(pre, post, RaftStep::Replay { msg: msg });
            lemma_unvoting_steps_keep_the_record(pre, post);
        },
        RaftStep::Stutter => {
            lemma_quiet_steps_preserve_commit(pre, post, RaftStep::Stutter);
            lemma_unvoting_steps_keep_the_record(pre, post);
        },
    }
}

/// An initial cluster satisfies it: nothing has voted, so all three clauses are
/// vacuous.
pub proof fn lemma_init_vote_inv(c: Cluster)
    requires
        raft_init(c),
    ensures
        raft_vote_inv(c),
{
    lemma_init_commit_inv(c);
}

/// The unlabelled version. Its own lemma for the trigger-inference reason
/// `lemma_raft_next_preserves_hist` documents.
pub proof fn lemma_raft_next_preserves_votes(pre: Cluster, post: Cluster)
    requires
        raft_vote_inv(pre),
        raft_next(pre, post),
    ensures
        raft_vote_inv(post),
{
    let s = choose|s: RaftStep| raft_step(pre, post, s);
    lemma_raft_step_preserves_votes(pre, post, s);
}

/// Walking an execution.
pub proof fn lemma_raft_execution_vote_inv(tr: Seq<Cluster>, i: int)
    requires
        raft_execution(tr),
        0 <= i < tr.len(),
    ensures
        raft_vote_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_init_vote_inv(tr[0]);
    } else {
        let j = i - 1;
        lemma_raft_execution_vote_inv(tr, j);
        assert(raft_next(tr[j], tr[j + 1]));
        assert(tr[j + 1] == tr[i]);
        lemma_raft_next_preserves_votes(tr[j], tr[i]);
    }
}

/// **The vote-record invariant holds in every reachable state.**
pub proof fn theorem_reachable_vote_inv(c: Cluster)
    requires
        raft_reachable(c),
    ensures
        raft_vote_inv(c),
{
    let tr = choose|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c;
    lemma_raft_execution_vote_inv(tr, tr.len() - 1);
}

// ---------------------------------------------------------------------------
// What the record buys
// ---------------------------------------------------------------------------

/// **A candidate that won a vote was at least as late, in terms, as every entry
/// in that voter's log.**
///
/// C43 read off the record rather than off a live state, and that difference is
/// the whole reason the record exists: C43 is about a voter's log *now*, and by
/// the time the induction asks, "now" is long past.
///
/// One line from [`inv_a_vote_was_up_to_date`] and
/// [`lemma_the_last_term_is_the_largest`]: whichever disjunct of
/// `at_least_as_up_to_date` holds, the candidate's last term is at least the
/// voter's, and the voter's dominates every entry it had.
pub proof fn theorem_a_voter_saw_nothing_later_than_the_candidate(
    c: Cluster,
    r: VoteLog,
    i: nat,
)
    requires
        inv_a_vote_was_up_to_date(c),
        inv_a_recorded_log_is_shaped(c),
        c.voted_with.contains(r),
        i < r.voter_log.len(),
    ensures
        r.voter_log[i as int].term <= r.cand_last_term,
{
    lemma_the_last_term_is_the_largest(r.voter_log, i);
}

/// **Quorum intersection, with the judgement attached.**
///
/// Any quorum whatsoever meets the winner's voters in a server, and for that
/// server the record says what its log looked like when it voted and that the
/// winner's summary dominated it.
///
/// This is where the induction's first and third steps join. Instantiate `q`
/// with the quorum that held a committed entry — the one
/// [`crate::raft::proofs::commit::theorem_a_commit_was_on_a_quorum`] produces —
/// and the shared voter is a server that both held the entry and judged the
/// winner at least as up to date as its own log.
///
/// What it does *not* do is carry the entry across the run between the commit
/// and the election. That is
/// [`crate::raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`],
/// whose hypothesis only the induction discharges.
pub proof fn theorem_a_winner_shares_a_judged_voter_with_any_quorum(
    c: Cluster,
    n: ServerId,
    t: Term,
    q: Set<ServerId>,
) -> (shared: ServerId)
    requires
        raft_vote_inv(c),
        won_election(c, n, t),
        is_quorum(c, q),
    ensures
        q.contains(shared),
        c.votes.contains(Vote { voter: shared, term: t, candidate: n }),
        exists|lg: Seq<Entry>, ct: Term, ci: nat|
            #[trigger]
            c.voted_with.contains(
                VoteLog {
                    voter: shared,
                    term: t,
                    candidate: n,
                    voter_log: lg,
                    cand_last_term: ct,
                    cand_last_index: ci,
                },
            ) && at_least_as_up_to_date(ct, ci, lg),
{
    lemma_quorums_intersect(c, voters_for(c, n, t), q);
    let shared = choose|v: ServerId| voters_for(c, n, t).contains(v) && q.contains(v);

    // `voters_for` is a filter, so membership unfolds straight to the vote.
    assert(c.votes.contains(Vote { voter: shared, term: t, candidate: n }));

    let w = choose|lg: Seq<Entry>, ct: Term, ci: nat|
        c.voted_with.contains(
            VoteLog {
                voter: shared,
                term: t,
                candidate: n,
                voter_log: lg,
                cand_last_term: ct,
                cand_last_index: ci,
            },
        );
    let r = VoteLog {
        voter: shared,
        term: t,
        candidate: n,
        voter_log: w.0,
        cand_last_term: w.1,
        cand_last_index: w.2,
    };
    assert(c.voted_with.contains(r));
    assert(at_least_as_up_to_date(r.cand_last_term, r.cand_last_index, r.voter_log));
    shared
}

/// The same, for any reachable cluster — **judgement included**, which is the
/// whole point and which the first version of this wrapper left out.
///
/// # A postcondition is not inherited
///
/// This wrapper originally ensured only the shared voter and the vote, and
/// stopped there. Its body called the theorem above, whose contract *does*
/// promise the `VoteLog` and its `at_least_as_up_to_date` judgement — but a
/// caller sees only what the wrapper's own `ensures` says. So a proof starting
/// from `raft_reachable` could recover the shared voter and nothing about what
/// that voter saw: the theorem was named "judged", documented as "the same",
/// and contractually weaker than both.
///
/// The existential is therefore repeated here. It costs a duplicated clause and
/// it buys the only thing this theorem is for. Worth stating as a rule, because
/// every `*_reachable` wrapper in this repository has the same shape: **a
/// wrapper's contract is written, not inferred**, and a wrapper that forwards a
/// call does not forward its postconditions.
pub proof fn theorem_a_winner_shares_a_judged_voter_with_any_quorum_reachable(
    c: Cluster,
    n: ServerId,
    t: Term,
    q: Set<ServerId>,
) -> (shared: ServerId)
    requires
        raft_reachable(c),
        won_election(c, n, t),
        is_quorum(c, q),
    ensures
        q.contains(shared),
        c.votes.contains(Vote { voter: shared, term: t, candidate: n }),
        exists|lg: Seq<Entry>, ct: Term, ci: nat|
            #[trigger]
            c.voted_with.contains(
                VoteLog {
                    voter: shared,
                    term: t,
                    candidate: n,
                    voter_log: lg,
                    cand_last_term: ct,
                    cand_last_index: ci,
                },
            ) && at_least_as_up_to_date(ct, ci, lg),
{
    theorem_reachable_vote_inv(c);
    theorem_a_winner_shares_a_judged_voter_with_any_quorum(c, n, t, q)
}

} // verus!
