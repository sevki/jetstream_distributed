//! The executable election steps agree with the model.
//!
//! The same obligations `proofs::refinement` discharges for the ownership
//! steps: when a step fires the model's transition fires, to exactly the record
//! the step computed; and when it refuses, the model's transition is not
//! enabled. The second half is the one that carries the weight, because a step
//! function that refused everything would satisfy the first perfectly.
//!
//! # The couplings
//!
//! A step sees one server's record and a couple of booleans; the model's state
//! is a whole `Cluster`. The correspondence is named as hypotheses rather than
//! assumed:
//!
//! | Hypothesis | What supplies it |
//! | --- | --- |
//! | `already_voted == has_voted(c, voter, term)` | the voter's own record of its votes |
//! | `has_quorum == won_election(c, n, term)` | the candidate's tally, via [`crate::raft::steps::is_majority`] |
//! | `c.messages.contains(RequestVote { .. })` | the request that arrived |
//! | `carries_term(c, term)` | the message that carried the higher term |
//!
//! The vote coupling is the one a server can break, and breaking it breaks
//! Election Safety rather than merely the refinement: `already_voted` is what
//! `tr_grant_vote`'s `!has_voted` guard becomes at the machine, and that guard
//! is sentence three of the whole argument. A server that forgets a vote across
//! a restart reports `false` here and votes twice — which is why the record has
//! to be durable, exactly as the ownership registry's epoch floor does.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::steps::*;

verus! {

// ---------------------------------------------------------------------------
// The post-states, built explicitly
// ---------------------------------------------------------------------------

/// Where standing for election sends the cluster.
pub open spec fn timeout_post(c: Cluster, n: Id) -> Cluster {
    Cluster {
        members: c.members,
        servers: c.servers.insert(
            n,
            Server {
                role: Role::Candidate,
                current_term: c.servers[n].current_term + 1,
                log: c.servers[n].log,
                commit: c.servers[n].commit,
            },
        ),
        votes: c.votes.insert(
            Vote { voter: n, term: c.servers[n].current_term + 1, candidate: n },
        ),
        messages: c.messages.insert(
            RaftMessage::RequestVote {
                term: c.servers[n].current_term + 1,
                candidate: n,
                last_term: last_term(c.servers[n].log),
                last_index: c.servers[n].log.len(),
            },
        ),
        created: c.created,
        led: c.led,
        committed: c.committed,
        // The self-vote's judgement. `tr_timeout` writes it, so a post-state
        // that left `voted_with` alone would no longer be where the transition
        // sends the cluster — which is what this module exists to check.
        voted_with: c.voted_with.insert(
            VoteLog {
                voter: n,
                term: c.servers[n].current_term + 1,
                candidate: n,
                voter_log: c.servers[n].log,
                cand_last_term: last_term(c.servers[n].log),
                cand_last_index: c.servers[n].log.len(),
            },
        ),
    }
}

/// Where granting a vote sends it.
///
/// It takes the candidate's summary now, and did not before: the post-state
/// records the *judgement*, and a judgement is a relation between the voter's
/// log and what it was weighed against. A post-state that dropped the summary
/// would be describing a different transition.
pub open spec fn grant_vote_post(
    c: Cluster,
    voter: Id,
    cand: Id,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
) -> Cluster {
    Cluster {
        members: c.members,
        servers: c.servers.insert(
            voter,
            Server {
                role: Role::Follower,
                current_term: term,
                log: c.servers[voter].log,
                commit: c.servers[voter].commit,
            },
        ),
        votes: c.votes.insert(Vote { voter: voter, term: term, candidate: cand }),
        messages: c.messages.insert(
            RaftMessage::VoteGranted { term: term, voter: voter, candidate: cand },
        ),
        created: c.created,
        led: c.led,
        committed: c.committed,
        voted_with: c.voted_with.insert(
            VoteLog {
                voter: voter,
                term: term,
                candidate: cand,
                voter_log: c.servers[voter].log,
                cand_last_term: cand_last_term,
                cand_last_index: cand_last_index,
            },
        ),
    }
}

/// Where taking the term sends it.
pub open spec fn become_leader_post(c: Cluster, n: Id, term: Term) -> Cluster {
    Cluster {
        members: c.members,
        servers: c.servers.insert(
            n,
            Server {
                role: Role::Leader,
                current_term: term,
                log: c.servers[n].log,
                commit: c.servers[n].commit,
            },
        ),
        votes: c.votes,
        messages: c.messages.insert(RaftMessage::Heartbeat { term: term, leader: n }),
        created: c.created,
        led: c.led.insert(Led { server: n, term: term }),
        committed: c.committed,
        voted_with: c.voted_with,
    }
}

/// Where stepping down sends it.
pub open spec fn step_down_post(c: Cluster, n: Id, term: Term) -> Cluster {
    Cluster {
        members: c.members,
        servers: c.servers.insert(
            n,
            Server {
                role: Role::Follower,
                current_term: term,
                log: c.servers[n].log,
                commit: c.servers[n].commit,
            },
        ),
        votes: c.votes,
        messages: c.messages,
        created: c.created,
        led: c.led,
        committed: c.committed,
        voted_with: c.voted_with,
    }
}

// ---------------------------------------------------------------------------
// Timeout
// ---------------------------------------------------------------------------

pub proof fn theorem_timeout_step_refines_tr_timeout(c: Cluster, n: Id)
    requires
        c.members.contains(n),
        c.servers.contains_key(n),
        timeout_fires(c.servers[n].role),
    ensures
        tr_timeout(c, timeout_post(c, n), n),
        timeout_post(c, n).servers[n].role == Role::Candidate,
        timeout_post(c, n).servers[n].current_term == c.servers[n].current_term + 1,
        // Standing for election does not touch the log. Worth stating rather
        // than reading off the definition: it is half of Leader Append-Only.
        timeout_post(c, n).servers[n].log == c.servers[n].log,
{
}

/// A refused timeout is a transition the model could not have taken either.
pub proof fn theorem_timeout_step_refuses_exactly_when_disabled(
    c: Cluster,
    post: Cluster,
    n: Id,
)
    requires
        !timeout_fires(c.servers[n].role),
    ensures
        !tr_timeout(c, post, n),
{
}

// ---------------------------------------------------------------------------
// Granting a vote
// ---------------------------------------------------------------------------

pub proof fn theorem_grant_vote_step_refines_tr_grant_vote(
    c: Cluster,
    voter: Id,
    cand: Id,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        c.members.contains(voter),
        c.members.contains(cand),
        c.servers.contains_key(voter),
        c.messages.contains(
            RaftMessage::RequestVote {
                term: term,
                candidate: cand,
                last_term: cand_last_term,
                last_index: cand_last_index,
            },
        ),
        grant_vote_fires(c.servers[voter].current_term, term, has_voted(c, voter, term)),
        // The other half of the guard, and the half the executable step does
        // not decide: a question about two logs rather than about a term.
        at_least_as_up_to_date(cand_last_term, cand_last_index, c.servers[voter].log),
    ensures
        tr_grant_vote(
            c,
            grant_vote_post(c, voter, cand, term, cand_last_term, cand_last_index),
            voter,
            cand,
            term,
            cand_last_term,
            cand_last_index,
        ),
        grant_vote_post(c, voter, cand, term, cand_last_term, cand_last_index).servers[voter].role
            == Role::Follower,
        grant_vote_post(c, voter, cand, term, cand_last_term, cand_last_index).servers[voter]
            .current_term == term,
        grant_vote_post(c, voter, cand, term, cand_last_term, cand_last_index).servers[voter].log
            == c.servers[voter].log,
{
}

/// **A refused vote is a vote the model would not have granted.**
///
/// With the coupling in place, refusing means the term was behind or the voter
/// had already spent its vote — and the second of those is the guard two
/// leaders in one term would have to get past.
pub proof fn theorem_grant_vote_step_refuses_exactly_when_disabled(
    c: Cluster,
    post: Cluster,
    voter: Id,
    cand: Id,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        !grant_vote_fires(c.servers[voter].current_term, term, has_voted(c, voter, term)),
    ensures
        !tr_grant_vote(c, post, voter, cand, term, cand_last_term, cand_last_index),
{
}

// ---------------------------------------------------------------------------
// Taking the term
// ---------------------------------------------------------------------------

pub proof fn theorem_become_leader_step_refines_tr_become_leader(
    c: Cluster,
    n: Id,
    term: Term,
)
    requires
        c.servers.contains_key(n),
        become_leader_fires(
            c.servers[n].role,
            c.servers[n].current_term,
            term,
            won_election(c, n, term),
        ),
    ensures
        tr_become_leader(c, become_leader_post(c, n, term), n, term),
        become_leader_post(c, n, term).servers[n].role == Role::Leader,
        become_leader_post(c, n, term).servers[n].log == c.servers[n].log,
{
}

pub proof fn theorem_become_leader_step_refuses_exactly_when_disabled(
    c: Cluster,
    post: Cluster,
    n: Id,
    term: Term,
)
    requires
        !become_leader_fires(
            c.servers[n].role,
            c.servers[n].current_term,
            term,
            won_election(c, n, term),
        ),
    ensures
        !tr_become_leader(c, post, n, term),
{
}

// ---------------------------------------------------------------------------
// Stepping down
// ---------------------------------------------------------------------------

/// `carries_term` is a hypothesis rather than something the step checks: a
/// server steps down because a message arrived carrying the higher term, and
/// that the message is on the network is a fact about how the step was reached.
pub proof fn theorem_step_down_step_refines_tr_step_down(c: Cluster, n: Id, term: Term)
    requires
        c.servers.contains_key(n),
        carries_term(c, term),
        step_down_fires(c.servers[n].current_term, term),
    ensures
        tr_step_down(c, step_down_post(c, n, term), n, term),
        step_down_post(c, n, term).servers[n].role == Role::Follower,
        // Stepping down changes who you think you are, not what you recorded.
        step_down_post(c, n, term).servers[n].log == c.servers[n].log,
{
}

pub proof fn theorem_step_down_step_refuses_exactly_when_disabled(
    c: Cluster,
    post: Cluster,
    n: Id,
    term: Term,
)
    requires
        !step_down_fires(c.servers[n].current_term, term),
    ensures
        !tr_step_down(c, post, n, term),
{
}

// ---------------------------------------------------------------------------
// Yielding to a leader of your own term
// ---------------------------------------------------------------------------

/// **`tr_append_entries` makes its follower a follower.**
///
/// Read off the transition, and worth stating because it is the only place the
/// model demotes a server without advancing its term — the case
/// `tr_step_down` cannot reach. It is what justifies
/// [`crate::raft::steps::follow_step`]: a candidate that accepts an append from
/// the leader of the term it is standing in stops standing, and its term does
/// not move.
pub proof fn theorem_an_append_makes_its_receiver_a_follower(
    c: Cluster,
    post: Cluster,
    leader: Id,
    follower: Id,
    prefix: nat,
)
    requires
        tr_append_entries(c, post, leader, follower, prefix),
    ensures
        post.servers[follower].role == Role::Follower,
        post.servers[follower].current_term == c.servers[follower].current_term,
{
}

/// The step computes exactly that role change.
///
/// Stated against the transition rather than against a post-state of its own:
/// `follow_step` does not construct a cluster, it reports the `(role, term)`
/// the model's follower ends up with, and this is the sentence saying so.
pub proof fn theorem_follow_step_agrees_with_tr_append_entries(
    c: Cluster,
    post: Cluster,
    leader: Id,
    follower: Id,
    prefix: nat,
    term: Term,
)
    requires
        tr_append_entries(c, post, leader, follower, prefix),
        term == c.servers[follower].current_term,
        follow_fires(c.servers[follower].role, c.servers[follower].current_term, term),
    ensures
        post.servers[follower].role == Role::Follower,
        post.servers[follower].current_term == term,
{
}

/// **A refused yield is a demotion the model would not have made either — for
/// the one role the model can demote.**
///
/// The asymmetry is deliberate and is the whole content of the theorem. When
/// the term does not match, `tr_append_entries` is not enabled at all, so the
/// refusal is exact. When the role is `Leader` at an equal term the transition
/// *is* enabled in the raw relation, and the step still refuses — which is why
/// the hypothesis here excludes that case rather than pretending it does not
/// exist. Election Safety is what rules it out of any reachable cluster: a
/// leader of `term` receiving an append from another leader of `term` would be
/// two leaders in one term.
pub proof fn theorem_follow_step_refuses_exactly_when_disabled(
    c: Cluster,
    post: Cluster,
    leader: Id,
    follower: Id,
    prefix: nat,
    term: Term,
)
    requires
        !follow_fires(c.servers[follower].role, c.servers[follower].current_term, term),
        term != c.servers[follower].current_term,
    ensures
        !(tr_append_entries(c, post, leader, follower, prefix) && c.servers[leader].current_term
            == term),
{
}

// ---------------------------------------------------------------------------
// Counting
// ---------------------------------------------------------------------------

/// **The `u64` tally answers the model's question about the set.**
///
/// [`is_majority`] is proved to compute `votes + votes > members` in `nat`;
/// this is what makes that the same question as `is_quorum`, given that the
/// numbers really are the sizes of the sets they claim to be. The two
/// hypotheses are where an implementation lies to itself: a tally that
/// double-counts a voter, or a membership count taken from a stale
/// configuration, and neither is a thing a step function can check.
pub proof fn theorem_majority_count_is_a_quorum(
    c: Cluster,
    s: Set<Id>,
    votes: u64,
    members: u64,
)
    requires
        s.subset_of(c.members),
        s.len() == votes as nat,
        c.members.len() == members as nat,
    ensures
        (votes as nat + votes as nat > members as nat) == is_quorum(c, s),
{
}

/// A tally is never larger than the membership, which is [`is_majority`]'s
/// precondition and the reason its subtraction cannot go below zero.
pub proof fn theorem_a_tally_fits_in_the_membership(c: Cluster, s: Set<Id>)
    requires
        s.subset_of(c.members),
    ensures
        s.len() <= c.members.len(),
{
    lemma_len_subset(s, c.members);
}

} // verus!
