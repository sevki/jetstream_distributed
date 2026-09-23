//! Raft's election decisions, executable and verified.
//!
//! The same shape as [`crate::ownership::steps`], one protocol up: each decision a server
//! makes about its own record is a small `u64` function with a postcondition
//! stated in terms of [`crate::raft::model`], and `crate::raft::proofs::refinement` ties
//! those postconditions to the model's transitions.
//!
//! # What a step sees, and what it does not
//!
//! A step here is a pure function of **one server's record** plus the handful of
//! facts the caller has already established: whether this server has already
//! voted in the term being asked about, whether a tally is a majority. It does
//! no I/O, holds no lock, and counts nothing itself.
//!
//! That last exclusion is the important one. Counting votes is where a real
//! Raft implementation goes wrong, so the count is not hidden inside a
//! transition — it is [`is_majority`], its own function with its own
//! postcondition, and the transition takes the answer as an argument.
//!
//! # The one place `u64` is not `nat`
//!
//! Terms, like epochs, are unbounded in the model and bounded here. A server
//! that cannot advance its term refuses rather than wrapping, for the reason
//! `steps::Refusal::Exhausted` gives: wrapping would take the term *backwards*,
//! and every argument in `proofs::raft` rests on terms only going up.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::raft::model::*;

verus! {

/// Why a step did not fire. The protocol's reasons only — a server has others
/// (an unknown peer, an unreachable disk) and a step function never learns
/// about them.
#[derive(Clone, Copy)]
pub enum RaftRefusal {
    /// The `u64` term space is exhausted. See the module docs.
    Exhausted,
    /// This server has already voted in that term. The guard Election Safety
    /// rests on.
    AlreadyVoted,
    /// The request's term is behind this server's own.
    TermBehind,
    /// Only a candidate can take a term it is standing for.
    NotCandidate,
    /// The votes collected are not a majority.
    NoQuorum,
    /// Nothing to step down to: the term is not ahead.
    NotHigher,
    /// A leader does not stand for election; it is already in a term.
    AlreadyLeading,
}

/// A server's role, at the machine.
#[derive(Clone, Copy)]
pub enum ExecRole {
    Follower,
    Candidate,
    Leader,
}

/// A server's election state, at `u64`.
#[derive(Clone, Copy)]
pub struct ExecServer {
    pub role: ExecRole,
    pub current_term: u64,
}

impl ExecRole {
    /// The ghost role this stands for.
    pub open spec fn view(self) -> Role {
        match self {
            ExecRole::Follower => Role::Follower,
            ExecRole::Candidate => Role::Candidate,
            ExecRole::Leader => Role::Leader,
        }
    }
}

/// What a step did.
pub enum RaftOutcome {
    /// It fired, and this is the server's new record.
    Moved(ExecServer),
    /// It did not.
    Refused(RaftRefusal),
}

// ---------------------------------------------------------------------------
// Counting
// ---------------------------------------------------------------------------

/// **Is `votes` a majority of `members`?**
///
/// Its own function, because this is the line a Raft implementation gets
/// wrong. Two ways, both famous:
///
/// * `votes * 2 >= members` — an off-by-one that lets two disjoint halves of an
///   even cluster each elect a leader, which is Election Safety gone;
/// * `votes * 2 > members` — correct, and it **overflows** `u64` for a tally
///   above `2^63`. Absurd for a cluster, and absurd is not the same as
///   impossible when the count is a wire-supplied number.
///
/// `votes > members - votes` is the same predicate with neither hazard: no
/// multiplication to overflow, and the subtraction cannot go below zero because
/// a tally is drawn from the membership. The postcondition is stated in `nat`,
/// where the question has no hazards at all, so the proof is that this `u64`
/// expression answers the unbounded question.
pub fn is_majority(votes: u64, members: u64) -> (r: bool)
    requires
        votes <= members,
    ensures
        r == (votes as nat + votes as nat > members as nat),
{
    votes > members - votes
}

// ---------------------------------------------------------------------------
// The guards and the results, at the model's level
// ---------------------------------------------------------------------------
//
// Stated over a server's `(role, current_term)` rather than over the whole
// `Server`, and that is not a simplification — it is the honest scope. A
// `Server` also carries a log, and **none of these four transitions reads it**:
// standing for election, granting a vote, taking a term and stepping down are
// decisions about who you are and which term you are in. Writing the guards
// over the whole record would have implied the log was consulted, and would
// have forced the executable type to carry a copy of a log it never looks at.
//
// The log's own decisions are a separate matter, and `tr_append_entries` is
// guarded by the log rather than by the role.

/// `tr_timeout`'s guard: anyone not already leading may stand.
pub open spec fn timeout_fires(role: Role) -> bool {
    !match role {
        Role::Leader => true,
        _ => false,
    }
}

/// `tr_grant_vote`'s guard *on the voter's term*: not behind, and not already
/// spent.
///
/// The up-to-date comparison is the other half of that transition's guard and
/// is deliberately not here: it is a question about two logs, which is
/// `at_least_as_up_to_date`'s business, and the server answers it before
/// reaching this step.
pub open spec fn grant_vote_fires(current_term: Term, term: Term, already_voted: bool) -> bool {
    term >= current_term && !already_voted
}

/// `tr_become_leader`'s guard.
pub open spec fn become_leader_fires(
    role: Role,
    current_term: Term,
    term: Term,
    has_quorum: bool,
) -> bool {
    &&& match role {
        Role::Candidate => true,
        _ => false,
    }
    &&& current_term == term
    &&& has_quorum
}

/// `tr_step_down`'s guard: the term really is ahead.
pub open spec fn step_down_fires(current_term: Term, term: Term) -> bool {
    term > current_term
}

// ---------------------------------------------------------------------------
// The executable steps
// ---------------------------------------------------------------------------

/// Stand for election in the next term.
pub fn timeout_step(st: ExecServer) -> (r: RaftOutcome)
    ensures
        match r {
            RaftOutcome::Moved(next) => timeout_fires(st.role.view()) && next.role.view()
                == Role::Candidate && next.current_term as nat == st.current_term as nat + 1,
            RaftOutcome::Refused(why) => !timeout_fires(st.role.view()) || (why is Exhausted),
        },
{
    match st.role {
        ExecRole::Leader => RaftOutcome::Refused(RaftRefusal::AlreadyLeading),
        _ => {
            if st.current_term == u64::MAX {
                RaftOutcome::Refused(RaftRefusal::Exhausted)
            } else {
                RaftOutcome::Moved(
                    ExecServer { role: ExecRole::Candidate, current_term: st.current_term + 1 },
                )
            }
        },
    }
}

/// Grant a vote for `term`.
///
/// `already_voted` is the caller's answer to "has this server voted in `term`?"
/// — it stands for `has_voted(c, voter, term)`, and a server supplies it from
/// the record it keeps of its own votes. It is an argument rather than
/// something the step works out, because the step cannot see that record and
/// pretending otherwise is how the one guard Election Safety rests on gets
/// lost.
pub fn grant_vote_step(st: ExecServer, term: u64, already_voted: bool) -> (r: RaftOutcome)
    ensures
        match r {
            RaftOutcome::Moved(next) => grant_vote_fires(
                st.current_term as nat,
                term as nat,
                already_voted,
            ) && next.role.view() == Role::Follower && next.current_term == term,
            RaftOutcome::Refused(_) => !grant_vote_fires(
                st.current_term as nat,
                term as nat,
                already_voted,
            ),
        },
{
    if term < st.current_term {
        RaftOutcome::Refused(RaftRefusal::TermBehind)
    } else if already_voted {
        RaftOutcome::Refused(RaftRefusal::AlreadyVoted)
    } else {
        RaftOutcome::Moved(ExecServer { role: ExecRole::Follower, current_term: term })
    }
}

/// Take the term this server is standing for, having won it.
///
/// `has_quorum` stands for `won_election(c, n, term)` and is what
/// [`is_majority`] answers.
pub fn become_leader_step(st: ExecServer, term: u64, has_quorum: bool) -> (r: RaftOutcome)
    ensures
        match r {
            RaftOutcome::Moved(next) => become_leader_fires(
                st.role.view(),
                st.current_term as nat,
                term as nat,
                has_quorum,
            ) && next.role.view() == Role::Leader && next.current_term == term,
            RaftOutcome::Refused(_) => !become_leader_fires(
                st.role.view(),
                st.current_term as nat,
                term as nat,
                has_quorum,
            ),
        },
{
    match st.role {
        ExecRole::Candidate => {
            if st.current_term != term {
                RaftOutcome::Refused(RaftRefusal::NotCandidate)
            } else if !has_quorum {
                RaftOutcome::Refused(RaftRefusal::NoQuorum)
            } else {
                RaftOutcome::Moved(ExecServer { role: ExecRole::Leader, current_term: term })
            }
        },
        _ => RaftOutcome::Refused(RaftRefusal::NotCandidate),
    }
}

/// Step down into a strictly higher term.
pub fn step_down_step(st: ExecServer, term: u64) -> (r: RaftOutcome)
    ensures
        match r {
            RaftOutcome::Moved(next) => step_down_fires(st.current_term as nat, term as nat)
                && next.role.view() == Role::Follower && next.current_term == term,
            RaftOutcome::Refused(_) => !step_down_fires(st.current_term as nat, term as nat),
        },
{
    if term > st.current_term {
        RaftOutcome::Moved(ExecServer { role: ExecRole::Follower, current_term: term })
    } else {
        RaftOutcome::Refused(RaftRefusal::NotHigher)
    }
}

} // verus!
