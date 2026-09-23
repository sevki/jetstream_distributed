//! Raft's election decisions, executable and verified.
//!
//! The same shape as [`crate::steps`], one protocol up: each decision a server
//! makes about its own record is a small `u64` function with a postcondition
//! stated in terms of [`crate::raft`], and `crate::proofs::raft_refinement` ties
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

use crate::raft::*;

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

impl ExecServer {
    /// The ghost record this stands for.
    pub open spec fn view(self) -> Server {
        Server {
            role: match self.role {
                ExecRole::Follower => Role::Follower,
                ExecRole::Candidate => Role::Candidate,
                ExecRole::Leader => Role::Leader,
            },
            current_term: self.current_term as nat,
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

/// `tr_timeout`'s guard on the server's own record.
pub open spec fn timeout_fires(s: Server) -> bool {
    !is_leader(s)
}

/// Where standing for election leaves the server.
pub open spec fn timeout_next(s: Server) -> Server {
    Server { role: Role::Candidate, current_term: s.current_term + 1 }
}

/// `tr_grant_vote`'s guard on the voter: not behind, and not already spent.
pub open spec fn grant_vote_fires(s: Server, term: Term, already_voted: bool) -> bool {
    term >= s.current_term && !already_voted
}

/// Granting a vote adopts the term and drops to follower.
pub open spec fn grant_vote_next(term: Term) -> Server {
    Server { role: Role::Follower, current_term: term }
}

/// `tr_become_leader`'s guard.
pub open spec fn become_leader_fires(s: Server, term: Term, has_quorum: bool) -> bool {
    is_candidate(s) && s.current_term == term && has_quorum
}

pub open spec fn become_leader_next(term: Term) -> Server {
    Server { role: Role::Leader, current_term: term }
}

/// `tr_step_down`'s guard: the term really is ahead.
pub open spec fn step_down_fires(s: Server, term: Term) -> bool {
    term > s.current_term
}

pub open spec fn step_down_next(term: Term) -> Server {
    Server { role: Role::Follower, current_term: term }
}

// ---------------------------------------------------------------------------
// The executable steps
// ---------------------------------------------------------------------------

/// Stand for election in the next term.
pub fn timeout_step(st: ExecServer) -> (r: RaftOutcome)
    ensures
        match r {
            RaftOutcome::Moved(next) => timeout_fires(st.view()) && next.view() == timeout_next(
                st.view(),
            ),
            RaftOutcome::Refused(why) => !timeout_fires(st.view()) || (why is Exhausted),
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
            RaftOutcome::Moved(next) => grant_vote_fires(st.view(), term as nat, already_voted)
                && next.view() == grant_vote_next(term as nat),
            RaftOutcome::Refused(_) => !grant_vote_fires(st.view(), term as nat, already_voted),
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
            RaftOutcome::Moved(next) => become_leader_fires(st.view(), term as nat, has_quorum)
                && next.view() == become_leader_next(term as nat),
            RaftOutcome::Refused(_) => !become_leader_fires(st.view(), term as nat, has_quorum),
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
            RaftOutcome::Moved(next) => step_down_fires(st.view(), term as nat) && next.view()
                == step_down_next(term as nat),
            RaftOutcome::Refused(_) => !step_down_fires(st.view(), term as nat),
        },
{
    if term > st.current_term {
        RaftOutcome::Moved(ExecServer { role: ExecRole::Follower, current_term: term })
    } else {
        RaftOutcome::Refused(RaftRefusal::NotHigher)
    }
}

} // verus!
