//! Raft leader election: the state space and the transition relation.
//!
//! Like [`crate::model`], this module defines *only* the state and the
//! transitions. It does not import the specification layer, so a specification
//! cannot be quietly tuned until it comes out true.
//!
//! # Why this is in the same repository as the ownership model
//!
//! The ownership model's strongest assumption, stated at `model::System::actors`
//! and first in the README's failure-model table, is that **ownership records
//! are updated atomically**: every epoch-advancing transition reads
//! `pre.actors[a]` and writes `post.actors.insert(a, ..)` in one step, which
//! rules out two coordinators deciding concurrently *by construction* — the
//! model cannot express it. That table says a real deployment must buy the
//! assumption from consensus or from a store with compare-and-swap.
//!
//! This is the first half of buying it. Raft's **Election Safety** — at most one
//! leader per term — is the same sentence as the ownership model's exclusivity
//! theorem with two words changed, and it is bought a completely different way:
//!
//! ```text
//! ownership:  at most one authoritative owner per epoch, because a single
//!             atomic registry hands the epoch out
//! raft:       at most one leader per term, because any two quorums share a
//!             voter and a voter votes once per term
//! ```
//!
//! One assumes the thing that makes exclusivity easy; the other builds it out
//! of counting. Put side by side, they say what a coordinator costs.
//!
//! **Be exact about what this does and does not discharge.** A single leader per
//! term is *not* an atomic registry. The registry's contents — which node owns
//! which actor at which epoch — become a single agreed fact only once entries
//! are replicated and committed, and log replication is not modelled here. What
//! is here is the election, in full, with the safety property that every later
//! Raft argument rests on.
//!
//! # What is modelled
//!
//! * A fixed set of `members`, each with a [`Server`] record: a [`Role`] and a
//!   `current_term`.
//! * `votes`: every vote ever granted, as a `(voter, term, candidate)` triple.
//!   This set never shrinks. A vote is a *physical* fact in the same sense as
//!   `model::System::issued`: a crash does not un-cast it, so a server that
//!   comes back must not vote again for a term it has already voted in.
//! * `messages`: every message ever sent, never shrinking, delivery not
//!   consuming — which gives duplication, reordering, delay and loss for free,
//!   exactly as `model::System::network` does.
//!
//! # What is deliberately not modelled
//!
//! Logs, `AppendEntries`, commitment, and therefore Log Matching, Leader
//! Completeness and State Machine Safety. A leader here is a server that won an
//! election, nothing more. The `lastLogIndex`/`lastLogTerm` comparison in the
//! real `RequestVote` — the up-to-date check — is part of log replication and
//! is absent with it: **its absence cannot make an election unsafe**, because it
//! only ever refuses votes that this model grants, so every run here is a run of
//! the fuller protocol. It is what makes elections *useful* rather than safe,
//! and it is the first thing the log work adds.
#![allow(unused_imports)]

use vstd::prelude::*;

verus! {

/// Identity of a server (a machine in the cluster).
pub type ServerId = nat;

/// A Raft term. Monotonically increasing per server, and the analogue of
/// `model::Epoch` — see the module docs.
pub type Term = nat;

/// What a server currently believes itself to be.
pub enum Role {
    Follower,
    Candidate,
    Leader,
}

/// A server's election-relevant state.
///
/// There is no `voted_for` field: the `votes` set already records every vote
/// ever cast, and a second copy of the same fact is a second thing to keep in
/// step. Everything the protocol asks about a server's voting — has it voted in
/// this term, who for — is a question about `Cluster::votes`.
pub struct Server {
    pub role: Role,
    pub current_term: Term,
}

/// One vote, granted once and never retracted.
pub struct Vote {
    pub voter: ServerId,
    pub term: Term,
    pub candidate: ServerId,
}

/// Protocol messages. Like `model::Message`, these are hints: every transition
/// is additionally guarded by the server's own state, so a replayed or
/// reordered message cannot by itself move the protocol forward.
pub enum RaftMessage {
    /// Candidate -> everyone: stand for election at `term`.
    RequestVote { term: Term, candidate: ServerId },
    /// Voter -> candidate: you have my vote for `term`.
    VoteGranted { term: Term, voter: ServerId, candidate: ServerId },
    /// Leader -> everyone: I won `term`.
    Heartbeat { term: Term, leader: ServerId },
}

/// The whole cluster.
pub struct Cluster {
    /// The servers that exist. Fixed: this model has no reconfiguration, which
    /// is a real and well-known source of Raft unsafety and is out of scope
    /// with the log.
    pub members: Set<ServerId>,
    /// Each member's record. The domain never changes.
    pub servers: Map<ServerId, Server>,
    /// Every vote ever granted. Monotonically grows.
    pub votes: Set<Vote>,
    /// Every message ever sent. Monotonically grows (see the module docs).
    pub messages: Set<RaftMessage>,
}

// ---------------------------------------------------------------------------
// Role tests
// ---------------------------------------------------------------------------
//
// Written as matches rather than as `s.role is Leader` so that nothing about
// this model depends on which enum-test syntax a Verus release offers.

pub open spec fn is_leader(s: Server) -> bool {
    match s.role {
        Role::Leader => true,
        _ => false,
    }
}

pub open spec fn is_candidate(s: Server) -> bool {
    match s.role {
        Role::Candidate => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Votes and quorums
// ---------------------------------------------------------------------------

/// Has `voter` already voted in `term`, for anybody?
///
/// The trigger is the `contains` of a fully-applied `Vote`, so instantiating
/// this existential produces a term the rest of the proof already mentions.
pub open spec fn has_voted(c: Cluster, voter: ServerId, term: Term) -> bool {
    exists|cand: ServerId|
        #[trigger] c.votes.contains(Vote { voter: voter, term: term, candidate: cand })
}

/// The members that voted for `cand` in `term`.
///
/// Defined as a *filter of `members`* rather than as a projection of `votes`,
/// and the difference is load-bearing: a filter is a subset of what it filters
/// by construction, which is precisely the hypothesis
/// [`lemma_quorums_intersect`] needs. Projecting `votes` through a map would
/// give the same elements and no such guarantee, and the cardinality of a
/// mapped set is a much harder thing to reason about.
pub open spec fn voters_for(c: Cluster, cand: ServerId, term: Term) -> Set<ServerId> {
    c.members.filter(
        |n: ServerId| c.votes.contains(Vote { voter: n, term: term, candidate: cand }),
    )
}

/// `s` is a majority of the cluster.
///
/// `s.len() + s.len()` rather than `s.len() * 2`: the two are the same number
/// and only one of them is linear arithmetic.
pub open spec fn is_quorum(c: Cluster, s: Set<ServerId>) -> bool {
    &&& s.subset_of(c.members)
    &&& s.len() + s.len() > c.members.len()
}

/// `n` won `term`.
pub open spec fn won_election(c: Cluster, n: ServerId, term: Term) -> bool {
    is_quorum(c, voters_for(c, n, term))
}

// ---------------------------------------------------------------------------
// Transitions
// ---------------------------------------------------------------------------

/// A server that is not already leading times out and stands for election in
/// the next term, voting for itself.
///
/// The self-vote is recorded in `votes` rather than merely implied, because the
/// whole of Election Safety is a counting argument over that set: a candidate
/// that did not appear in its own tally would be one vote short of the
/// protocol's.
pub open spec fn tr_timeout(pre: Cluster, post: Cluster, n: ServerId) -> bool {
    &&& pre.members.contains(n)
    &&& pre.servers.contains_key(n)
    &&& !is_leader(pre.servers[n])
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        n,
        Server { role: Role::Candidate, current_term: pre.servers[n].current_term + 1 },
    )
    &&& post.votes == pre.votes.insert(
        Vote {
            voter: n,
            term: pre.servers[n].current_term + 1,
            candidate: n,
        },
    )
    &&& post.messages == pre.messages.insert(
        RaftMessage::RequestVote {
            term: pre.servers[n].current_term + 1,
            candidate: n,
        },
    )
}

/// A member grants its vote for `term` to `cand`.
///
/// Three guards, and the middle one is the whole protocol:
///
/// * a `RequestVote` for that term and candidate is on the network — a *hint*,
///   and replaying it grants nothing extra because of the next guard;
/// * **`voter` has not already voted in `term`**. One vote per server per term
///   is what makes two quorums contradictory;
/// * the request's term is not behind the voter's own, which is Raft's rule
///   that a server never votes in a term it has already left.
///
/// Granting a vote also *adopts* the term and drops to follower, which is
/// Raft's "if RPC request or response contains term T > currentTerm, set
/// currentTerm = T, convert to follower".
pub open spec fn tr_grant_vote(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
) -> bool {
    &&& pre.members.contains(voter)
    &&& pre.members.contains(cand)
    &&& pre.servers.contains_key(voter)
    &&& pre.messages.contains(RaftMessage::RequestVote { term: term, candidate: cand })
    &&& term >= pre.servers[voter].current_term
    &&& !has_voted(pre, voter, term)
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        voter,
        Server { role: Role::Follower, current_term: term },
    )
    &&& post.votes == pre.votes.insert(
        Vote { voter: voter, term: term, candidate: cand },
    )
    &&& post.messages == pre.messages.insert(
        RaftMessage::VoteGranted { term: term, voter: voter, candidate: cand },
    )
}

/// A candidate that has collected a quorum of votes for its own term declares
/// itself leader.
///
/// Note what is *not* required: that the votes were delivered, or counted, or
/// that anybody agrees. The guard is the votes themselves, which is what makes
/// the safety argument about the protocol rather than about a tally kept
/// correctly.
pub open spec fn tr_become_leader(pre: Cluster, post: Cluster, n: ServerId, term: Term) -> bool {
    &&& pre.servers.contains_key(n)
    &&& is_candidate(pre.servers[n])
    &&& pre.servers[n].current_term == term
    &&& won_election(pre, n, term)
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(n, Server { role: Role::Leader, current_term: term })
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages.insert(
        RaftMessage::Heartbeat { term: term, leader: n },
    )
}

/// A server learns of a strictly higher term and steps down into it.
///
/// This is the transition that makes a leader stop being one, and it fires on
/// evidence that is only a *hint* — any message carrying the term, from anyone,
/// however old. That is deliberate and it is safe: stepping down never grants
/// authority, and a leader that steps down for no good reason has lost nothing
/// the protocol promised it.
pub open spec fn tr_step_down(pre: Cluster, post: Cluster, n: ServerId, term: Term) -> bool {
    &&& pre.servers.contains_key(n)
    &&& term > pre.servers[n].current_term
    &&& carries_term(pre, term)
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        n,
        Server { role: Role::Follower, current_term: term },
    )
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages
}

/// Some message on the network names `term`.
pub open spec fn carries_term(c: Cluster, term: Term) -> bool {
    ||| exists|cand: ServerId|
        #[trigger] c.messages.contains(RaftMessage::RequestVote { term: term, candidate: cand })
    ||| exists|leader: ServerId|
        #[trigger] c.messages.contains(RaftMessage::Heartbeat { term: term, leader: leader })
}

/// The network redelivers a message sent earlier. Explicit duplication/replay.
pub open spec fn tr_replay(pre: Cluster, post: Cluster, m: RaftMessage) -> bool {
    &&& pre.messages.contains(m)
    &&& post.messages == pre.messages.insert(m)
    &&& post.members == pre.members
    &&& post.servers == pre.servers
    &&& post.votes == pre.votes
}

/// Nothing happens (an arbitrary delay).
pub open spec fn tr_stutter(pre: Cluster, post: Cluster) -> bool {
    &&& post.members == pre.members
    &&& post.servers == pre.servers
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages
}

/// The labelled transitions.
pub enum RaftStep {
    Timeout { server: ServerId },
    GrantVote { voter: ServerId, candidate: ServerId, term: Term },
    BecomeLeader { server: ServerId, term: Term },
    StepDown { server: ServerId, term: Term },
    Replay { msg: RaftMessage },
    Stutter,
}

/// The transition relation, indexed by the step that was taken.
pub open spec fn raft_step(pre: Cluster, post: Cluster, s: RaftStep) -> bool {
    match s {
        RaftStep::Timeout { server } => tr_timeout(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term } => tr_grant_vote(
            pre,
            post,
            voter,
            candidate,
            term,
        ),
        RaftStep::BecomeLeader { server, term } => tr_become_leader(pre, post, server, term),
        RaftStep::StepDown { server, term } => tr_step_down(pre, post, server, term),
        RaftStep::Replay { msg } => tr_replay(pre, post, msg),
        RaftStep::Stutter => tr_stutter(pre, post),
    }
}

/// The unlabelled transition relation.
pub open spec fn raft_next(pre: Cluster, post: Cluster) -> bool {
    exists|s: RaftStep| raft_step(pre, post, s)
}

/// Initial states: everybody a follower at term 0, nothing voted, nothing sent.
pub open spec fn raft_init(c: Cluster) -> bool {
    &&& (forall|n: ServerId| #[trigger]
        c.members.contains(n) ==> c.servers.contains_key(n))
    &&& (forall|n: ServerId|
        #![trigger c.servers[n]]
        c.servers.contains_key(n) ==> !is_leader(c.servers[n]) && c.servers[n].current_term == 0)
    &&& (forall|v: Vote| !(#[trigger] c.votes.contains(v)))
    &&& (forall|m: RaftMessage| !(#[trigger] c.messages.contains(m)))
}

/// `tr` is a finite execution of the cluster.
///
/// The multi-trigger on both adjacent states is the one `model::valid_execution`
/// documents: with `tr[i]` alone the conclusion introduces `tr[i + 1]`, which
/// matches the trigger again and walks off the end of the sequence.
pub open spec fn raft_execution(tr: Seq<Cluster>) -> bool {
    &&& tr.len() > 0
    &&& raft_init(tr[0])
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> raft_next(tr[i], tr[i + 1]))
}

/// `c` is reachable if some finite execution ends in it.
pub open spec fn raft_reachable(c: Cluster) -> bool {
    exists|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c
}

} // verus!
