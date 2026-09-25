//! Raft: the state space and the transition relation.
//!
//! Like [`crate::ownership::model`], this module defines *only* the state and the
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
//! are replicated *and the replication is proved to agree*. The transitions that
//! replicate are here; the theorems that would make agreement a fact are not.
//! See "What is modelled but not yet proved" below, which is the honest line
//! between the two.
//!
//! # What is modelled
//!
//! * A fixed set of `members`, each with a [`Server`] record: a [`Role`], a
//!   `current_term`, a `log` and a `commit` count.
//! * `votes`: every vote ever granted, as a `(voter, term, candidate)` triple.
//!   This set never shrinks. A vote is a *physical* fact in the same sense as
//!   `model::System::issued`: a crash does not un-cast it, so a server that
//!   comes back must not vote again for a term it has already voted in.
//! * `messages`: every message ever sent, never shrinking, delivery not
//!   consuming — which gives duplication, reordering, delay and loss for free,
//!   exactly as `model::System::network` does.
//! * The election: [`tr_timeout`], [`tr_grant_vote`] — with the
//!   `lastLogIndex`/`lastLogTerm` up-to-date comparison, see
//!   [`at_least_as_up_to_date`] — [`tr_become_leader`] and [`tr_step_down`].
//! * The log: [`tr_client_request`] stamps an entry with its leader's term,
//!   [`tr_append_entries`] carries one entry under the consistency check and
//!   truncates whatever diverged, and [`tr_advance_commit`] advances the commit
//!   point under **figure 8's restriction** — a majority holding a prefix is not
//!   enough unless the last entry of that prefix is of the committing leader's
//!   own term.
//!
//! * The history: [`Cluster::created`], [`Cluster::led`] and
//!   [`Cluster::committed`], three **ghost** fields recording what the state
//!   cannot — every entry any leader ever made, every `(server, term)` ever
//!   led, and every entry any leader ever committed. Written and never read,
//!   which `crate::raft::proofs::history` proves rather than promises.
//!
//!   The third is the one whose absence is felt most sharply. `Server::commit`
//!   is a count, and it *retreats* when a truncation cuts below it — so without
//!   [`Cluster::committed`] a safety property about committed entries has
//!   nothing to quantify over once the retreat has happened.
//!
//! # What is proved
//!
//! Election Safety, in `crate::raft::proofs::election`. The single-step log
//! properties, in `crate::raft::proofs::log`. And **Log Matching**, in
//! `crate::raft::proofs::history`: two logs that agree on an entry's term at an
//! index agree on every entry at and below it.
//!
//! # What is modelled but not yet proved
//!
//! **Leader Completeness and State Machine Safety.** They need Log Matching plus
//! an induction over terms relating [`at_least_as_up_to_date`] — the guard that
//! restricts elections by the log — to what has been committed. A follower here
//! will still truncate entries it had committed, which is faithful Raft; the
//! protection against that is supposed to come from the election restriction,
//! and the election restriction's proof is what is missing.
//!
//! Half of the election restriction *is* proved, in
//! `crate::raft::proofs::terms`: a candidate whose last term is behind an entry
//! the voter holds cannot collect that vote at all. What is missing is the case
//! where the candidate's last term is at or above the voter's, which is where
//! the induction over terms actually lives.
//!
//! So: the transition system includes replication; the verified guarantees now
//! reach agreement between logs, and stop short of agreement surviving a leader
//! change. Read any claim about this module against that line.
//!
//! # What is deliberately not modelled
//!
//! Reconfiguration. Membership is fixed at `members` and no transition changes
//! it, which is not an oversight: joint consensus is a separate protocol with
//! its own well-known unsafety, and modelling it half-way would be worse than
//! not modelling it.
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

/// One log entry.
///
/// `value` is opaque on purpose. What a state machine does with a command is
/// not this model's business, and keeping it opaque is what makes the safety
/// argument about *ordering* — every server applies the same commands in the
/// same order — rather than about what the commands mean.
pub struct Entry {
    pub term: Term,
    pub value: nat,
}

/// A server's state.
///
/// There is no `voted_for` field: the `votes` set already records every vote
/// ever cast, and a second copy of the same fact is a second thing to keep in
/// step. Everything the protocol asks about a server's voting — has it voted in
/// this term, who for — is a question about `Cluster::votes`.
pub struct Server {
    pub role: Role,
    pub current_term: Term,
    /// The replicated log. Index 0 is the first entry; the paper counts from 1.
    pub log: Seq<Entry>,
    /// **How many entries are committed**, not the index of the last one.
    ///
    /// A count rather than an index, so "nothing is committed" is `0` rather
    /// than a sentinel, and `commit` is exactly the length of the committed
    /// prefix. Off-by-one errors around `commitIndex` are a known hazard in
    /// Raft implementations and this is the cheapest way not to have them.
    pub commit: nat,
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
    ///
    /// Carries the candidate's log summary, because the voter's up-to-date
    /// check is about the candidate's log and the voter cannot see it. Reading
    /// the candidate's *current* log in the guard instead would be a model in
    /// which a vote is decided on information that did not exist when it was
    /// asked for.
    RequestVote { term: Term, candidate: ServerId, last_term: Term, last_index: nat },
    /// Voter -> candidate: you have my vote for `term`.
    VoteGranted { term: Term, voter: ServerId, candidate: ServerId },
    /// Leader -> everyone: I won `term`.
    Heartbeat { term: Term, leader: ServerId },
}

/// **Ghost.** Which `(term, index)` an entry was created at.
///
/// The pair that names an entry in Raft's own argument: Election Safety says
/// one leader per term, so a term and an index between them name a single act
/// of creation by a single server.
pub struct Slot {
    pub term: Term,
    pub index: nat,
}

/// **Ghost.** What a leader recorded when it created an entry.
pub struct Creation {
    pub value: nat,
    /// The term of the entry immediately before this one, or `0` for the first.
    ///
    /// **This is the field that makes Log Matching an induction rather than a
    /// wish.** Knowing two logs agree on an entry's value at some slot says
    /// nothing about what came before it; knowing they agree on the *term
    /// before it* steps the argument down one index, and repeating that reaches
    /// index 0. `tr_append_entries`' consistency check is exactly the guard
    /// that keeps this true — which is what that check is for.
    pub prev_term: Term,
}

/// **Ghost.** A server has, at some point, been leader of a term.
pub struct Led {
    pub server: ServerId,
    pub term: Term,
}

/// **Ghost.** An entry a leader has committed, and the term it did it in.
///
/// `leader_term` is the term of the **leader that committed it**, not the
/// entry's own term. The two are equal for the newest entry of a commit — that
/// is figure 8's restriction, the guard on [`tr_advance_commit`] — and can
/// differ below it, because a leader that commits its own entry carries
/// everything before it along.
///
/// Recording the entry rather than an index is the point. `Server::commit` is a
/// count, and a count cannot answer the question Leader Completeness asks:
/// *which* entry did a quorum agree on at that index. A count is also lost the
/// moment the log is truncated under it — see
/// [`crate::raft::proofs::log::theorem_a_commit_retreat_means_a_committed_entry_was_deleted`]
/// — whereas this set never shrinks.
pub struct Commit {
    pub leader_term: Term,
    pub index: nat,
    pub entry: Entry,
}

/// The term of the entry before index `i`, or `0` if there is none.
pub open spec fn term_before(log: Seq<Entry>, i: nat) -> Term {
    if i == 0 {
        0
    } else {
        log[i - 1].term
    }
}

/// **What a leader's commit records**: every index it makes committed, with the
/// entry there and the term of the leader doing it.
///
/// A set rather than a length, for the reason [`Commit`] gives.
///
/// # Why this is a recursion and not a comprehension
///
/// The obvious way to write it is `Set::new(|k| k.index < upto && ..)`. In this
/// vstd `Set` is the **finite** set type — `ISet` is the unrestricted one — and
/// `Set::new` accordingly returns `Option<Set<A>>`, `None` when the predicate
/// picks out infinitely many elements. This predicate does not, but saying so
/// would mean discharging finiteness at every use.
///
/// Built up one index at a time it is finite *structurally*, with nothing to
/// discharge: `Set::empty()` and `Set::insert` are total. The price is that
/// membership is no longer syntactic, which is what
/// [`crate::raft::proofs::commit::lemma_committed_by_members`] pays once.
///
/// The `upto > s.log.len()` arm cannot be reached from [`tr_advance_commit`],
/// whose guard bounds `upto` by the log. It skips rather than stopping so that
/// the recursion means the same thing at every `upto` — stopping would make the
/// set jump from empty to full as the recursion descended into range.
pub open spec fn committed_by(s: Server, upto: nat) -> Set<Commit>
    decreases upto,
{
    if upto == 0 {
        Set::empty()
    } else if upto > s.log.len() {
        committed_by(s, (upto - 1) as nat)
    } else {
        committed_by(s, (upto - 1) as nat).insert(
            Commit {
                leader_term: s.current_term,
                index: (upto - 1) as nat,
                entry: s.log[upto - 1],
            },
        )
    }
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
    /// **Ghost: every entry any leader has ever created.**
    ///
    /// History, not state. No server can see this and **no guard reads it** —
    /// [`theorem_history_does_not_gate_the_protocol`] is the proof of that, and
    /// it is what makes this an auxiliary variable rather than an assumption
    /// smuggled into the model. What it buys is the one thing the state alone
    /// cannot say: that nothing was *ever* created at a slot before.
    pub created: Map<Slot, Creation>,
    /// **Ghost: every `(server, term)` in which that server has led.**
    ///
    /// Same discipline, same proof. A server that has led a term has left a
    /// mark that outlives its leadership, and that mark is what rules out a
    /// second leader of the same term creating a second entry at the same
    /// index.
    pub led: Set<Led>,
    /// **Ghost: every entry any leader has ever committed.**
    ///
    /// The third record, and the same discipline as the other two: written at
    /// [`tr_advance_commit`], read by no guard,
    /// [`crate::raft::proofs::history::theorem_history_does_not_gate_the_protocol`]
    /// proving that rather than promising it.
    ///
    /// It exists because commitment is the one thing the state genuinely cannot
    /// say. `Server::commit` is a count on one server, and it *retreats* when a
    /// truncation cuts below it — so after the retreat nothing anywhere records
    /// that the entry was ever committed, and a safety property about committed
    /// entries has nothing to quantify over. This set is what Leader
    /// Completeness and State Machine Safety are statements about.
    pub committed: Set<Commit>,
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

pub open spec fn is_follower(s: Server) -> bool {
    match s.role {
        Role::Follower => true,
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
// Logs
// ---------------------------------------------------------------------------

/// The term of a log's last entry, or 0 for an empty log.
///
/// 0 is safe as the empty case because no entry is ever created at term 0:
/// entries are appended by leaders, and a leader's term is at least 1 because
/// `tr_timeout` is the only way to become a candidate and it increments.
pub open spec fn last_term(log: Seq<Entry>) -> Term {
    if log.len() == 0 {
        0
    } else {
        log[log.len() - 1].term
    }
}

/// **Raft's up-to-date comparison**, and the reason the log restricts elections
/// rather than the other way round.
///
/// A voter refuses a candidate whose log is behind its own: a later last term
/// wins, and at equal last terms the longer log wins. This is what makes
/// Leader Completeness possible at all — without it, a server missing committed
/// entries could be elected and then overwrite them.
pub open spec fn at_least_as_up_to_date(cand_term: Term, cand_len: nat, voter: Seq<Entry>) -> bool {
    ||| cand_term > last_term(voter)
    ||| (cand_term == last_term(voter) && cand_len >= voter.len())
}

/// `s` holds `p`'s first `n` entries.
pub open spec fn has_prefix(s: Seq<Entry>, p: Seq<Entry>, n: nat) -> bool {
    &&& s.len() >= n
    &&& p.len() >= n
    &&& (forall|i: int| #![trigger s[i], p[i]] 0 <= i < n ==> s[i] == p[i])
}

/// The members whose logs hold `log`'s first `n` entries.
///
/// A filter of the membership, for the reason [`voters_for`] is one: a filter is
/// a subset of what it filters by construction, which is the hypothesis
/// quorum intersection needs.
pub open spec fn replicated_on(c: Cluster, log: Seq<Entry>, n: nat) -> Set<ServerId> {
    c.members.filter(
        |s: ServerId| c.servers.contains_key(s) && has_prefix(c.servers[s].log, log, n),
    )
}

/// What a follower's log becomes when it accepts one entry at `prefix`.
///
/// **The suffix is deleted only on a conflict.** Figure 2's rule 3 is *if an
/// existing entry conflicts with a new one (same index, different terms),
/// delete it and all that follow*, and the conditional is the whole of it: an
/// unconditional truncation loses entries to a request that told the follower
/// nothing new, because a duplicate or reordered `AppendEntries` for an earlier
/// index would throw away everything after it.
///
/// So when the entry already there has the leader's term, the log is left
/// alone. That is sound *because of Log Matching* — one `(index, term)` names
/// one entry, so the entry already there is the entry being sent — which makes
/// this the one place in the model where a transition's shape leans on a
/// theorem rather than the other way round. `crate::raft::proofs::history`
/// proves the theorem without using this branch, so the reasoning is not
/// circular; see `lemma_the_consistency_check_preserves_the_record`.
///
/// Otherwise: keep my first `prefix` entries, then the leader's. Written as
/// "keep mine" rather than "copy the leader's first `prefix`", which would bake
/// Log Matching into the transition instead of leaving it to be proved.
pub open spec fn appended_log(follower: Seq<Entry>, leader: Seq<Entry>, prefix: nat) -> Seq<Entry> {
    if prefix < follower.len() && follower[prefix as int].term == leader[prefix as int].term {
        follower
    } else {
        follower.take(prefix as int).push(leader[prefix as int])
    }
}

pub open spec fn min_nat(a: nat, b: nat) -> nat {
    if a <= b {
        a
    } else {
        b
    }
}

pub open spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b {
        a
    } else {
        b
    }
}

/// The commit index a follower ends up with after accepting an entry.
///
/// `min(leaderCommit, index of last new entry)` as figure 2 has it, and then
/// **clamped to the length of the log**.
///
/// # The clamp gives up monotonicity, and that is a choice
///
/// Raft's commit index is supposed to be monotone. This expression is not, and
/// the earlier version of this comment claimed both "never backwards" and
/// "never past the end of the log" — which cannot both hold, because a
/// truncation that cuts *below* the commit point forces one of them to give.
/// A follower with `commit = 5` told to replace the entry at index 0 ends with
/// a one-entry log, and either its commit point still says 5 — naming four
/// entries that no longer exist — or it retreats to 1.
///
/// This model retreats, and the trade is worth stating rather than
/// discovering. A commit point naming absent entries is a state no later
/// reader can make sense of: every query about "what has been applied" reads
/// past the end of the log. A commit point that went backwards is a broken
/// *promise* but a readable state, and the breach is visible.
///
/// # What is actually proved about it
///
/// Not "never backwards", which is false. Instead, in
/// `crate::raft::proofs::log`:
///
/// * [`crate::raft::proofs::log::theorem_the_commit_point_never_outruns_the_log`]
///   — the clamp does what it is for.
/// * `theorem_the_commit_point_does_not_retreat_above_a_truncation` — commit
///   **is** monotone whenever the truncation point is at or above it, which is
///   every step of a healthy cluster.
/// * `theorem_the_commit_point_retreats_only_below_a_truncation` — and when it
///   does retreat, the truncation was strictly below the old commit point.
///
/// So monotonicity holds conditionally, on exactly the condition **Leader
/// Completeness would discharge**: a leader never asks a follower to delete a
/// committed entry, because a committed entry is in every future leader's log.
/// This repository does not prove Leader Completeness, so the model may not
/// treat that case as unreachable — it has to handle it, and the theorems above
/// say precisely how. When Leader Completeness lands, the condition becomes
/// vacuous and monotonicity becomes unconditional; until then it is a
/// hypothesis with a name.
///
/// It is a named function rather than an expression inside [`tr_append_entries`]
/// because the proof of `lemma_append_entries_preserves_inv` has to hand its
/// frame lemma a `Server` that is *exactly* what the transition inserts. Two
/// copies of one rule drift, and did.
pub open spec fn accepted_commit(follower_commit: nat, leader_commit: nat, new_log_len: nat) -> nat {
    min_nat(max_nat(follower_commit, min_nat(leader_commit, new_log_len)), new_log_len)
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
/// protocol's. The `RequestVote` carries the candidate's log summary as it
/// stood *at this moment*, which is what a voter later judges.
pub open spec fn tr_timeout(pre: Cluster, post: Cluster, n: ServerId) -> bool {
    &&& pre.members.contains(n)
    &&& pre.servers.contains_key(n)
    &&& !is_leader(pre.servers[n])
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        n,
        Server {
            role: Role::Candidate,
            current_term: pre.servers[n].current_term + 1,
            log: pre.servers[n].log,
            commit: pre.servers[n].commit,
        },
    )
    &&& post.votes == pre.votes.insert(
        Vote { voter: n, term: pre.servers[n].current_term + 1, candidate: n },
    )
    &&& post.messages == pre.messages.insert(
        RaftMessage::RequestVote {
            term: pre.servers[n].current_term + 1,
            candidate: n,
            last_term: last_term(pre.servers[n].log),
            last_index: pre.servers[n].log.len(),
        },
    )
    &&& post.created == pre.created
    &&& post.led == pre.led
    &&& post.committed == pre.committed
}

/// A member grants its vote for `term` to `cand`.
///
/// Four guards now, and each rules out a different way the protocol could go
/// wrong:
///
/// * a `RequestVote` for that term, candidate and log summary is on the network
///   — a *hint*, and replaying it grants nothing extra because of the next
///   guard;
/// * **`voter` has not already voted in `term`**. One vote per server per term
///   is what makes two quorums contradictory, and it is sentence three of
///   Election Safety;
/// * the request's term is not behind the voter's own;
/// * **the candidate's log is at least as up to date as the voter's**. This one
///   buys nothing for Election Safety and everything for Leader Completeness:
///   it is what stops a server that is missing committed entries from being
///   elected and then overwriting them.
pub open spec fn tr_grant_vote(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
) -> bool {
    &&& pre.members.contains(voter)
    &&& pre.members.contains(cand)
    &&& pre.servers.contains_key(voter)
    &&& pre.messages.contains(
        RaftMessage::RequestVote {
            term: term,
            candidate: cand,
            last_term: cand_last_term,
            last_index: cand_last_index,
        },
    )
    &&& term >= pre.servers[voter].current_term
    &&& !has_voted(pre, voter, term)
    &&& at_least_as_up_to_date(cand_last_term, cand_last_index, pre.servers[voter].log)
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        voter,
        Server {
            role: Role::Follower,
            current_term: term,
            log: pre.servers[voter].log,
            commit: pre.servers[voter].commit,
        },
    )
    &&& post.votes == pre.votes.insert(Vote { voter: voter, term: term, candidate: cand })
    &&& post.messages == pre.messages.insert(
        RaftMessage::VoteGranted { term: term, voter: voter, candidate: cand },
    )
    &&& post.created == pre.created
    &&& post.led == pre.led
    &&& post.committed == pre.committed
}

/// A candidate that has collected a quorum of votes for its own term declares
/// itself leader.
pub open spec fn tr_become_leader(pre: Cluster, post: Cluster, n: ServerId, term: Term) -> bool {
    &&& pre.servers.contains_key(n)
    &&& is_candidate(pre.servers[n])
    &&& pre.servers[n].current_term == term
    &&& won_election(pre, n, term)
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        n,
        Server {
            role: Role::Leader,
            current_term: term,
            log: pre.servers[n].log,
            commit: pre.servers[n].commit,
        },
    )
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages.insert(RaftMessage::Heartbeat { term: term, leader: n })
    &&& post.created == pre.created
    // **The mark that outlives the leadership.** A server that steps down is
    // no longer a leader of this term and nothing in `servers` remembers that
    // it ever was — which is exactly the fact a later `tr_client_request`
    // needs, so it is recorded here rather than reconstructed later.
    &&& post.led == pre.led.insert(Led { server: n, term: term })
    &&& post.committed == pre.committed
}

/// A server learns of a strictly higher term and steps down into it.
///
/// Note what it does *not* do: touch the log. Stepping down changes who you
/// think you are, not what you have recorded.
pub open spec fn tr_step_down(pre: Cluster, post: Cluster, n: ServerId, term: Term) -> bool {
    &&& pre.servers.contains_key(n)
    &&& term > pre.servers[n].current_term
    &&& carries_term(pre, term)
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        n,
        Server {
            role: Role::Follower,
            current_term: term,
            log: pre.servers[n].log,
            commit: pre.servers[n].commit,
        },
    )
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages
    &&& post.created == pre.created
    &&& post.led == pre.led
    &&& post.committed == pre.committed
}

/// A client command reaches the leader, which appends it **at its own term**.
///
/// The term stamped on an entry is the term of the leader that created it, and
/// that is the whole basis of Log Matching: an entry's `(index, term)` pair
/// names the leader that made it, because Election Safety says there was only
/// one leader of that term.
pub open spec fn tr_client_request(pre: Cluster, post: Cluster, n: ServerId, value: nat) -> bool {
    &&& pre.servers.contains_key(n)
    &&& is_leader(pre.servers[n])
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        n,
        Server {
            role: pre.servers[n].role,
            current_term: pre.servers[n].current_term,
            log: pre.servers[n].log.push(
                Entry { term: pre.servers[n].current_term, value: value },
            ),
            commit: pre.servers[n].commit,
        },
    )
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages
    // **The creation record.** Written at the slot the entry lands in, with
    // the term of the entry before it. That second component is what
    // `tr_append_entries`' consistency check preserves, and between them they
    // are what makes two agreeing entries imply two agreeing prefixes.
    //
    // Note there is no guard saying the slot is fresh. A guard would *assume*
    // that a leader never creates twice at one slot, which is the thing to be
    // proved; `crate::raft::proofs::history` proves it instead, and an
    // overwrite here would show up as a broken invariant rather than as a
    // transition that quietly could not fire.
    &&& post.created == pre.created.insert(
        Slot { term: pre.servers[n].current_term, index: pre.servers[n].log.len() },
        Creation {
            value: value,
            prev_term: term_before(pre.servers[n].log, pre.servers[n].log.len()),
        },
    )
    &&& post.led == pre.led
    &&& post.committed == pre.committed
}

/// The leader replicates the entry at `prefix` to a follower.
///
/// The **consistency check** is the guard `follower.log[prefix - 1].term ==
/// leader.log[prefix - 1].term`: the follower accepts an entry only if it
/// already agrees with the leader on the one before it. A follower that
/// accepts truncates whatever it had beyond `prefix` — including, as far as
/// this model is concerned, entries it had already committed. That is faithful
/// Raft and it is deliberately not guarded against here: safety against it
/// comes from the election restriction, which is a theorem, not from a
/// side-condition that assumes the answer.
///
/// Accepting also makes the receiver a follower, which is Raft's rule and what
/// makes Leader Append-Only provable: a leader's log can only be truncated by
/// this transition, and a receiver of it is not a leader afterwards.
pub open spec fn tr_append_entries(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
) -> bool {
    &&& pre.servers.contains_key(leader)
    &&& pre.servers.contains_key(follower)
    &&& leader != follower
    &&& is_leader(pre.servers[leader])
    &&& pre.servers[follower].current_term == pre.servers[leader].current_term
    &&& prefix < pre.servers[leader].log.len()
    &&& prefix <= pre.servers[follower].log.len()
    &&& (prefix > 0 ==> pre.servers[follower].log[prefix - 1].term
        == pre.servers[leader].log[prefix - 1].term)
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        follower,
        Server {
            role: Role::Follower,
            current_term: pre.servers[follower].current_term,
            log: appended_log(pre.servers[follower].log, pre.servers[leader].log, prefix),
            commit: accepted_commit(
                pre.servers[follower].commit,
                pre.servers[leader].commit,
                appended_log(pre.servers[follower].log, pre.servers[leader].log, prefix).len(),
            ),
        },
    )
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages
    &&& post.created == pre.created
    &&& post.led == pre.led
    &&& post.committed == pre.committed
}

/// The leader commits a prefix once a majority holds it.
///
/// **And only if the last entry of that prefix is from the leader's own term.**
/// That restriction is figure 8 of the Raft paper: a leader that committed an
/// older entry on the strength of a majority alone could have that entry
/// overwritten by a later leader, because a majority holding an entry is not
/// the same as a majority having *voted* on it. Counting replicas is not
/// enough; the entry has to belong to the term doing the counting.
pub open spec fn tr_advance_commit(pre: Cluster, post: Cluster, n: ServerId, upto: nat) -> bool {
    &&& pre.servers.contains_key(n)
    &&& is_leader(pre.servers[n])
    &&& upto > pre.servers[n].commit
    &&& upto <= pre.servers[n].log.len()
    &&& pre.servers[n].log[upto - 1].term == pre.servers[n].current_term
    &&& is_quorum(pre, replicated_on(pre, pre.servers[n].log, upto))
    &&& post.members == pre.members
    &&& post.servers == pre.servers.insert(
        n,
        Server {
            role: pre.servers[n].role,
            current_term: pre.servers[n].current_term,
            log: pre.servers[n].log,
            commit: upto,
        },
    )
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages
    &&& post.created == pre.created
    &&& post.led == pre.led
    // **The mark commitment leaves.** The only transition that writes it, and
    // the only one that needs to: `commit` is a count on one server and it can
    // retreat, so without this the fact that a quorum once agreed on an entry
    // is erasable by a later truncation. See `Cluster::committed`.
    &&& post.committed == pre.committed.union(committed_by(pre.servers[n], upto))
}

/// Some message on the network names `term`.
pub open spec fn carries_term(c: Cluster, term: Term) -> bool {
    ||| exists|cand: ServerId, lt: Term, li: nat|
        #[trigger] c.messages.contains(
            RaftMessage::RequestVote {
                term: term,
                candidate: cand,
                last_term: lt,
                last_index: li,
            },
        )
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
    &&& post.created == pre.created
    &&& post.led == pre.led
    &&& post.committed == pre.committed
}

/// Nothing happens (an arbitrary delay).
pub open spec fn tr_stutter(pre: Cluster, post: Cluster) -> bool {
    &&& post.members == pre.members
    &&& post.servers == pre.servers
    &&& post.votes == pre.votes
    &&& post.messages == pre.messages
    &&& post.created == pre.created
    &&& post.led == pre.led
    &&& post.committed == pre.committed
}

/// The labelled transitions.
pub enum RaftStep {
    Timeout { server: ServerId },
    GrantVote {
        voter: ServerId,
        candidate: ServerId,
        term: Term,
        cand_last_term: Term,
        cand_last_index: nat,
    },
    BecomeLeader { server: ServerId, term: Term },
    StepDown { server: ServerId, term: Term },
    ClientRequest { server: ServerId, value: nat },
    AppendEntries { leader: ServerId, follower: ServerId, prefix: nat },
    AdvanceCommit { server: ServerId, upto: nat },
    Replay { msg: RaftMessage },
    Stutter,
}

/// The transition relation, indexed by the step that was taken.
pub open spec fn raft_step(pre: Cluster, post: Cluster, s: RaftStep) -> bool {
    match s {
        RaftStep::Timeout { server } => tr_timeout(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term, cand_last_term, cand_last_index } =>
            tr_grant_vote(pre, post, voter, candidate, term, cand_last_term, cand_last_index),
        RaftStep::BecomeLeader { server, term } => tr_become_leader(pre, post, server, term),
        RaftStep::StepDown { server, term } => tr_step_down(pre, post, server, term),
        RaftStep::ClientRequest { server, value } => tr_client_request(pre, post, server, value),
        RaftStep::AppendEntries { leader, follower, prefix } => tr_append_entries(
            pre,
            post,
            leader,
            follower,
            prefix,
        ),
        RaftStep::AdvanceCommit { server, upto } => tr_advance_commit(pre, post, server, upto),
        RaftStep::Replay { msg } => tr_replay(pre, post, msg),
        RaftStep::Stutter => tr_stutter(pre, post),
    }
}

/// The unlabelled transition relation.
pub open spec fn raft_next(pre: Cluster, post: Cluster) -> bool {
    exists|s: RaftStep| raft_step(pre, post, s)
}

/// Initial states: everybody a follower at term 0 with an empty log, nothing
/// voted, nothing committed, nothing sent.
///
/// **A follower, not merely "not a leader".** This clause used to say
/// `!is_leader`, which admitted a cluster starting with a *candidate* at term 0
/// — a state Raft never starts in (figure 2: *"when servers start up, they
/// begin as followers"*) and one this file's own summary line already ruled
/// out. It also cannot be made sense of: a candidate has, by construction, voted
/// for itself, and an initial state has no votes.
///
/// Tightening it narrows `raft_reachable`, so it is a change to what the
/// reachability theorems quantify over and not a cosmetic one. It narrows it to
/// the states Raft actually has.
pub open spec fn raft_init(c: Cluster) -> bool {
    &&& (forall|n: ServerId| #[trigger] c.members.contains(n) ==> c.servers.contains_key(n))
    &&& (forall|n: ServerId|
        #![trigger c.servers[n]]
        c.servers.contains_key(n) ==> is_follower(c.servers[n]) && c.servers[n].current_term == 0
            && c.servers[n].log.len() == 0 && c.servers[n].commit == 0)
    &&& (forall|v: Vote| !(#[trigger] c.votes.contains(v)))
    &&& (forall|m: RaftMessage| !(#[trigger] c.messages.contains(m)))
    &&& (forall|s: Slot| !(#[trigger] c.created.contains_key(s)))
    &&& (forall|l: Led| !(#[trigger] c.led.contains(l)))
    &&& (forall|k: Commit| !(#[trigger] c.committed.contains(k)))
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

/// A **labelled** finite run: `tr` holds the states and `labels[i]` is the step
/// that takes `tr[i]` to `tr[i + 1]`.
///
/// `raft_execution` quantifies over `raft_next`, which hides *which* step was
/// taken. That is the right notion for a safety theorem — whatever the cluster
/// did, this holds — and the wrong one for a scenario, whose entire content is
/// which steps were taken. See `model::run` for the same distinction and the
/// same reason.
pub open spec fn raft_run(tr: Seq<Cluster>, labels: Seq<RaftStep>) -> bool {
    &&& tr.len() > 0
    &&& labels.len() == tr.len() - 1
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() ==> raft_step(tr[i], tr[i + 1], labels[i]))
}

/// A labelled run that starts at initialisation.
pub open spec fn raft_labelled_execution(tr: Seq<Cluster>, labels: Seq<RaftStep>) -> bool {
    &&& raft_run(tr, labels)
    &&& raft_init(tr[0])
}

/// `c` is reachable if some finite execution ends in it.
pub open spec fn raft_reachable(c: Cluster) -> bool {
    exists|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c
}

} // verus!
