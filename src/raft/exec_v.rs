//! A Raft server's election record, executable and verified.
//!
//! [`crate::raft::steps`] decides, from a server's role and term, whether an
//! election step fires. The server also keeps what those decisions are *about*:
//! who it voted for in the term it is in, and — as a candidate — whose votes it
//! has been sent. An [`ElectionCore`] is those together, with one method per
//! election step, and each method's contract says what it does to all of them.
//!
//! # Why the vote and the tally are here
//!
//! `grant_vote_step` takes `already_voted` as an input standing for
//! `has_voted(c, voter, term)`, and `become_leader_step` takes `has_quorum`
//! standing for `won_election(c, n, term)`. Both are facts about records the step
//! cannot see. A server that clears its vote in the wrong place votes twice in
//! one term; one that counts a vote nobody cast elects a leader the cluster never
//! elected — and either is Election Safety gone. These records change in the same
//! methods as the role and the term, under contracts that
//! [`crate::raft::proofs::election_core`] ties to the model.
//!
//! # What is verified
//!
//! * `stand` — `tr_timeout`: the next term, a self-vote, a tally of one.
//! * `grant` — `tr_grant_vote`, and the retransmission of a vote already given.
//! * `count` and the win — `tr_become_leader`: only on a majority of votes that
//!   were each counted once.
//! * `step_down` — `tr_step_down`: a higher term, and the vote and tally cleared
//!   with it.
//! * `yield_to` — the role change `tr_append_entries` makes on a candidate.
//! * A refusal changes nothing.
//!
//! # What is not
//!
//! The log (the up-to-date comparison is an argument), the commit point and the
//! replication progress, the roster, the lock, the audit log, and the **durable
//! store**: `stand`, `grant` and `step_down` take a `persist` closure and move
//! only if it says the term and vote are written down. That it is called
//! *before* the record changes is the code's order, not a proved property.
#![allow(unused_imports)]
#![allow(
    clippy::new_without_default,
    clippy::len_without_is_empty,
    clippy::match_like_matches_macro
)]

use vstd::prelude::*;

use crate::id::{Id, IdSet};
use crate::raft::model::*;
use crate::raft::steps::*;

verus! {

/// What a vote request was answered with.
#[derive(Clone, Copy)]
pub enum VoteOutcome {
    /// The vote is the candidate's: given now, or given before and given again.
    Granted,
    /// It is not.
    Refused,
}

/// Why a step that writes the term down did not happen.
#[derive(Clone, Copy)]
pub enum ElectRefusal {
    /// The protocol declined it.
    Refused(RaftRefusal),
    /// The term and vote could not be made durable, so they were not used.
    Down,
}

/// A server's election record: its role and term, whom it voted for in that
/// term, and — as a candidate — whose votes it has counted.
pub struct ElectionCore {
    /// Role and term.
    pub server: ExecServer,
    /// Whom this server voted for in `server.current_term`, if anyone.
    pub voted_for: Option<Id>,
    /// The votes counted for this server's own candidacy in `server.current_term`.
    pub tally: IdSet,
}

/// Nothing about the core changed.
pub open spec fn same_core(pre: ElectionCore, post: ElectionCore) -> bool {
    &&& post.server.role.view() == pre.server.role.view()
    &&& post.server.current_term == pre.server.current_term
    &&& post.voted_for == pre.voted_for
    &&& post.tally@ == pre.tally@
}

impl ElectionCore {
    /// A follower at `term` that voted for `voted_for` there — what recovery
    /// produces, since there is no durable role.
    pub fn recovered(term: u64, voted_for: Option<Id>) -> (c: ElectionCore)
        ensures
            c.server.role.view() == Role::Follower,
            c.server.current_term == term,
            c.voted_for == voted_for,
            forall|n: Id| !c.tally@.contains(n),
    {
        ElectionCore {
            server: ExecServer { role: ExecRole::Follower, current_term: term },
            voted_for,
            tally: IdSet::new(),
        }
    }

    /// Whether this server leads.
    pub fn leads(&self) -> (r: bool)
        ensures
            r == (self.server.role.view() == Role::Leader),
    {
        match self.server.role {
            ExecRole::Leader => true,
            _ => false,
        }
    }

    /// `tr_timeout`: stand for election in the next term, voting for yourself.
    /// The term and the self-vote go to `persist` together; the server moves only
    /// if they are written down. Returns the term it stands in.
    pub fn stand<F: FnOnce(u64, Option<Id>) -> bool>(&mut self, me: Id, persist: F) -> (r: Result<
        u64,
        ElectRefusal,
    >)
        requires
            forall|t: u64, v: Option<Id>| call_requires(persist, (t, v)),
        ensures
            match r {
                Ok(term) => {
                    &&& timeout_fires(old(self).server.role.view())
                    &&& final(self).server.role.view() == Role::Candidate
                    &&& term as nat == old(self).server.current_term as nat + 1
                    &&& final(self).server.current_term == term
                    &&& final(self).voted_for == Some(me)
                    &&& final(self).tally@ == Set::<Id>::empty().insert(me)
                },
                Err(ElectRefusal::Refused(why)) => {
                    &&& (!timeout_fires(old(self).server.role.view()) || (why is Exhausted))
                    &&& same_core(*old(self), *final(self))
                },
                Err(ElectRefusal::Down) => {
                    &&& timeout_fires(old(self).server.role.view())
                    &&& same_core(*old(self), *final(self))
                },
            },
    {
        /* The term and the self-vote are decided by `timeout_step` and written
         * through `persist` before the record changes, as the service did; the
         * tally restarts at the candidate alone.
         * Origin Rust: let next = match timeout_step(g.server) {..};
         *              self.persist(&mut g, term, Some(self.me))?;
         *              g.server = next;
         *              g.voted_for = Some(self.me);
         *              g.tally = HashSet::new();
         *              g.tally.insert(self.me);
         */
        match timeout_step(self.server) {
            RaftOutcome::Moved(next) => {
                let term = next.current_term;
                if persist(term, Some(me)) {
                    self.server = next;
                    self.voted_for = Some(me);
                    let mut tally = IdSet::new();
                    tally.insert(me);
                    self.tally = tally;
                    Ok(term)
                } else {
                    Err(ElectRefusal::Down)
                }
            },
            RaftOutcome::Refused(why) => Err(ElectRefusal::Refused(why)),
        }
    }

    /// `tr_step_down`: adopt a strictly higher term, as a follower with no vote
    /// and no tally. Returns whether it moved; a term that is not ahead is not a
    /// refusal worth reporting.
    pub fn step_down<F: FnOnce(u64, Option<Id>) -> bool>(&mut self, term: u64, persist: F) -> (r:
        Result<bool, ElectRefusal>)
        requires
            forall|t: u64, v: Option<Id>| call_requires(persist, (t, v)),
        ensures
            match r {
                Ok(true) => {
                    &&& step_down_fires(old(self).server.current_term as nat, term as nat)
                    &&& final(self).server.role.view() == Role::Follower
                    &&& final(self).server.current_term == term
                    &&& final(self).voted_for is None
                    &&& forall|n: Id| !final(self).tally@.contains(n)
                },
                Ok(false) => {
                    &&& !step_down_fires(old(self).server.current_term as nat, term as nat)
                    &&& same_core(*old(self), *final(self))
                },
                Err(_) => {
                    &&& step_down_fires(old(self).server.current_term as nat, term as nat)
                    &&& same_core(*old(self), *final(self))
                },
            },
    {
        /* The vote and the tally leave with the old term, both written down first.
         * Origin Rust: self.persist(g, term, None)?;
         *              g.server = next;
         *              g.voted_for = None;
         *              g.tally = HashSet::new();
         */
        match step_down_step(self.server, term) {
            RaftOutcome::Moved(next) => {
                if persist(term, None) {
                    self.server = next;
                    self.voted_for = None;
                    self.tally = IdSet::new();
                    Ok(true)
                } else {
                    Err(ElectRefusal::Down)
                }
            },
            RaftOutcome::Refused(_) => Ok(false),
        }
    }

    /// The role change `tr_append_entries` makes on a candidate that hears from
    /// the leader of the term it is standing in: it stops standing. The term and
    /// the vote are kept, because a restart must still find that vote. Returns
    /// whether it moved.
    pub fn yield_to(&mut self, term: u64) -> (moved: bool)
        requires
        ensures
            if moved {
                &&& follow_fires(
                    old(self).server.role.view(),
                    old(self).server.current_term as nat,
                    term as nat,
                )
                &&& final(self).server.role.view() == Role::Follower
                &&& final(self).server.current_term == old(self).server.current_term
                &&& final(self).voted_for == old(self).voted_for
                &&& forall|n: Id| !final(self).tally@.contains(n)
            } else {
                &&& !follow_fires(
                    old(self).server.role.view(),
                    old(self).server.current_term as nat,
                    term as nat,
                )
                &&& same_core(*old(self), *final(self))
            },
    {
        /* New executable code: the service's append path moved the role itself; the
         * role change `tr_append_entries` makes on a candidate is now this method.
         * Origin Rust: <none; new executable code>
         */
        match follow_step(self.server, term) {
            RaftOutcome::Moved(next) => {
                self.server = next;
                self.tally = IdSet::new();
                true
            },
            RaftOutcome::Refused(_) => false,
        }
    }

    /// `tr_grant_vote`: answer a request for `candidate`'s election in `term`,
    /// whose log is `up_to_date` against this server's own (the caller compares
    /// the logs). A vote already given to the same candidate in the same term is
    /// given again — a retransmission, not a second vote — and a fresh one goes
    /// to `persist` before the record changes.
    pub fn grant<F: FnOnce(u64, Option<Id>) -> bool>(
        &mut self,
        candidate: Id,
        term: u64,
        up_to_date: bool,
        persist: F,
    ) -> (r: Result<VoteOutcome, ElectRefusal>)
        requires
            forall|t: u64, v: Option<Id>| call_requires(persist, (t, v)),
        ensures
            match r {
                Ok(VoteOutcome::Granted) => {
                    ||| {
                        // A retransmission: the vote was already this candidate's.
                        &&& up_to_date
                        &&& old(self).server.current_term == term
                        &&& old(self).voted_for == Some(candidate)
                        &&& same_core(*old(self), *final(self))
                    }
                    ||| {
                        &&& up_to_date
                        &&& grant_vote_fires(
                            old(self).server.current_term as nat,
                            term as nat,
                            old(self).server.current_term == term && old(self).voted_for is Some,
                        )
                        &&& final(self).server.role.view() == Role::Follower
                        &&& final(self).server.current_term == term
                        &&& final(self).voted_for == Some(candidate)
                        // A candidacy does not outlive its term.
                        &&& (term == old(self).server.current_term ==> final(self).tally@
                            == old(self).tally@)
                        &&& (term != old(self).server.current_term ==> forall|n: Id|
                            !final(self).tally@.contains(n))
                    }
                },
                Ok(VoteOutcome::Refused) => {
                    &&& same_core(*old(self), *final(self))
                    &&& (!up_to_date || !grant_vote_fires(
                        old(self).server.current_term as nat,
                        term as nat,
                        old(self).server.current_term == term && old(self).voted_for is Some,
                    ))
                },
                Err(_) => {
                    &&& up_to_date
                    &&& grant_vote_fires(
                        old(self).server.current_term as nat,
                        term as nat,
                        old(self).server.current_term == term && old(self).voted_for is Some,
                    )
                    &&& same_core(*old(self), *final(self))
                },
            },
    {
        /* Same order as the service: a log that is behind is refused first, a
         * repeat of the vote already given is answered again, and a fresh vote
         * goes through `grant_vote_step` and `persist` before the record changes.
         * Origin Rust: if !up_to_date { return Ok(Ballot::Refused(g.server.current_term)); }
         *              if g.server.current_term == term && g.voted_for == Some(candidate) {
         *                  return Ok(Ballot::Granted(term));
         *              }
         *              let already_voted = g.server.current_term == term && g.voted_for.is_some();
         *              match grant_vote_step(g.server, term, already_voted) {..}
         */
        if !up_to_date {
            return Ok(VoteOutcome::Refused);
        }
        let same_term = self.server.current_term == term;
        if same_term && self.voted_for == Some(candidate) {
            return Ok(VoteOutcome::Granted);
        }
        let already_voted = same_term && self.voted_for.is_some();
        match grant_vote_step(self.server, term, already_voted) {
            RaftOutcome::Moved(next) => {
                if persist(term, Some(candidate)) {
                    let moved_term = next.current_term != self.server.current_term;
                    self.server = next;
                    self.voted_for = Some(candidate);
                    if moved_term {
                        self.tally = IdSet::new();
                    }
                    Ok(VoteOutcome::Granted)
                } else {
                    Err(ElectRefusal::Down)
                }
            },
            RaftOutcome::Refused(_) => Ok(VoteOutcome::Refused),
        }
    }

    /// Count a vote `from` granted for `term`, and take the term if that makes a
    /// majority of `members`. A vote for a term this server has left is not
    /// counted. Returns whether this server now leads — which is not always the
    /// answer to "did this ballot win it": a second ballot after the election was
    /// won changes nothing and the server still leads.
    ///
    /// `counted` says the vote was counted; `won` says it was this ballot that
    /// made the server leader.
    pub fn count(&mut self, from: Id, term: u64, members: u64) -> (r: Counted)
        requires
        ensures
            final(self).voted_for == old(self).voted_for,
            final(self).server.current_term == old(self).server.current_term,
            r.leads == (final(self).server.role.view() == Role::Leader),
            if r.counted {
                &&& old(self).server.current_term == term
                &&& final(self).tally@ == old(self).tally@.insert(from)
            } else {
                &&& final(self).tally@ == old(self).tally@
                &&& final(self).server.role.view() == old(self).server.role.view()
                &&& r.leads == (old(self).server.role.view() == Role::Leader)
            },
            r.won ==> {
                &&& r.counted
                &&& become_leader_fires(
                    old(self).server.role.view(),
                    old(self).server.current_term as nat,
                    term as nat,
                    true,
                )
                &&& final(self).tally@.len() + final(self).tally@.len()
                    > members as nat
                &&& final(self).tally@.len() <= members as nat
                &&& final(self).server.role.view() == Role::Leader
            },
            !r.won && r.counted ==> {
                &&& final(self).tally@.len() + final(self).tally@.len()
                    <= members as nat || final(self).tally@.len() > members as nat
                    || !become_leader_fires(
                    old(self).server.role.view(),
                    old(self).server.current_term as nat,
                    term as nat,
                    true,
                )
            },
    {
        /* A ballot for a term the server has left is not counted; otherwise it is
         * tallied and the term taken if the tally is a majority.
         * Origin Rust: if g.server.current_term != term { return Ok(matches!(g.server.role, ExecRole::Leader)); }
         *              g.tally.insert(from);
         *              let votes = g.tally.len() as u64;
         *              self.take_the_term(&mut g, term, votes, my_len)
         */
        if self.server.current_term != term {
            return Counted { counted: false, won: false, leads: self.leads() };
        }
        self.tally.insert(from);
        let votes = self.tally.len() as u64;
        let has_quorum = votes <= members && is_majority(votes, members);
        match become_leader_step(self.server, term, has_quorum) {
            RaftOutcome::Moved(next) => {
                self.server = next;
                Counted { counted: true, won: true, leads: true }
            },
            RaftOutcome::Refused(_) => Counted { counted: true, won: false, leads: self.leads() },
        }
    }
}

/// What counting a vote did.
#[derive(Clone, Copy)]
pub struct Counted {
    /// The vote was for the term this server is in, and was counted.
    pub counted: bool,
    /// It made the server leader.
    pub won: bool,
    /// The server leads now.
    pub leads: bool,
}

} // verus!
