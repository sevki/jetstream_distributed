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

use crate::host::HostId;
use crate::raft::model::*;
use crate::raft::steps::*;

verus! {

/// The servers whose votes have been counted, each once.
pub struct Tally {
    /// The voters. Each appears at most once.
    pub items: Vec<HostId>,
}

impl Tally {
    /// Each voter appears once.
    pub open spec fn well_formed(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < self.items@.len() && 0 <= j < self.items@.len() && self.items@[i]
                == self.items@[j] ==> i == j
    }

    /// The voters, as the model's set of servers.
    pub open spec fn view_set(&self) -> Set<HostId> {
        self.items@.to_set()
    }
}

/// A voter is in the tally exactly when it is among the items.
pub proof fn lemma_in_tally(items: Seq<HostId>, n: HostId)
    ensures
        items.to_set().contains(n) <==> exists|i: int| 0 <= i < items.len() && items[i] == n,
{
    items.to_set_ensures();
    if exists|i: int| 0 <= i < items.len() && items[i] == n {
        let i = choose|i: int| 0 <= i < items.len() && items[i] == n;
        assert(items[i] == n);
        assert(items.contains(n));
    }
    if items.contains(n) {
        let i = choose|i: int| 0 <= i < items.len() && items[i] == n;
        assert(items[i] == n);
    }
}

/// **A tally's count is its set's size**: each voter counted once.
pub proof fn lemma_tally_len(t: Tally)
    requires
        t.well_formed(),
    ensures
        t.view_set().len() == t.items@.len(),
{
    let m = t.items@;
    assert(m.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() && i != j implies m[i]
            != m[j] by {
            assert(t.items@[i] != t.items@[j]);
        }
    }
    m.unique_seq_to_set();
}

impl Tally {
    /// Nobody.
    pub fn new() -> (t: Tally)
        ensures
            t.well_formed(),
            t.items@.len() == 0,
            forall|n: HostId| !t.view_set().contains(n),
    {
        let t = Tally { items: Vec::new() };
        proof {
            assert forall|n: HostId| !t.view_set().contains(n) by {
                lemma_in_tally(t.items@, n);
            }
        }
        t
    }

    /// Whether `x` has been counted.
    pub fn contains(&self, x: HostId) -> (r: bool)
        ensures
            r == self.view_set().contains(x),
    {
        let mut i: usize = 0;
        while i < self.items.len()
            invariant
                i <= self.items@.len(),
                forall|k: int| 0 <= k < i ==> self.items@[k] != x,
            decreases self.items@.len() - i,
        {
            if self.items[i] == x {
                proof {
                    lemma_in_tally(self.items@, x);
                    assert(self.items@[i as int] == x);
                }
                return true;
            }
            i += 1;
        }
        proof {
            lemma_in_tally(self.items@, x);
            if self.view_set().contains(x) {
                let k = choose|k: int| 0 <= k < self.items@.len() && self.items@[k] == x;
                assert(self.items@[k] == x);
            }
        }
        false
    }

    /// Count `x`'s vote, once.
    pub fn insert(&mut self, x: HostId)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).view_set() == old(self).view_set().insert(x),
    {
        let ghost before = self.items@;
        let present = self.contains(x);
        if !present {
            self.items.push(x);
        }
        proof {
            let after = self.items@;
            lemma_in_tally(before, x);
            if !present {
                assert forall|k: int| 0 <= k < before.len() implies before[k] != x by {
                    if before[k] == x {
                        assert(before[k] == x);
                    }
                }
            }
            assert forall|n: HostId| self.view_set().contains(n) == old(self).view_set().insert(
                x,
            ).contains(n) by {
                lemma_in_tally(before, n);
                lemma_in_tally(after, n);
                if n == x {
                    lemma_in_tally(before, x);
                    if !old(self).view_set().contains(x) {
                        assert(after[after.len() - 1] == x);
                    }
                } else {
                    if self.view_set().contains(n) {
                        let k = choose|k: int| 0 <= k < after.len() && after[k] == n;
                        assert(k < before.len());
                    }
                    if old(self).view_set().contains(n) {
                        let k = choose|k: int| 0 <= k < before.len() && before[k] == n;
                        assert(after[k] == before[k]);
                    }
                }
            }
            assert(self.view_set() == old(self).view_set().insert(x));
            assert forall|i: int, j: int|
                0 <= i < after.len() && 0 <= j < after.len() && after[i] == after[j] implies i
                == j by {
                if after.len() > before.len() {
                    let last = (after.len() - 1) as int;
                    if i == last && j != last {
                        assert(before[j] != x);
                    }
                    if j == last && i != last {
                        assert(before[i] != x);
                    }
                }
            }
        }
    }

    /// How many voters have been counted.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self.items@.len(),
    {
        self.items.len()
    }
}

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
    pub voted_for: Option<HostId>,
    /// The votes counted for this server's own candidacy in `server.current_term`.
    pub tally: Tally,
}

impl ElectionCore {
    /// The core is as it should be: its tally is a set.
    pub open spec fn well_formed(&self) -> bool {
        self.tally.well_formed()
    }
}

/// Nothing about the core changed.
pub open spec fn same_core(pre: ElectionCore, post: ElectionCore) -> bool {
    &&& post.server.role.view() == pre.server.role.view()
    &&& post.server.current_term == pre.server.current_term
    &&& post.voted_for == pre.voted_for
    &&& post.tally.view_set() == pre.tally.view_set()
}

impl ElectionCore {
    /// A follower at `term` that voted for `voted_for` there — what recovery
    /// produces, since there is no durable role.
    pub fn recovered(term: u64, voted_for: Option<HostId>) -> (c: ElectionCore)
        ensures
            c.well_formed(),
            c.server.role.view() == Role::Follower,
            c.server.current_term == term,
            c.voted_for == voted_for,
            forall|n: HostId| !c.tally.view_set().contains(n),
    {
        ElectionCore {
            server: ExecServer { role: ExecRole::Follower, current_term: term },
            voted_for,
            tally: Tally::new(),
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
    pub fn stand<F: FnOnce(u64, Option<HostId>) -> bool>(&mut self, me: HostId, persist: F) -> (r: Result<
        u64,
        ElectRefusal,
    >)
        requires
            old(self).well_formed(),
            forall|t: u64, v: Option<HostId>| call_requires(persist, (t, v)),
        ensures
            final(self).well_formed(),
            match r {
                Ok(term) => {
                    &&& timeout_fires(old(self).server.role.view())
                    &&& final(self).server.role.view() == Role::Candidate
                    &&& term as nat == old(self).server.current_term as nat + 1
                    &&& final(self).server.current_term == term
                    &&& final(self).voted_for == Some(me)
                    &&& final(self).tally.view_set() == Set::<HostId>::empty().insert(me)
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
                    let mut tally = Tally::new();
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
    pub fn step_down<F: FnOnce(u64, Option<HostId>) -> bool>(&mut self, term: u64, persist: F) -> (r:
        Result<bool, ElectRefusal>)
        requires
            old(self).well_formed(),
            forall|t: u64, v: Option<HostId>| call_requires(persist, (t, v)),
        ensures
            final(self).well_formed(),
            match r {
                Ok(true) => {
                    &&& step_down_fires(old(self).server.current_term as nat, term as nat)
                    &&& final(self).server.role.view() == Role::Follower
                    &&& final(self).server.current_term == term
                    &&& final(self).voted_for is None
                    &&& forall|n: HostId| !final(self).tally.view_set().contains(n)
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
                    self.tally = Tally::new();
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
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            if moved {
                &&& follow_fires(
                    old(self).server.role.view(),
                    old(self).server.current_term as nat,
                    term as nat,
                )
                &&& final(self).server.role.view() == Role::Follower
                &&& final(self).server.current_term == old(self).server.current_term
                &&& final(self).voted_for == old(self).voted_for
                &&& forall|n: HostId| !final(self).tally.view_set().contains(n)
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
                self.tally = Tally::new();
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
    pub fn grant<F: FnOnce(u64, Option<HostId>) -> bool>(
        &mut self,
        candidate: HostId,
        term: u64,
        up_to_date: bool,
        persist: F,
    ) -> (r: Result<VoteOutcome, ElectRefusal>)
        requires
            old(self).well_formed(),
            forall|t: u64, v: Option<HostId>| call_requires(persist, (t, v)),
        ensures
            final(self).well_formed(),
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
                        &&& (term == old(self).server.current_term ==> final(self).tally.view_set()
                            == old(self).tally.view_set())
                        &&& (term != old(self).server.current_term ==> forall|n: HostId|
                            !final(self).tally.view_set().contains(n))
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
                        self.tally = Tally::new();
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
    pub fn count(&mut self, from: HostId, term: u64, members: u64) -> (r: Counted)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).voted_for == old(self).voted_for,
            final(self).server.current_term == old(self).server.current_term,
            r.leads == (final(self).server.role.view() == Role::Leader),
            if r.counted {
                &&& old(self).server.current_term == term
                &&& final(self).tally.view_set() == old(self).tally.view_set().insert(from)
            } else {
                &&& final(self).tally.view_set() == old(self).tally.view_set()
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
                &&& final(self).tally.view_set().len() + final(self).tally.view_set().len()
                    > members as nat
                &&& final(self).tally.view_set().len() <= members as nat
                &&& final(self).server.role.view() == Role::Leader
            },
            !r.won && r.counted ==> {
                &&& final(self).tally.view_set().len() + final(self).tally.view_set().len()
                    <= members as nat || final(self).tally.view_set().len() > members as nat
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
        proof {
            lemma_tally_len(self.tally);
        }
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
