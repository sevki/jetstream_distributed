//! The Raft service: an election, a split vote, and the thing a server has to
//! write down.
//!
//! `raft::proofs::election::theorem_election_safety` says at most one server
//! leads a term, and `scenario_a_leader_is_elected` says elections happen. This
//! is the service exercised against both: a real election that produces exactly
//! one leader, and the durable record without which the service could produce
//! two while the proof went on being true.
//!
//! These drive the `Peer` directly rather than over the wire. Identity still
//! arrives the way the service insists on — a `Context` carrying the caller's
//! address, never an argument naming a server — and what is under test is the
//! election logic, which a simulated network between the caller and the fact
//! would only make harder to read.

use std::collections::HashMap;
use std::io;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use distributed_ownership::raft::service::{
    Ballot, Consensus, Durable, Event, MemoryLog, MemoryLogStore, Peer, Persisted, Standing,
};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

const A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));

fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([(A, 0u64), (B, 1u64), (C, 2u64)])
}

/// A caller, identified the way the service identifies one: by where the
/// connection came from.
fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

/// Every server in this file starts with an empty log, so the up-to-date check
/// is satisfied by `(0, 0)` everywhere and these tests stay about *elections*.
/// `tests/raft_log.rs` is where the log does the deciding.
fn peer(me: u64, log: &MemoryLog) -> Peer {
    Peer::new(roster(), me, Arc::new(log.clone()), Arc::new(MemoryLogStore::new()))
        .expect("the server is on the roster")
}

/// A candidate that persuades one peer leads a cluster of three.
#[tokio::test]
async fn a_candidate_with_two_of_three_leads() {
    let (la, lb, lc) = (MemoryLog::new(), MemoryLog::new(), MemoryLog::new());
    let (a, b, c) = (peer(0, &la), peer(1, &lb), peer(2, &lc));

    let term = a.stand_for_election().unwrap();
    assert_eq!(term, 1, "a fresh server stands for term 1");
    assert!(!a.standing_now().leading, "one vote of three is not a majority");

    // A asks B, which has no reason to refuse.
    assert_eq!(b.request_vote(from(A), term, 0, 0).await.unwrap(), Ballot::Granted(1));
    let leads = a.count_ballot(1, term, Ballot::Granted(term)).unwrap();
    assert!(leads, "two of three is a majority");
    assert_eq!(a.standing_now(), Standing { term: 1, leading: true });

    // C never voted and is still at term 0 — a leader does not need the last
    // vote, which is the whole point of a majority.
    assert_eq!(c.standing_now().term, 0);
    assert!(a.log().contains(&Event::Led { term: 1, votes: 2 }), "{:?}", a.log());
}

/// **Two candidates in one term, and only one of them can win.**
///
/// The service's version of Election Safety. Both A and B stand for term 1 and
/// each votes for itself; C has one vote to give and gives it to whoever asks
/// first. The loser is not merely slower — it is *refused*, by A which spent
/// its vote on itself and by C which spent its vote on A.
#[tokio::test]
async fn two_candidates_cannot_both_win_a_term() {
    let (la, lb, lc) = (MemoryLog::new(), MemoryLog::new(), MemoryLog::new());
    let (a, b, c) = (peer(0, &la), peer(1, &lb), peer(2, &lc));

    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert_eq!(b.stand_for_election().unwrap(), 1);

    // A gets to C first.
    assert_eq!(c.request_vote(from(A), 1, 0, 0).await.unwrap(), Ballot::Granted(1));
    assert!(a.count_ballot(2, 1, Ballot::Granted(1)).unwrap(), "A has its own vote and C's");

    // B now has nowhere to go. C has spent its vote...
    assert_eq!(
        c.request_vote(from(B), 1, 0, 0).await.unwrap(),
        Ballot::Refused(1),
        "a server votes once per term — this is the guard the whole argument rests on"
    );
    // ...and A spent its own on itself.
    assert_eq!(a.request_vote(from(B), 1, 0, 0).await.unwrap(), Ballot::Refused(1));

    assert!(a.standing_now().leading);
    assert!(
        !b.standing_now().leading,
        "two leaders in one term is what `theorem_election_safety` rules out"
    );
}

/// A voter that restarts does not vote twice in the same term.
///
/// Raft's figure 2 requires `currentTerm` and `votedFor` on stable storage
/// *before responding to RPCs*, and this is why: the vote is the only thing
/// standing between two candidates and two majorities.
#[tokio::test]
async fn a_restarted_voter_does_not_vote_twice() {
    let lc = MemoryLog::new();

    {
        let c = peer(2, &lc);
        assert_eq!(c.request_vote(from(A), 1, 0, 0).await.unwrap(), Ballot::Granted(1));
    }
    assert_eq!(
        lc.load().unwrap(),
        Persisted { current_term: 1, voted_for: Some(0) },
        "the vote is on stable storage, not only in the server's head"
    );

    // Everything the server knew is gone except the record.
    let c = peer(2, &lc);
    assert_eq!(c.standing_now().term, 1, "a recovered server resumes its term");
    assert_eq!(
        c.request_vote(from(B), 1, 0, 0).await.unwrap(),
        Ballot::Refused(1),
        "the restart must not hand B a vote C already gave A"
    );

    // And the same candidate asking again is answered the same way, because a
    // repeated request is a retransmission rather than a second vote.
    assert_eq!(c.request_vote(from(A), 1, 0, 0).await.unwrap(), Ballot::Granted(1));
}

/// The same run against a voter that forgot, so the defect is on the record
/// rather than only its absence.
///
/// Every assertion here states something the protocol forbids, and the test
/// passes because a server without stable storage really does it. Without this,
/// the test above passes for two indistinguishable reasons.
#[tokio::test]
async fn a_forgetful_voter_votes_twice_and_elects_two_leaders() {
    {
        let c = peer(2, &MemoryLog::new());
        assert_eq!(c.request_vote(from(A), 1, 0, 0).await.unwrap(), Ballot::Granted(1));
    }

    // A fresh log, standing in for a server that wrote nothing down.
    let c = peer(2, &MemoryLog::new());
    assert_eq!(c.standing_now().term, 0, "it has forgotten the term as well as the vote");
    assert_eq!(
        c.request_vote(from(B), 1, 0, 0).await.unwrap(),
        Ballot::Granted(1),
        "the same server votes a second time in the same term"
    );

    // Which is not untidy: both candidates now hold two of three.
    let (a, b) = (peer(0, &MemoryLog::new()), peer(1, &MemoryLog::new()));
    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert_eq!(b.stand_for_election().unwrap(), 1);
    assert!(a.count_ballot(2, 1, Ballot::Granted(1)).unwrap());
    assert!(b.count_ballot(2, 1, Ballot::Granted(1)).unwrap());
    assert!(
        a.standing_now().leading && b.standing_now().leading,
        "two leaders in term 1 — the state `theorem_election_safety` says is \
         unreachable, reached by a server that forgot its vote"
    );
}

/// A server cannot be started claiming to be somebody who is not in the
/// cluster, and a vote cannot be counted from one.
#[tokio::test]
async fn strangers_are_not_servers() {
    assert!(Peer::new(roster(), 7, Arc::new(MemoryLog::new()), Arc::new(MemoryLogStore::new()))
            .is_err());

    let a = peer(0, &MemoryLog::new());
    a.stand_for_election().unwrap();
    let refused = a.count_ballot(7, 1, Ballot::Granted(1)).unwrap_err();
    assert_eq!(refused.code(), Some("ERR"), "{refused:?}");

    // And a caller the roster does not know names no server, whatever it claims.
    let stranger = Context::new(
        Some(RemoteAddr::IpAddr(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 9)))),
        None,
    );
    let refused = a.request_vote(stranger, 5, 0, 0).await.unwrap_err();
    assert_eq!(refused.code(), Some("NO"), "{refused:?}");
}

/// A stale vote does not elect anybody.
///
/// A reply delayed past a new election names a term the candidate has left.
/// Counting it would let a ballot cast for term 1 buy term 2, which is the
/// same class of mistake as a stale epoch buying a write.
#[tokio::test]
async fn a_vote_for_a_term_the_candidate_has_left_is_not_counted() {
    let a = peer(0, &MemoryLog::new());
    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert_eq!(a.stand_for_election().unwrap(), 2, "standing again burns a term");

    assert!(
        !a.count_ballot(1, 1, Ballot::Granted(1)).unwrap(),
        "a vote for term 1 must not count towards term 2"
    );
    assert!(!a.standing_now().leading);

    // The same voter, voting in the term actually being contested, does count.
    assert!(a.count_ballot(1, 2, Ballot::Granted(2)).unwrap());
}

/// **A refusal is not a vote, and a caller cannot make it one.**
///
/// The tally is what `become_leader_step`'s `has_quorum` argument comes from,
/// and `has_quorum == won_election` is the coupling the refinement proof names.
/// A method that took a server number and a term would let a candidate count a
/// peer that said no — a majority assembled out of nothing, and a leader the
/// model never elected. So the ballot itself is the argument.
#[tokio::test]
async fn a_refused_ballot_is_not_a_vote() {
    let (la, lb) = (MemoryLog::new(), MemoryLog::new());
    let (a, b) = (peer(0, &la), peer(1, &lb));

    // B stands first and spends its vote on itself, so it refuses A.
    assert_eq!(b.stand_for_election().unwrap(), 1);
    assert_eq!(a.stand_for_election().unwrap(), 1);
    let ballot = b.request_vote(from(A), 1, 0, 0).await.unwrap();
    assert_eq!(ballot, Ballot::Refused(1));

    assert!(!a.count_ballot(1, 1, ballot).unwrap(), "a refusal counts for nothing");
    assert!(!a.standing_now().leading, "one vote of three is not a majority");

    // And the tally did not quietly grow: the only way it could have is the
    // ballot A actually received.
    assert!(
        !a.log().iter().any(|e| matches!(e, Event::Counted { from: 1, .. })),
        "{:?}",
        a.log()
    );
}

/// A ballot granted for some other term is refused outright.
///
/// Distinguished from the stale-reply case above on purpose. There the ballot
/// was honest and late; here the term it was granted for is not the term the
/// caller says it is counting towards, which is a caller that has lost track of
/// its own candidacy rather than a network that was slow.
#[tokio::test]
async fn a_ballot_for_another_term_is_refused() {
    let a = peer(0, &MemoryLog::new());
    assert_eq!(a.stand_for_election().unwrap(), 1);

    let refused = a.count_ballot(1, 1, Ballot::Granted(2)).unwrap_err();
    assert_eq!(refused.code(), Some("NO"), "{refused:?}");
    assert!(!a.standing_now().leading);
}

/// **A candidate learns from a refusal that it has already lost.**
///
/// Raft's term rule is about responses as well as requests. Without a path for
/// one, a candidate refused by a peer at a higher term would go on standing in
/// a term nobody will vote in — and would have to wait for an unrelated inbound
/// request to find out, which on a quiet network may be a long time.
#[tokio::test]
async fn a_candidate_adopts_a_term_a_refusal_carried() {
    let (la, lb) = (MemoryLog::new(), MemoryLog::new());
    let (a, b) = (peer(0, &la), peer(1, &lb));

    // B is far ahead.
    for _ in 0..4 {
        b.stand_for_election().unwrap();
    }
    assert_eq!(b.standing_now().term, 4);

    assert_eq!(a.stand_for_election().unwrap(), 1);
    let ballot = b.request_vote(from(A), 1, 0, 0).await.unwrap();
    assert_eq!(ballot, Ballot::Refused(4), "B tells A what term it is really in");

    assert!(!a.count_ballot(1, 1, ballot).unwrap());
    assert_eq!(
        a.standing_now(),
        Standing { term: 4, leading: false },
        "a refusal carrying a higher term deposes the candidate that read it"
    );
    // And durably, because it is a term change like any other.
    assert_eq!(la.load().unwrap(), Persisted { current_term: 4, voted_for: None });
}

/// A leader that reconnects finds out from its own heartbeat replies.
///
/// The same rule from the other end, and the case a partitioned leader is in:
/// it believes it leads, the cluster has moved on, and the only news reaching
/// it is the answers to the heartbeats it keeps sending.
#[tokio::test]
async fn a_stale_leader_steps_down_on_the_reply_to_its_own_heartbeat() {
    let (la, lb) = (MemoryLog::new(), MemoryLog::new());
    let (a, b) = (peer(0, &la), peer(1, &lb));

    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert!(a.count_ballot(1, 1, Ballot::Granted(1)).unwrap());
    assert!(a.standing_now().leading);

    // While A was away, B took term 3.
    for _ in 0..3 {
        b.stand_for_election().unwrap();
    }
    let seen = b.heartbeat(from(A), 1).await.unwrap();
    assert_eq!(seen, Standing { term: 3, leading: false }, "B is a candidate at 3");

    assert!(!a.observe_standing(seen).unwrap(), "A is not the leader any more");
    assert_eq!(a.standing_now(), Standing { term: 3, leading: false });
    assert_eq!(la.load().unwrap(), Persisted { current_term: 3, voted_for: None });
}

/// **A split vote's loser stops standing when it hears the winner.**
///
/// Figure 2's rule for candidates: *"if AppendEntries RPC received from new
/// leader: convert to follower"*. The term is *equal*, so `step_down_to` cannot
/// see it — and a candidate that kept standing would keep timing out into terms
/// nobody needed, turning one split vote into a sequence of them.
#[tokio::test]
async fn a_candidate_yields_to_the_winner_of_its_own_term() {
    let (la, lb) = (MemoryLog::new(), MemoryLog::new());
    let (a, b) = (peer(0, &la), peer(1, &lb));

    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert_eq!(b.stand_for_election().unwrap(), 1, "a split vote: both stand at 1");

    // A wins term 1 elsewhere and heartbeats B.
    let seen = b.heartbeat(from(A), 1).await.unwrap();
    assert_eq!(seen, Standing { term: 1, leading: false });
    assert!(
        b.log().contains(&Event::SteppedDown { from_term: 1, to_term: 1 }),
        "{:?}",
        b.log()
    );

    // **The vote is kept**, because the term did not move and B really did vote
    // in term 1. A restart must still find it, or B votes twice in one term.
    assert_eq!(lb.load().unwrap(), Persisted { current_term: 1, voted_for: Some(1) });
    assert_eq!(
        b.request_vote(from(C), 1, 0, 0).await.unwrap(),
        Ballot::Refused(1),
        "yielding is not un-voting"
    );
}

/// A leader is not unseated by a peer naming its term.
///
/// The asymmetry `steps::follow_fires` documents. Two leaders in one term is
/// the state Election Safety rules out, so an equal-term heartbeat reaching a
/// leader is a case the model cannot reach — and a server that demoted itself
/// on one would let any peer on the roster depose it by claiming a term it
/// already knows.
#[tokio::test]
async fn a_leader_is_not_deposed_by_its_own_term() {
    let la = MemoryLog::new();
    let a = peer(0, &la);
    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert!(a.count_ballot(1, 1, Ballot::Granted(1)).unwrap());

    let seen = a.heartbeat(from(B), 1).await.unwrap();
    assert_eq!(seen, Standing { term: 1, leading: true }, "still the leader of term 1");
}

/// Storage whose `save` installs the value and *then* fails, once.
///
/// Not a contrived failure: it is the shape [`Durable`]'s docs describe and the
/// one a `write, rename, fsync-the-directory` sequence actually has. The rename
/// makes the value visible to every later `load`; only the last step, the one
/// that makes it survive a crash, can still fail — and by then the caller's
/// error says nothing about whether the value is there.
#[derive(Clone)]
struct InstallsThenFails {
    held: Arc<Mutex<Persisted>>,
    fail_next: Arc<AtomicBool>,
}

impl InstallsThenFails {
    fn new() -> Self {
        InstallsThenFails {
            held: Arc::new(Mutex::new(Persisted::default())),
            fail_next: Arc::new(AtomicBool::new(false)),
        }
    }
}

impl Durable for InstallsThenFails {
    fn load(&self) -> io::Result<Persisted> {
        Ok(*self.held.lock().expect("store lock"))
    }

    fn save(&self, state: Persisted) -> io::Result<()> {
        *self.held.lock().expect("store lock") = state;
        if self.fail_next.swap(false, Ordering::SeqCst) {
            return Err(io::Error::other("the directory sync failed after the rename"));
        }
        Ok(())
    }
}

/// **A failed `save` is not a `save` that did not happen.**
///
/// The server refuses, which is right — it must not act on a decision it could
/// not write down. What it must *also* not do is go on believing the store
/// still holds the old record, because it does not: a later write would then
/// take the durable term backwards past one a restart would have found. So the
/// store is asked what it really holds, and whatever is ahead is adopted.
#[tokio::test]
async fn a_persist_that_failed_after_installing_is_not_ignored() {
    let store = InstallsThenFails::new();
    let a = Peer::new(roster(), 0, Arc::new(store.clone()), Arc::new(MemoryLogStore::new()))
        .expect("on the roster");

    store.fail_next.store(true, Ordering::SeqCst);
    let refused = a.stand_for_election().unwrap_err();
    assert_eq!(refused.code(), Some("DOWN"), "{refused:?}");

    // The candidacy did not happen: the server is a follower, because a term it
    // did not reach under its own power is not one it can be standing in.
    assert_eq!(
        a.standing_now(),
        Standing { term: 1, leading: false },
        "the term on disk is adopted, the candidacy is not"
    );
    assert_eq!(
        store.load().unwrap(),
        Persisted { current_term: 1, voted_for: Some(0) },
        "the write landed; only the sync failed"
    );

    // And the self-vote on disk is honoured rather than written over. A server
    // that had stayed at term 0 would grant this one.
    assert_eq!(
        a.request_vote(from(B), 1, 0, 0).await.unwrap(),
        Ballot::Refused(1),
        "term 1's vote is spent, and the record saying so was not overtaken"
    );
}
