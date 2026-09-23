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
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use distributed_ownership::raft::service::{
    Ballot, Consensus, Durable, Event, MemoryLog, Peer, Persisted, Standing,
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

fn peer(me: u64, log: &MemoryLog) -> Peer {
    Peer::new(roster(), me, Arc::new(log.clone())).expect("the server is on the roster")
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
    assert_eq!(b.request_vote(from(A), term).await.unwrap(), Ballot::Granted(1));
    let leads = a.count_vote(1, term).unwrap();
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
    assert_eq!(c.request_vote(from(A), 1).await.unwrap(), Ballot::Granted(1));
    assert!(a.count_vote(2, 1).unwrap(), "A has its own vote and C's");

    // B now has nowhere to go. C has spent its vote...
    assert_eq!(
        c.request_vote(from(B), 1).await.unwrap(),
        Ballot::Refused(1),
        "a server votes once per term — this is the guard the whole argument rests on"
    );
    // ...and A spent its own on itself.
    assert_eq!(a.request_vote(from(B), 1).await.unwrap(), Ballot::Refused(1));

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
        assert_eq!(c.request_vote(from(A), 1).await.unwrap(), Ballot::Granted(1));
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
        c.request_vote(from(B), 1).await.unwrap(),
        Ballot::Refused(1),
        "the restart must not hand B a vote C already gave A"
    );

    // And the same candidate asking again is answered the same way, because a
    // repeated request is a retransmission rather than a second vote.
    assert_eq!(c.request_vote(from(A), 1).await.unwrap(), Ballot::Granted(1));
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
        assert_eq!(c.request_vote(from(A), 1).await.unwrap(), Ballot::Granted(1));
    }

    // A fresh log, standing in for a server that wrote nothing down.
    let c = peer(2, &MemoryLog::new());
    assert_eq!(c.standing_now().term, 0, "it has forgotten the term as well as the vote");
    assert_eq!(
        c.request_vote(from(B), 1).await.unwrap(),
        Ballot::Granted(1),
        "the same server votes a second time in the same term"
    );

    // Which is not untidy: both candidates now hold two of three.
    let (a, b) = (peer(0, &MemoryLog::new()), peer(1, &MemoryLog::new()));
    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert_eq!(b.stand_for_election().unwrap(), 1);
    assert!(a.count_vote(2, 1).unwrap());
    assert!(b.count_vote(2, 1).unwrap());
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
    assert!(Peer::new(roster(), 7, Arc::new(MemoryLog::new())).is_err());

    let a = peer(0, &MemoryLog::new());
    a.stand_for_election().unwrap();
    let refused = a.count_vote(7, 1).unwrap_err();
    assert_eq!(refused.code(), Some("ERR"), "{refused:?}");

    // And a caller the roster does not know names no server, whatever it claims.
    let stranger = Context::new(
        Some(RemoteAddr::IpAddr(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 9)))),
        None,
    );
    let refused = a.request_vote(stranger, 5).await.unwrap_err();
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
        !a.count_vote(1, 1).unwrap(),
        "a vote for term 1 must not count towards term 2"
    );
    assert!(!a.standing_now().leading);

    // The same voter, voting in the term actually being contested, does count.
    assert!(a.count_vote(1, 2).unwrap());
}
