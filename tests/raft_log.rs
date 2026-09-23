//! The log: replication, the consistency check, truncation, the up-to-date
//! comparison, and the commit rule figure 8 of the Raft paper exists for.
//!
//! The log is a **trait** (`LogStore`) and these run against the in-memory
//! mock. That is the point of the trait: a real log is a file with a format, an
//! fsync policy and a truncation story, and none of that belongs in the
//! protocol — while the protocol's own behaviour is exactly what you want to
//! exercise without a disk in the way.
//!
//! What these tests do **not** do is establish Log Matching or Leader
//! Completeness. Those are properties of every reachable run, not of the half
//! dozen written out here, and `raft::proofs::log` says plainly that they are
//! not proved. A passing test file is not a substitute and is not offered as
//! one.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use distributed_ownership::raft::service::{
    Appended, Ballot, Consensus, LogEntry, LogStore, MemoryLog, MemoryLogStore, Peer,
};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

const A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));

fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([(A, 0u64), (B, 1u64), (C, 2u64)])
}

fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

fn peer_with(me: u64, log: &MemoryLogStore) -> Peer {
    Peer::new(roster(), me, Arc::new(MemoryLog::new()), Arc::new(log.clone()))
        .expect("the server is on the roster")
}

/// Make `p` the leader of term 1 in a three-server cluster.
fn make_leader(p: &Peer) -> u64 {
    let term = p.stand_for_election().expect("may stand");
    assert!(
        p.count_ballot(1, term, Ballot::Granted(term)).expect("node 1 is a member"),
        "two of three leads"
    );
    term
}

/// A leader appends, a follower takes it, and the two logs agree.
#[tokio::test]
async fn a_follower_takes_the_leaders_entry() {
    let (la, lb) = (MemoryLogStore::new(), MemoryLogStore::new());
    let (a, b) = (peer_with(0, &la), peer_with(1, &lb));
    let term = make_leader(&a);

    let idx = a.append_command(42).expect("the leader may append");
    assert_eq!(idx, 0);
    let entry = la.entries()[0];
    assert_eq!(entry.term, term, "an entry carries the term of the leader that made it");

    // `prefix` 0: the follower is asked to agree on nothing before this entry.
    assert_eq!(
        b.append_entries(from(A), term, 0, 0, entry, 0).await.unwrap(),
        Appended::Accepted(1)
    );
    assert_eq!(lb.entries(), la.entries(), "the follower's entry is the leader's");
}

/// A follower refuses an entry it cannot place.
///
/// The consistency check, both ways it can fail: a `prefix` past the end of the
/// follower's log, and a `prev_term` that does not match what the follower has.
#[tokio::test]
async fn a_follower_refuses_an_entry_it_cannot_place() {
    let (la, lb) = (MemoryLogStore::new(), MemoryLogStore::new());
    let (a, b) = (peer_with(0, &la), peer_with(1, &lb));
    let term = make_leader(&a);
    a.append_command(1).unwrap();
    a.append_command(2).unwrap();

    // The follower has nothing, so it cannot agree on one entry already.
    assert_eq!(
        b.append_entries(from(A), term, 1, term, la.entries()[1], 0).await.unwrap(),
        Appended::Rejected(term),
        "a prefix past the end of the follower's log has nothing to check against"
    );
    assert!(lb.entries().is_empty(), "a refused entry is not written");

    // Give it a first entry from a *different* term, then ask it to extend.
    lb.append(LogEntry { term: 99, value: 7 }).unwrap();
    assert_eq!(
        b.append_entries(from(A), term, 1, term, la.entries()[1], 0).await.unwrap(),
        Appended::Rejected(term),
        "the entry before the one being sent must have the term the leader says"
    );
}

/// Accepting an entry drops whatever the follower had beyond the agreed prefix.
///
/// A follower that appended without truncating would keep entries no leader
/// ever committed — which is the whole reason `overwrite` and not `append` is
/// what `LogStore` demands here.
#[tokio::test]
async fn an_accepted_entry_truncates_a_divergent_tail() {
    let (la, lb) = (MemoryLogStore::new(), MemoryLogStore::new());
    let (a, b) = (peer_with(0, &la), peer_with(1, &lb));
    let term = make_leader(&a);
    a.append_command(1).unwrap();
    a.append_command(2).unwrap();

    // The follower agrees on entry 0 and then has two entries of its own that
    // the leader never had.
    lb.append(la.entries()[0]).unwrap();
    lb.append(LogEntry { term: 1, value: 77 }).unwrap();
    lb.append(LogEntry { term: 1, value: 88 }).unwrap();
    assert_eq!(lb.entries().len(), 3);

    assert_eq!(
        b.append_entries(from(A), term, 1, term, la.entries()[1], 0).await.unwrap(),
        Appended::Accepted(2)
    );
    assert_eq!(lb.entries(), la.entries(), "the divergent tail is gone, not appended past");
}

/// **A candidate whose log is behind is refused.**
///
/// The up-to-date check, and the guard that exists for the log rather than for
/// the election: without it a server missing entries could be elected and then
/// overwrite them. Both halves of the comparison are exercised — a shorter log
/// at the same last term, and an older last term however long the log.
#[tokio::test]
async fn a_candidate_whose_log_is_behind_is_refused() {
    let lv = MemoryLogStore::new();
    let voter = peer_with(2, &lv);
    lv.append(LogEntry { term: 2, value: 1 }).unwrap();
    lv.append(LogEntry { term: 2, value: 2 }).unwrap();

    // Same last term, shorter log.
    assert_eq!(
        voter.request_vote(from(A), 3, 2, 1).await.unwrap(),
        Ballot::Refused(3),
        "a shorter log at the same last term is behind"
    );

    // Older last term, longer log — length does not rescue it.
    assert_eq!(
        voter.request_vote(from(A), 4, 1, 9).await.unwrap(),
        Ballot::Refused(4),
        "a later last term wins outright; length is only the tie-break"
    );

    // Equal is good enough, which is what lets a whole cluster vote for a peer
    // that is merely not behind.
    assert_eq!(voter.request_vote(from(B), 5, 2, 2).await.unwrap(), Ballot::Granted(5));
}

/// **Commitment needs a majority *and* an entry of the leader's own term.**
///
/// Figure 8 of the Raft paper. A majority *holding* an entry is not a majority
/// having *voted* on it, so a leader that committed an older entry on replica
/// count alone could have it overwritten by a later leader. The resolution is
/// that the old entry becomes committed indirectly, once an entry of the
/// current term above it is.
#[tokio::test]
async fn an_old_entry_is_committed_only_under_one_of_the_leaders_own() {
    let la = MemoryLogStore::new();
    // An entry left over from term 1.
    la.append(LogEntry { term: 1, value: 5 }).unwrap();

    let a = peer_with(0, &la);
    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert_eq!(a.stand_for_election().unwrap(), 2, "standing again burns a term");
    assert!(a.count_ballot(1, 2, Ballot::Granted(2)).unwrap(), "two of three leads term 2");

    // Everyone holds the term-1 entry. That is a majority, and it is not
    // enough.
    assert_eq!(a.record_match(1, 1).unwrap(), 0);
    assert_eq!(
        a.record_match(2, 1).unwrap(),
        0,
        "a majority holding an entry from an earlier term does not commit it"
    );
    assert_eq!(a.commit(), 0);

    // The leader appends one of its own and gets a majority for *that*.
    a.append_command(6).unwrap();
    assert_eq!(a.record_match(1, 2).unwrap(), 2);
    assert_eq!(
        a.commit(),
        2,
        "committing the current-term entry commits everything under it, which is \
         how the term-1 entry becomes safe"
    );
}

/// A follower learns the commit point from the leader, bounded by what it
/// actually has.
#[tokio::test]
async fn a_follower_commits_no_further_than_its_own_log() {
    let (la, lb) = (MemoryLogStore::new(), MemoryLogStore::new());
    let (a, b) = (peer_with(0, &la), peer_with(1, &lb));
    let term = make_leader(&a);
    a.append_command(1).unwrap();
    a.append_command(2).unwrap();

    // The leader claims two entries are committed while sending only the first.
    assert_eq!(
        b.append_entries(from(A), term, 0, 0, la.entries()[0], 2).await.unwrap(),
        Appended::Accepted(1)
    );
    assert_eq!(
        b.commit(),
        1,
        "a follower cannot commit an entry it does not have, whatever the leader says"
    );
}
