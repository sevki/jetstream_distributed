//! The durable log, run rather than proved.
//!
//! `raft::proofs::store` proves C27–C31 about a model. These run the executable
//! store — `RecordLogStore`, whose entries are `replay_exec` of a record log
//! that only ever grows — and check the same statements on concrete runs.
//!
//! The one worth reading is
//! `a_crash_at_every_prefix_lands_on_a_log_the_store_had`. C28 says a crash can
//! only rewind; this takes a run that appends, truncates, appends again, and
//! then crashes at **every** record boundary in it, checking each recovery
//! against the log the store actually had at that point. A proof says it for
//! all runs; this says it for one run at every point, which is the kind of
//! evidence that catches an executable layer disagreeing with the model it
//! claims to implement.
//!
//! What these do **not** establish is Log Matching or Leader Completeness,
//! unchanged by anything here.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use distributed_ownership::raft::service::{
    Appended, Ballot, Consensus, LogEntry, LogStore, MemoryLog, Peer, RecordLogStore,
};
use distributed_ownership::raft::store::ExecRecord;
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

fn peer_with(me: u64, log: &RecordLogStore) -> Peer {
    Peer::new(roster(), me, Arc::new(MemoryLog::new()), Arc::new(log.clone()))
        .expect("the server is on the roster")
}

fn e(term: u64, value: u64) -> LogEntry {
    LogEntry { term, value }
}

/// **`replay`, written out by hand.**
///
/// Deliberately a second implementation and not a call into the store's own.
/// Checking `after_crash` against `replay_exec` would be checking the store
/// against itself: any disagreement between the model and the code would
/// cancel out and the test would pass. Three lines, obviously right, and
/// independent.
fn naively_replayed(records: &[ExecRecord]) -> Vec<LogEntry> {
    let mut log: Vec<LogEntry> = Vec::new();
    for r in records {
        if r.is_truncate {
            let keep = (r.a as usize).min(log.len());
            log.truncate(keep);
        } else {
            log.push(LogEntry { term: r.a, value: r.b });
        }
    }
    log
}

// ---------------------------------------------------------------------------
// The device
// ---------------------------------------------------------------------------

/// **An append is one record; an overwrite is two.** C29 and C30, on the
/// device rather than in the model: the log gets shorter and the device does
/// not.
#[test]
fn a_truncation_lengthens_the_device() {
    let log = RecordLogStore::new();
    log.append(e(1, 10)).unwrap();
    log.append(e(1, 11)).unwrap();
    log.append(e(1, 12)).unwrap();
    assert_eq!(log.device_len(), 3, "three appends, three records");
    assert_eq!(log.len().unwrap(), 3);

    // Cut back to one entry and write a different one there. The log loses
    // two entries; the device gains two records.
    log.overwrite(1, e(2, 99)).unwrap();
    assert_eq!(log.entries(), vec![e(1, 10), e(2, 99)], "the tail is gone");
    assert_eq!(log.len().unwrap(), 2, "the log shrank");
    assert_eq!(log.device_len(), 5, "and the device grew, by exactly two");
}

/// **A truncation costs one marker however much it deletes.** The device grows
/// by two for an overwrite that throws away one entry and by two for one that
/// throws away a hundred.
#[test]
fn the_cost_of_a_truncation_does_not_depend_on_what_it_deletes() {
    let small = RecordLogStore::new();
    let large = RecordLogStore::new();
    for i in 0..2u64 {
        small.append(e(1, i)).unwrap();
    }
    for i in 0..100u64 {
        large.append(e(1, i)).unwrap();
    }

    let (before_small, before_large) = (small.device_len(), large.device_len());
    small.overwrite(1, e(2, 7)).unwrap();
    large.overwrite(1, e(2, 7)).unwrap();

    assert_eq!(small.device_len() - before_small, 2);
    assert_eq!(large.device_len() - before_large, 2, "99 entries deleted, still two records");
    assert_eq!(small.entries(), large.entries(), "and the same log either way");
}

// ---------------------------------------------------------------------------
// Crashes
// ---------------------------------------------------------------------------

/// **A crash at every prefix lands on a log the store had.**
///
/// C28, run. The store is driven through a sequence that appends, truncates
/// and appends again — so the log genuinely goes backwards partway through —
/// and after every single record the log is remembered. Then the run is
/// crashed at each of those points in turn, and what recovery produces is
/// compared against what was remembered.
///
/// A store whose in-memory log had drifted from its device would fail this at
/// the first point they disagreed, which is the whole reason it is written
/// over *every* prefix rather than over the end.
#[test]
fn a_crash_at_every_prefix_lands_on_a_log_the_store_had() {
    let log = RecordLogStore::new();

    // A run in which the log genuinely goes backwards partway through, so the
    // prefixes are not simply longer and longer logs.
    log.append(e(1, 10)).unwrap();
    log.append(e(1, 11)).unwrap();
    log.append(e(1, 12)).unwrap();
    log.overwrite(1, e(2, 99)).unwrap();
    log.append(e(2, 100)).unwrap();

    let records = log.records();
    assert_eq!(records.len(), 6, "3 appends + 2 for the overwrite + 1 append");

    for k in 0..=records.len() {
        let recovered = log.after_crash(k);
        assert_eq!(
            recovered.entries(),
            naively_replayed(&records[..k]),
            "a crash after {k} records recovered a log the store never had"
        );
        assert_eq!(recovered.device_len(), k, "and recovery kept exactly what survived");
    }
}

/// The intermediate state of an overwrite is itself a state the store had.
///
/// The one place a crash lands *inside* an operation: the marker is on the
/// device and the entry after it is not. What comes back is the truncated log
/// without the new entry — a log the protocol will simply re-derive when the
/// leader retries, and not a log with a hole in it.
#[test]
fn a_crash_between_the_marker_and_the_entry_is_a_truncation_and_no_more() {
    let log = RecordLogStore::new();
    log.append(e(1, 10)).unwrap();
    log.append(e(1, 11)).unwrap();
    log.overwrite(1, e(2, 99)).unwrap();

    // Records: append, append, truncate, append. Crash after the third.
    let torn = log.after_crash(3);
    assert_eq!(torn.entries(), vec![e(1, 10)], "truncated, and the new entry never landed");

    // And the store carries on from there: the leader retries and it lands.
    torn.overwrite(1, e(2, 99)).unwrap();
    assert_eq!(torn.entries(), log.entries());
}

// ---------------------------------------------------------------------------
// Compaction
// ---------------------------------------------------------------------------

/// **Compaction keeps the log and removes the markers**, which is C31.
#[test]
fn compaction_keeps_the_log_and_shrinks_the_device() {
    let log = RecordLogStore::new();
    for i in 0..5u64 {
        log.append(e(1, i)).unwrap();
        log.overwrite(i, e(2, i)).unwrap();
    }
    let before = log.entries();
    assert!(log.device_len() > before.len(), "markers have accumulated");

    log.compact();
    assert_eq!(log.entries(), before, "the log is unchanged");
    assert_eq!(log.device_len(), before.len(), "one record per entry, no markers");

    // And the compacted device still recovers to the same log — which is what
    // makes the rewrite safe to do before a crash rather than only after one.
    assert_eq!(log.after_crash(log.device_len()).entries(), before);
}

// ---------------------------------------------------------------------------
// The protocol on top
// ---------------------------------------------------------------------------

/// **An `AppendEntries` whose entry is already there writes nothing at all.**
///
/// C29's other branch, and the claim that makes this design cheap rather than
/// merely correct. The follower takes an entry, then the same `AppendEntries`
/// arrives again — a duplicate, which under heartbeats is most of them — and
/// the device does not move.
///
/// This is not an optimisation in the store. It is `Peer::append_entries`'
/// conditional truncation, which is in the protocol because of figure 2's rule
/// 3 and which `raft::proofs::history` needed to prove Log Matching. The check
/// that makes the protocol safe is the check that makes the steady state free.
#[tokio::test]
async fn a_duplicate_append_entries_does_not_touch_the_device() {
    let log = RecordLogStore::new();
    let follower = peer_with(1, &log);

    // Term 1, one entry at index 0.
    let first = follower.append_entries(from(A), 1, 0, 0, e(1, 42), 0).await.unwrap();
    assert_eq!(first, Appended::Accepted(1));
    let after_first = log.device_len();
    assert_eq!(log.entries(), vec![e(1, 42)]);

    // The very same request again.
    let again = follower.append_entries(from(A), 1, 0, 0, e(1, 42), 0).await.unwrap();
    assert_eq!(again, Appended::Accepted(1), "still accepted");
    assert_eq!(log.entries(), vec![e(1, 42)], "and the log is unchanged");
    assert_eq!(log.device_len(), after_first, "the device was not touched");
}

/// And a *conflicting* entry at the same index does reach the device, so the
/// test above is not passing because nothing ever writes.
#[tokio::test]
async fn a_conflicting_append_entries_does_touch_the_device() {
    let log = RecordLogStore::new();
    let follower = peer_with(1, &log);

    follower.append_entries(from(A), 1, 0, 0, e(1, 42), 0).await.unwrap();
    let after_first = log.device_len();

    // Same index, a later leader's term: a genuine conflict.
    let replaced = follower.append_entries(from(A), 2, 0, 0, e(2, 43), 0).await.unwrap();
    assert_eq!(replaced, Appended::Accepted(1));
    assert_eq!(log.entries(), vec![e(2, 43)], "the divergent entry is gone");
    assert_eq!(log.device_len(), after_first + 2, "and it cost exactly two records");
}

/// The store survives a restart in the middle of a replication run: a follower
/// takes three entries, the process dies having written two, and comes back
/// able to take the third.
#[tokio::test]
async fn a_follower_that_restarts_carries_on_from_what_it_wrote() {
    let log = RecordLogStore::new();
    let follower = peer_with(1, &log);

    follower.append_entries(from(A), 1, 0, 0, e(1, 10), 0).await.unwrap();
    follower.append_entries(from(A), 1, 1, 1, e(1, 11), 0).await.unwrap();
    follower.append_entries(from(A), 1, 2, 1, e(1, 12), 0).await.unwrap();
    assert_eq!(log.entries(), vec![e(1, 10), e(1, 11), e(1, 12)]);
    assert_eq!(log.device_len(), 3, "three entries, three records: replication extends");

    // The third record never reached the device.
    let restarted_store = log.after_crash(2);
    assert_eq!(restarted_store.entries(), vec![e(1, 10), e(1, 11)]);

    let restarted = peer_with(1, &restarted_store);
    let retried = restarted.append_entries(from(A), 1, 2, 1, e(1, 12), 0).await.unwrap();
    assert_eq!(retried, Appended::Accepted(3), "the leader retries and it lands");
    assert_eq!(restarted_store.entries(), vec![e(1, 10), e(1, 11), e(1, 12)]);
}

/// **Replication that extends costs one record per entry.**
///
/// The steady state, and the reason the identity marker is not written. A
/// leader nobody is fighting sends entry after entry at the end of the
/// follower's log; each is a single append, not an append and a marker that
/// deletes nothing.
#[tokio::test]
async fn extending_the_log_costs_one_record_per_entry() {
    let log = RecordLogStore::new();
    let follower = peer_with(1, &log);

    for i in 0..10u64 {
        let prev_term = if i == 0 { 0 } else { 1 };
        follower.append_entries(from(A), 1, i, prev_term, e(1, i), 0).await.unwrap();
    }
    assert_eq!(log.len().unwrap(), 10);
    assert_eq!(log.device_len(), 10, "one record per entry, no identity markers");
}

/// The record store is a drop-in for the mock: an election still works against
/// it, which is what makes it usable rather than merely correct.
#[tokio::test]
async fn the_record_store_serves_the_election_too() {
    let log = RecordLogStore::new();
    let a = peer_with(0, &log);
    let term = a.stand_for_election().expect("may stand");
    assert!(a.count_ballot(1, term, Ballot::Granted(term)).expect("a member"), "two of three leads");

    let idx = a.append_command(7).expect("the leader may append");
    assert_eq!(idx, 0);
    assert_eq!(log.entries(), vec![e(term, 7)]);
    assert_eq!(log.device_len(), 1);
}
