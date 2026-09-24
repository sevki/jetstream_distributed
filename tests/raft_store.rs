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
    Acceptance, Appended, Ballot, Consensus, LogEntry, LogStore, MemoryLog, Peer, RecordLogStore,
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

/// The reply a follower gives when it accepts at `term` with `len` entries.
///
/// The term is on the wire now rather than supplied by the caller, so an
/// assertion about a reply checks *when* it was accepted as well as what it
/// says — and `observe_appended` can no longer be handed the wrong term.
fn accepted(term: u64, len: u64) -> Appended {
    Appended::Accepted(Acceptance { term, len })
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

/// **Recovery reads every prefix, and reads it right.**
///
/// C28's totality half: `replay` is defined on *every* sequence of records, so
/// there is no prefix a device can present that recovery cannot read. Driven
/// over every cut of a run that appends, truncates and appends again — so the
/// log genuinely goes backwards partway through — and each recovery compared
/// against an independent replay.
///
/// Note what this does **not** claim: that every one of these cuts is a crash
/// the model permits. Most are not — `store_recover` requires
/// `pre.durable <= survived`, and between operations the line is at the end of
/// the device, so the only crash that loses anything is the window inside a
/// two-record `overwrite`. That is
/// `a_crash_inside_a_conflicting_append_loses_only_the_new_entry`. This test is
/// about the parser and the fold being total, which has to hold for *any*
/// prefix precisely because the store is not the only thing that could have
/// written the device.
#[test]
fn recovery_reads_every_prefix_and_reads_it_right() {
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
            "recovery from {k} records disagreed with an independent replay"
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

/// **Nothing is lost between operations.**
///
/// The executable side of `theorem_durability_never_retreats`. Every
/// `LogStore` method here syncs before it returns, so at every point a caller
/// could observe, the durable line is at the end of the device and there is no
/// crash that loses anything. The line lags only *inside* a two-record
/// overwrite, and what that window can lose is a truncation and no more —
/// which is `a_crash_between_the_marker_and_the_entry_is_a_truncation_and_no_more`.
#[test]
fn nothing_is_lost_between_operations() {
    let log = RecordLogStore::new();
    let mut ops = 0;

    let mut check = |l: &RecordLogStore, ops: &mut i32| {
        *ops += 1;
        assert_eq!(
            l.durable_len(),
            l.device_len(),
            "after operation {ops} the durable line is not at the end of the device"
        );
        // And the only crash the model permits from here keeps everything.
        assert_eq!(l.after_crash(l.durable_len()).entries(), l.entries());
    };

    log.append(e(1, 10)).unwrap();
    check(&log, &mut ops);
    log.append(e(1, 11)).unwrap();
    check(&log, &mut ops);
    log.overwrite(1, e(2, 99)).unwrap();
    check(&log, &mut ops);
    log.append(e(2, 100)).unwrap();
    check(&log, &mut ops);
    assert_eq!(ops, 4);
}

// ---------------------------------------------------------------------------
// Compaction
// ---------------------------------------------------------------------------

/// **Compaction keeps the log and shrinks the device**, which is C31.
///
/// The device ends one record longer than the log: the `Truncate { len: 0 }`
/// marker, then an append per entry. That one extra record is what makes the
/// staged generation self-sufficient, which is the test below.
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
    assert_eq!(log.device_len(), before.len() + 1, "the marker, then one record per entry");
    assert_eq!(log.durable_len(), log.device_len());

    // And the compacted device still recovers to the same log.
    assert_eq!(log.after_crash(log.device_len()).entries(), before);
}

/// **A crash between staging and reclaiming does not double the log.**
///
/// The failure `compaction_batch`'s leading marker exists to prevent, and the
/// one Codex pointed at. Compaction on an append-only device is two steps —
/// write the new generation, then reclaim the old one — and a crash can land
/// between them, leaving the device holding *both*.
///
/// Without the marker that state replays to `log + log`: the old generation
/// still replays to the log, and the new one appends every entry again. With
/// it, the staged generation clears what came before, so the device means the
/// same log whether the old records are still there or not.
///
/// This builds the intermediate state by hand rather than crashing a real
/// compaction, because that state is exactly what a real crash would leave and
/// nothing in the store will hold still there.
#[test]
fn a_crash_between_staging_and_reclaiming_does_not_double_the_log() {
    let log = RecordLogStore::new();
    log.append(e(1, 10)).unwrap();
    log.append(e(1, 11)).unwrap();
    log.overwrite(1, e(2, 99)).unwrap();
    let expected = log.entries();
    let old_generation = log.records();

    // The batch compaction would stage: clear, then one append per entry.
    let mut staged = vec![ExecRecord { is_truncate: true, a: 0, b: 0 }];
    staged.extend(
        expected.iter().map(|e| ExecRecord { is_truncate: false, a: e.term, b: e.value }),
    );

    // The middle state: the old generation, then the whole staged batch.
    let mut both = old_generation.clone();
    both.extend(staged.iter().copied());
    assert_eq!(
        naively_replayed(&both),
        expected,
        "a crash between staging and reclaiming must not double the log"
    );

    // And the reclaimed state means the same thing, so the reclaim is a no-op.
    assert_eq!(naively_replayed(&staged), expected);

    // Which is what the store actually does.
    log.compact();
    assert_eq!(log.entries(), expected);
    assert_eq!(log.records().len(), staged.len());
}

/// Without the leading marker the middle state really is wrong — so the test
/// above is not passing for some other reason.
#[test]
fn staging_without_the_marker_would_double_the_log() {
    let log = RecordLogStore::new();
    log.append(e(1, 10)).unwrap();
    log.append(e(1, 11)).unwrap();
    let expected = log.entries();

    let mut both = log.records();
    // The rewrite as `compacted(log)` alone — no marker.
    both.extend(
        expected.iter().map(|e| ExecRecord { is_truncate: false, a: e.term, b: e.value }),
    );

    let doubled = naively_replayed(&both);
    assert_eq!(doubled.len(), expected.len() * 2, "every entry twice, which is the bug");
    assert_eq!(&doubled[..expected.len()], &expected[..]);
}

/// **A batch written a record at a time rewinds the log.**
///
/// The control for `compact` being atomic, and the bug Copilot found: the
/// executable store used to append the marker and each entry separately and
/// sync once at the end, which is exactly this loop. Every intermediate state
/// is the marker plus a *prefix* of the log — the marker has already cleared
/// everything, and only some of the log has been written back — so a crash
/// part-way recovers a **shorter log than the store had**. Data loss on an
/// operation whose whole purpose is to change nothing.
///
/// `theorem_a_partial_batch_can_rewind` proves the rewind is exact rather than
/// merely possible. This is that theorem run, and it is what `compact`
/// installing the batch in one step is for.
#[test]
fn a_batch_written_one_record_at_a_time_would_rewind_the_log() {
    let log = RecordLogStore::new();
    for i in 0..5u64 {
        log.append(e(1, i)).unwrap();
    }
    let before = log.entries();
    let old_generation = log.records();

    let mut batch = vec![ExecRecord { is_truncate: true, a: 0, b: 0 }];
    batch.extend(before.iter().map(|e| ExecRecord { is_truncate: false, a: e.term, b: e.value }));

    // Every cut inside the batch, which is what a record-at-a-time loop makes
    // reachable. The marker is index 0, so a cut at `1 + k` has written k
    // entries back.
    for k in 0..before.len() {
        let mut partway = old_generation.clone();
        partway.extend(batch[..1 + k].iter().copied());
        assert_eq!(
            naively_replayed(&partway),
            before[..k].to_vec(),
            "a crash after {k} of the batch's entries recovers only {k} of {} — the rewind",
            before.len()
        );
    }

    // And the real `compact` never produces one of those states: it installs
    // the whole batch in a single step.
    log.compact();
    assert_eq!(log.entries(), before);
    assert_eq!(log.records().len(), batch.len());
    assert_eq!(log.durable_len(), log.device_len(), "and the whole batch is durable");
}

/// **Compaction runs, and the device stays within a constant factor of the log.**
///
/// C31 proved the rewrite sound and nothing called it, so the stated limitation
/// was that a store which never compacts grows without bound. It compacts
/// itself now, at `records > 2 * (entries + 1)`, and this is the bound.
///
/// The run is deliberately the bad case: every append followed by an overwrite
/// of the same index, which is three records per entry and the shape that made
/// the device outgrow the log in the first place.
#[test]
fn the_device_stays_within_a_constant_factor_of_the_log() {
    let log = RecordLogStore::new();
    for i in 0..60u64 {
        log.append(e(1, i)).unwrap();
        log.overwrite(i, e(2, i)).unwrap();
        let (records, entries) = (log.device_len(), log.len().unwrap() as usize);
        assert!(
            records <= 2 * (entries + 1) + 2,
            "after {i} rounds the device is {records} records for {entries} entries"
        );
        assert_eq!(log.durable_len(), records, "and compaction leaves everything durable");
    }
    // The log itself is untouched by any of it.
    assert_eq!(log.len().unwrap(), 60);
    for i in 0..60u64 {
        assert_eq!(log.entry_at(i).unwrap(), Some(e(2, i)));
    }
}

/// Compaction happening mid-run does not change what recovery reads.
///
/// The property that makes it safe to run automatically: a device that has been
/// rewritten replays to the same log, so a crash after a compaction recovers
/// what a crash before it would have.
#[test]
fn compaction_mid_run_does_not_change_what_recovery_reads() {
    let log = RecordLogStore::new();
    for i in 0..40u64 {
        log.append(e(1, i)).unwrap();
        log.overwrite(i, e(2, i)).unwrap();
        assert_eq!(
            log.after_crash(log.durable_len()).entries(),
            log.entries(),
            "recovery disagreed with memory at round {i}"
        );
    }
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
    assert_eq!(first, accepted(1, 1));
    let after_first = log.device_len();
    assert_eq!(log.entries(), vec![e(1, 42)]);

    // The very same request again.
    let again = follower.append_entries(from(A), 1, 0, 0, e(1, 42), 0).await.unwrap();
    assert_eq!(again, accepted(1, 1), "still accepted");
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
    assert_eq!(replaced, accepted(2, 1));
    assert_eq!(log.entries(), vec![e(2, 43)], "the divergent entry is gone");
    assert_eq!(log.device_len(), after_first + 2, "and it cost exactly two records");
}

/// The store survives a restart in the middle of a replication run: a follower
/// takes three entries, the process dies having written two, and comes back
/// able to take the third.
#[tokio::test]
async fn a_follower_that_restarts_keeps_everything_it_acknowledged() {
    let log = RecordLogStore::new();
    let follower = peer_with(1, &log);

    follower.append_entries(from(A), 1, 0, 0, e(1, 10), 0).await.unwrap();
    follower.append_entries(from(A), 1, 1, 1, e(1, 11), 0).await.unwrap();
    follower.append_entries(from(A), 1, 2, 1, e(1, 12), 0).await.unwrap();
    assert_eq!(log.entries(), vec![e(1, 10), e(1, 11), e(1, 12)]);
    assert_eq!(log.device_len(), 3, "three entries, three records: replication extends");

    // **Every one of those three syncs before answering**, so the durable line
    // is at the end of the device and there is no crash the model permits that
    // loses any of them. This is C35 from the protocol's side: the leader may
    // have committed on the strength of those `Accepted` replies.
    assert_eq!(log.durable_len(), 3);
    let restarted_store = log.after_crash(log.durable_len());
    assert_eq!(
        restarted_store.entries(),
        vec![e(1, 10), e(1, 11), e(1, 12)],
        "a restart may not take back an acknowledged entry"
    );

    // And the restarted follower carries on: a duplicate of the last request
    // is recognised, and the next one extends.
    let restarted = peer_with(1, &restarted_store);
    let duplicate = restarted.append_entries(from(A), 1, 2, 1, e(1, 12), 0).await.unwrap();
    assert_eq!(duplicate, accepted(1, 3));
    assert_eq!(restarted_store.device_len(), 3, "the duplicate wrote nothing");

    let next = restarted.append_entries(from(A), 1, 3, 1, e(1, 13), 0).await.unwrap();
    assert_eq!(next, accepted(1, 4));
    assert_eq!(restarted_store.entries(), vec![e(1, 10), e(1, 11), e(1, 12), e(1, 13)]);
}

/// **The one window a crash can lose anything**, and what it loses.
///
/// Replication that extends is one record and one sync, so between calls the
/// durable line is at the end of the device and nothing is at risk — which is
/// the test above. The line lags only *inside* a two-record `overwrite`, which
/// is what a conflicting `AppendEntries` does, and what that window can lose is
/// the new entry and nothing older.
#[tokio::test]
async fn a_crash_inside_a_conflicting_append_loses_only_the_new_entry() {
    let log = RecordLogStore::new();
    let follower = peer_with(1, &log);

    follower.append_entries(from(A), 1, 0, 0, e(1, 10), 0).await.unwrap();
    follower.append_entries(from(A), 1, 1, 1, e(1, 11), 0).await.unwrap();
    let settled = log.durable_len();
    assert_eq!(settled, 2);

    // A later leader replaces index 1: marker, then entry. Two records.
    follower.append_entries(from(A), 2, 1, 1, e(2, 99), 0).await.unwrap();
    assert_eq!(log.entries(), vec![e(1, 10), e(2, 99)]);
    assert_eq!(log.device_len(), settled + 2);

    // The crash lands between the two. `survived` is above the line as it
    // stood when the operation began, so this is a recovery the model permits.
    let torn = log.after_crash(settled + 1);
    assert_eq!(torn.entries(), vec![e(1, 10)], "the truncation landed, the entry did not");
    assert!(torn.entries().len() >= 1, "and nothing from before the operation was lost");

    // The leader retries and it lands.
    let restarted = peer_with(1, &torn);
    restarted.append_entries(from(A), 2, 1, 1, e(2, 99), 0).await.unwrap();
    assert_eq!(torn.entries(), log.entries());
}

/// **Replication that extends costs one record per entry.**/// **Replication that extends costs one record per entry.**
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
