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

use jetstream_distributed::host::HostId;
use jetstream_distributed::raft::service::{
    Acceptance, Appended, Ballot, Consensus, LogEntry, LogStore, MemoryLog, MemoryLogStore, Peer, Standing,
};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

const A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));

fn roster() -> HashMap<IpAddr, HostId> {
    HashMap::from([(A, 0), (B, 1), (C, 2)])
}

fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

fn peer_with(me: HostId, log: &MemoryLogStore) -> Peer {
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
        accepted(term, 1)
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

/// Accepting a **conflicting** entry drops whatever the follower had beyond the
/// agreed prefix.
///
/// A follower that appended without truncating would keep entries no leader ever
/// committed — which is why `LogStore` demands `overwrite` and not `append`.
///
/// **The divergence has to be a difference of *term*.** This test used to build
/// the follower's tail as `{term: 1, value: 77}` against the leader's
/// `{term: 1, value: 2}` — same index, same term, different value — and assert
/// that the follower truncated. Figure 2's rule 3 says an entry conflicts when
/// it has the *same index but a different term*, and that rule is sound
/// precisely because of Log Matching: one `(index, term)` names one entry. So
/// the old shape asserted behaviour on a state the protocol cannot reach, and
/// which `raft::proofs::history::theorem_log_matching` now says is impossible.
/// It passed only because the implementation truncated unconditionally, which
/// was the bug.
///
/// So the tail here is from an older term, which is the only kind of divergence
/// there is and the one figure 7 draws.
#[tokio::test]
async fn an_accepted_entry_truncates_a_divergent_tail() {
    let (la, lb) = (MemoryLogStore::new(), MemoryLogStore::new());
    let (a, b) = (peer_with(0, &la), peer_with(1, &lb));

    // A leads term 1 and appends one entry, then loses the term and wins 3.
    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert!(a.count_ballot(1, 1, Ballot::Granted(1)).unwrap());
    a.append_command(1).unwrap();
    assert!(!a.observe_standing(Standing { term: 2, leading: false }).unwrap());
    assert_eq!(a.stand_for_election().unwrap(), 3);
    assert!(a.count_ballot(1, 3, Ballot::Granted(3)).unwrap());
    a.append_command(2).unwrap();
    assert_eq!(la.entries().len(), 2);
    assert_eq!(la.entries()[1].term, 3);

    // The follower agrees on entry 0 and then has two term-1 entries that the
    // leader of term 3 never had.
    lb.append(la.entries()[0]).unwrap();
    lb.append(LogEntry { term: 1, value: 77 }).unwrap();
    lb.append(LogEntry { term: 1, value: 88 }).unwrap();
    assert_eq!(lb.entries().len(), 3);

    assert_eq!(
        b.append_entries(from(A), 3, 1, 1, la.entries()[1], 0).await.unwrap(),
        accepted(3, 2)
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
        accepted(term, 1)
    );
    assert_eq!(
        b.commit(),
        1,
        "a follower cannot commit an entry it does not have, whatever the leader says"
    );
}

// ---------------------------------------------------------------------------
// Six findings from a review, each with the run that shows the defect
// ---------------------------------------------------------------------------

/// **A replayed append does not throw away the entries after it.**
///
/// Figure 2's rule 3 deletes the suffix *only on a conflict*. An unconditional
/// truncation loses entries to a packet that told the follower nothing new: a
/// duplicate of the append for index 0, arriving after index 1 was accepted,
/// would leave the follower one entry shorter than it was.
#[tokio::test]
async fn a_replayed_append_keeps_the_entries_after_it() {
    let store = MemoryLogStore::new();
    let f = peer_with(1, &store);

    let e0 = LogEntry { term: 1, value: 10 };
    let e1 = LogEntry { term: 1, value: 11 };
    assert_eq!(f.append_entries(from(A), 1, 0, 0, e0, 0).await.unwrap(), accepted(1, 1));
    assert_eq!(f.append_entries(from(A), 1, 1, 1, e1, 0).await.unwrap(), accepted(1, 2));

    // The network redelivers the first one.
    assert_eq!(
        f.append_entries(from(A), 1, 0, 0, e0, 0).await.unwrap(),
        accepted(1, 2),
        "the entry at 0 is already there, so nothing is deleted and the reply \
         reports the log the follower really has"
    );
    assert_eq!(store.len().unwrap(), 2, "entry 1 survived the duplicate");
    assert_eq!(store.entry_at(1).unwrap(), Some(e1));
}

/// A genuine conflict still truncates, which is the other half of the rule.
#[tokio::test]
async fn a_conflicting_append_still_drops_the_tail() {
    let store = MemoryLogStore::new();
    let f = peer_with(1, &store);

    assert_eq!(
        f.append_entries(from(A), 1, 0, 0, LogEntry { term: 1, value: 10 }, 0).await.unwrap(),
        accepted(1, 1)
    );
    assert_eq!(
        f.append_entries(from(A), 1, 1, 1, LogEntry { term: 1, value: 11 }, 0).await.unwrap(),
        accepted(1, 2)
    );

    // A later leader overwrites index 1 with an entry of its own term.
    assert_eq!(
        f.append_entries(from(A), 2, 1, 1, LogEntry { term: 2, value: 99 }, 0).await.unwrap(),
        accepted(2, 2)
    );
    assert_eq!(store.entry_at(1).unwrap(), Some(LogEntry { term: 2, value: 99 }));
}

/// **A re-elected leader does not inherit its own past acknowledgements.**
///
/// `matchIndex[]` is volatile leader state and figure 2 says *reinitialized
/// after election*. Carried across a leadership, a peer's recorded length can
/// form a majority on its own and commit an entry at a reused index that the
/// peer has never held.
///
/// The run needs the leader's own log to have *shrunk* while it was away, which
/// is what makes the reused index reachable at all — and a truncation below the
/// commit point is the thing Leader Completeness would forbid and this
/// repository does not yet prove. So this is a test of the bookkeeping being
/// robust rather than of a state known to be reachable, which is the right
/// posture for a rule the paper states and the proof does not yet cover. It
/// doubles as the witness for the commit-point clamp.
#[tokio::test]
async fn a_new_leadership_starts_its_replication_tally_empty() {
    let la = MemoryLogStore::new();
    let a = peer_with(0, &la);

    // Term 1: A leads with three entries and both peers acknowledge all three.
    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert!(a.count_ballot(1, 1, Ballot::Granted(1)).unwrap());
    for v in [7u64, 8, 9] {
        a.append_command(v).unwrap();
    }
    a.record_match(1, 3).unwrap();
    assert_eq!(a.record_match(2, 3).unwrap(), 3);

    // A is deposed by a leader of term 2, which overwrites index 0 — so A's log
    // is one entry long, and its commit point cannot still be 3.
    assert_eq!(
        a.append_entries(from(B), 2, 0, 0, LogEntry { term: 2, value: 50 }, 0).await.unwrap(),
        accepted(2, 1)
    );
    assert_eq!(a.commit(), 1, "the commit point cannot name entries that are gone");

    // A wins term 3 and appends at index 1 — the index the term-1
    // acknowledgements claim both peers already hold.
    assert_eq!(a.stand_for_election().unwrap(), 3);
    assert!(a.count_ballot(1, 3, Ballot::Granted(3)).unwrap());
    assert_eq!(a.append_command(99).unwrap(), 1);

    // Peer 1 says, truthfully, that it holds one entry.
    a.record_match(1, 1).unwrap();
    assert_eq!(
        a.commit(),
        1,
        "with the term-1 lengths carried forward this would be 2 — a term-3 \
         entry committed on the strength of acknowledgements for a log that no \
         longer exists"
    );
}

/// **A reply that crossed a leadership boundary is not counted.**
///
/// An acknowledgement carries a length *and the term it was accepted at*, and
/// the term is what makes this checkable. A length read in a later term would be
/// an acknowledgement of a log the terms in between may have rewritten.
///
/// The term used to be a *caller* argument to `observe_appended`, which put the
/// whole check in the hands of whoever remembered to pass the right number. It
/// is on the wire now, so the case below is one the caller cannot get wrong:
/// the reply says term 1, this server is in term 3, and it is dropped.
#[tokio::test]
async fn an_acknowledgement_from_an_earlier_term_is_dropped() {
    let la = MemoryLogStore::new();
    let a = peer_with(0, &la);

    assert_eq!(a.stand_for_election().unwrap(), 1);
    assert!(a.count_ballot(1, 1, Ballot::Granted(1)).unwrap());
    assert_eq!(a.append_command(7).unwrap(), 0);

    // A hears of a higher term from a reply and steps down, then wins term 3.
    assert!(!a.observe_standing(Standing { term: 2, leading: false }).unwrap());
    assert_eq!(a.stand_for_election().unwrap(), 3);
    assert!(a.count_ballot(1, 3, Ballot::Granted(3)).unwrap());
    assert_eq!(a.append_command(8).unwrap(), 1);

    // A reply to something sent in term 1, arriving now.
    assert_eq!(
        a.observe_appended(1, accepted(1, 2)).unwrap(),
        None,
        "a term-1 acknowledgement says nothing about the term-3 log"
    );
    assert_eq!(a.commit(), 0);

    // The same reply, correctly attributed, does count.
    assert_eq!(a.observe_appended(1, accepted(3, 2)).unwrap(), Some(2));
    assert_eq!(a.commit(), 2);
}

/// **A heartbeat carries the commit point**, because a leader commits only
/// after the acknowledgement that caused it — so the append that did the work
/// carried the *old* commit value, and if no further command arrives the
/// heartbeat is the only thing left to tell the follower.
#[tokio::test]
async fn a_heartbeat_tells_a_follower_what_is_committed() {
    let store = MemoryLogStore::new();
    let f = peer_with(1, &store);

    assert_eq!(
        f.append_entries(from(A), 1, 0, 0, LogEntry { term: 1, value: 7 }, 0).await.unwrap(),
        accepted(1, 1)
    );
    assert_eq!(f.commit(), 0, "the append that carried it was sent before the commit");

    f.heartbeat(from(A), 1, 1).await.unwrap();
    assert_eq!(f.commit(), 1, "and the heartbeat is what says so");
}

/// A cluster of one elects its only member on its own vote.
#[tokio::test]
async fn a_cluster_of_one_elects_itself() {
    let alone = Peer::new(
        HashMap::from([(A, 0)]),
        0,
        Arc::new(MemoryLog::new()),
        Arc::new(MemoryLogStore::new()),
    )
    .expect("on its own roster");

    assert_eq!(alone.stand_for_election().unwrap(), 1);
    assert!(
        alone.standing_now().leading,
        "one vote of one is a majority, and no ballot can ever arrive to say so"
    );
}
