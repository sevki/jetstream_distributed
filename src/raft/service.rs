//! Raft, as a Jetstream service.
//!
//! [`crate::ownership::service`] serves a protocol whose exclusivity is
//! *assumed*: the ownership model's registry is updated atomically, which rules
//! out two coordinators by construction, and the Reference's failure-model table
//! says a real deployment has to buy that from consensus. This is the service
//! that starts buying it.
//!
//! Every decision this server makes about its own record goes through a step
//! function in [`crate::raft::steps`], each proved in
//! `crate::raft::proofs::refinement` to agree with the model's transition — and
//! the model's `theorem_election_safety` says at most one server leads a term.
//!
//! # Identity comes from the connection, again
//!
//! No method takes a server number. **The candidate asking for a vote is
//! whoever opened the connection**, not whoever the frame says. This is the
//! same design as the ownership service and it matters more here: a protocol
//! whose entire safety argument is "a server votes once per term" is exactly
//! the protocol you do not want taking the voter's *or* the candidate's
//! identity from a field an attacker fills in.
//!
//! The same caveat applies with the same force. [`Context::peer`] is `None`
//! over plain TCP, so identity here is an **address** checked against a table fixed
//! at construction, behind [`crate::identity::Identity`]. An address is not a credential. In a simulated
//! network nothing can spoof one; on a real network it is worth very little,
//! and replacing it with TLS identity is the first thing to do.
//!
//! # What a server writes down before it speaks
//!
//! Raft's own figure 2 requires `currentTerm` and `votedFor` to be *"updated on
//! stable storage before responding to RPCs"*, and that is not an optimisation
//! note — it is the same requirement the ownership registry's epoch floor turned
//! out to have, arrived at from the other end.
//!
//! A server that grants a vote, replies, restarts having forgotten, and grants
//! again has voted twice in one term. Two candidates can then each collect a
//! majority, and Election Safety is gone — not because the proof is wrong, but
//! because `already_voted` was reported `false` when the model's `has_voted`
//! was true. That is the coupling `crate::raft::proofs::refinement` names, and
//! [`Durable`] is what discharges it.
//!
//! So the order is: decide, **persist**, then reply. A server that dies between
//! the persist and the reply has lost a message, which the protocol handles. A
//! server that dies between the reply and the persist has broken the protocol.
//!
//! # What is here, and what it is worth
//!
//! The election, the log and the commit point: `request_vote` with the
//! up-to-date comparison, `append_entries` with the consistency check and the
//! truncation, `heartbeat`, and — inherent rather than on the wire, because
//! they are a server acting on itself — [`Peer::stand_for_election`],
//! [`Peer::append_command`] and [`Peer::record_match`], whose commit rule is
//! figure 8's.
//!
//! **What it is worth is the model's line, not more.** Election Safety and Log
//! Matching are proved; Leader Completeness and State Machine Safety are not,
//! for the reason `crate::raft::model`'s docs give. So two servers that agree on
//! an entry agree on everything below it — but that agreement is not yet proved
//! to survive a leader change, and until it is this service cannot make the
//! ownership registry's contents a single agreed fact.
//!
//! # Replies are a protocol step too
//!
//! A server does not only answer RPCs, it *reads the answers to its own* — and
//! Raft's term rule is about both directions: *"if RPC request or response
//! contains term T > currentTerm, set currentTerm = T, convert to follower"*.
//! A `Ballot::Refused(2)` reaching a term-1 candidate, or a `Standing { term: 2,
//! .. }` reaching a term-1 leader, carries exactly the same news as an inbound
//! request would.
//!
//! [`Peer::count_ballot`], [`Peer::observe_standing`] and
//! [`Peer::observe_appended`] are that side of the protocol. They take the
//! reply itself rather than a summary of it, which is what stops a caller
//! tallying a vote nobody granted: **there is no way to add to the tally except
//! by handing over a `Ballot::Granted` for the term being stood in**, and the
//! coupling `has_quorum == won_election` that the proof rests on is only as good
//! as that.
//!
//! **One of the three used to take the term the request went out in as an
//! argument, and no longer does.** A reply carries no clock: an acknowledgement
//! looks the same whenever it was sent, and one that crossed a leadership
//! boundary would be counted against a log the terms in between may have
//! rewritten. [`Appended::Accepted`] now carries [`Acceptance`], which states
//! the term the follower accepted at, so [`Peer::observe_appended`] compares
//! that against its own term and there is no argument left for a caller to get
//! wrong. [`Peer::count_ballot`] and [`Peer::observe_standing`] still take the
//! term, because a `Ballot` and a `Standing` are answers about a term rather
//! than about a log, and the term they name is the one being asked about.
//!
//! Every stale-reply hazard in this file is the same shape — state that outlives
//! the leadership it was collected for — which is also what
//! `crate::raft::proofs::history` is about on the other side.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::id::Id;
use crate::identity::{Identity, IntoIdentity};
use crate::raft::store::{apply_record, replay_exec, ExecEntry, ExecRecord};
use crate::raft::exec::{Counted, ElectRefusal, ElectionCore, VoteOutcome};
use crate::raft::steps::{is_majority, RaftRefusal};
use jetstream::prelude::*;

/// The reply to a vote request.
///
/// Both cases carry the voter's term, which is Raft's rule: a candidate that
/// hears a higher term learns it has already lost, and a refusal that did not
/// say so would leave it standing for a term nobody will vote in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub enum Ballot {
    /// The vote is yours, at this term.
    Granted(u64),
    /// Not this time. This is the voter's term.
    Refused(u64),
}

/// What a server says about itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Standing {
    pub term: u64,
    /// Whether this server believes it leads `term`. **A belief, not a fact**:
    /// a partitioned leader goes on believing this until it hears a higher
    /// term. Election Safety says at most one server can be right.
    pub leading: bool,
}

/// One log entry, on the wire and in storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct LogEntry {
    /// The term of the leader that created it. This is what makes an entry's
    /// `(index, term)` pair name a leader: Election Safety says there was only
    /// one leader of that term.
    pub term: u64,
    /// The command. Opaque here, as it is in the model: the safety argument is
    /// about the order entries are applied in, not about what they mean.
    pub value: u64,
}

/// **What a follower says when it takes an entry.**
///
/// Two fields, and the term is the one that matters. A reply carrying only a
/// length says *what* the follower has and nothing about *when* — and a length
/// read in a later term is an acknowledgement of a log the terms in between may
/// have rewritten. [`Peer::observe_appended`] used to take the term as a
/// *caller* argument, which put the whole staleness check in the hands of
/// whoever remembered to pass the right number.
///
/// Now the reply says which term it was accepted at, and the leader compares
/// that against its own. There is no argument left to get wrong.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Acceptance {
    /// The term the follower accepted at — which is the term the request
    /// carried, since `append_entries` refuses anything behind its own and
    /// steps up to anything ahead.
    pub term: u64,
    /// The follower's log length afterwards, which is what the leader tracks to
    /// decide what is replicated.
    pub len: u64,
}

/// The reply to `append_entries`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub enum Appended {
    /// Taken, at a stated term. See [`Acceptance`].
    Accepted(Acceptance),
    /// Refused. This is the follower's term, so a stale leader finds out.
    Rejected(u64),
}

/// **The replicated log.**
///
/// A trait, and mockable, for two reasons that pull the same way. A real log is
/// a file with a format, a fsync policy and a truncation story, and none of
/// that belongs in the protocol; and the protocol's own behaviour — the
/// consistency check, the truncation, the up-to-date comparison — is exactly
/// what you want to test without a disk in the way.
///
/// Every mutating method **must be durable before it returns**, for the reason
/// `Durable` gives about votes: a log that forgets an entry it acknowledged has
/// told the leader something untrue, and the leader may have committed on the
/// strength of it.
pub trait LogStore: Send + Sync + 'static {
    /// How many entries there are.
    fn len(&self) -> io::Result<u64>;

    /// Whether there are none.
    fn is_empty(&self) -> io::Result<bool> {
        Ok(self.len()? == 0)
    }

    /// The entry at `index`, or `None` past the end.
    fn entry_at(&self, index: u64) -> io::Result<Option<LogEntry>>;

    /// Append one entry, returning the new length.
    fn append(&self, entry: LogEntry) -> io::Result<u64>;

    /// Keep the first `prefix` entries, drop the rest, append `entry`.
    ///
    /// The truncation is the part that matters and the part a naive
    /// implementation gets wrong: a follower that appends without dropping the
    /// divergent tail keeps entries no leader ever committed.
    fn overwrite(&self, prefix: u64, entry: LogEntry) -> io::Result<()>;

    /// The term of the entry at `index`, or `None` past the end.
    fn term_at(&self, index: u64) -> io::Result<Option<u64>> {
        Ok(self.entry_at(index)?.map(|e| e.term))
    }

    /// The `(last term, length)` pair a `RequestVote` carries.
    ///
    /// An empty log reports term 0, which is safe as a floor because no entry
    /// is ever created at term 0: entries come from leaders, and a leader's
    /// term is at least 1.
    fn summary(&self) -> io::Result<(u64, u64)> {
        let n = self.len()?;
        if n == 0 {
            Ok((0, 0))
        } else {
            Ok((self.term_at(n - 1)?.unwrap_or(0), n))
        }
    }
}

/// An in-memory log. The mock, and the thing the tests run against.
#[derive(Clone, Debug, Default)]
pub struct MemoryLogStore(Arc<Mutex<Vec<LogEntry>>>);

impl MemoryLogStore {
    pub fn new() -> Self {
        MemoryLogStore(Arc::new(Mutex::new(Vec::new())))
    }

    /// The whole log, for tests to compare against.
    pub fn entries(&self) -> Vec<LogEntry> {
        self.0.lock().expect("log lock").clone()
    }
}

impl LogStore for MemoryLogStore {
    fn len(&self) -> io::Result<u64> {
        Ok(self.0.lock().expect("log lock").len() as u64)
    }

    fn entry_at(&self, index: u64) -> io::Result<Option<LogEntry>> {
        Ok(self.0.lock().expect("log lock").get(index as usize).copied())
    }

    fn append(&self, entry: LogEntry) -> io::Result<u64> {
        let mut g = self.0.lock().expect("log lock");
        g.push(entry);
        Ok(g.len() as u64)
    }

    fn overwrite(&self, prefix: u64, entry: LogEntry) -> io::Result<()> {
        let mut g = self.0.lock().expect("log lock");
        g.truncate(prefix as usize);
        g.push(entry);
        Ok(())
    }
}

/// **A `LogStore` whose device is append-only**, and the executable form of
/// [`crate::raft::store`].
///
/// [`MemoryLogStore`] is a `Vec<LogEntry>` that shrinks when it truncates,
/// which is a log no durable device can be. This one keeps a **record log** —
/// appends and truncation markers, only ever growing — and its entries are
/// `replay_exec` of that. `crate::raft::proofs::store` is what says the two
/// agree: C27 says memory and device never disagree, C28 says a crash can only
/// rewind, C29 says accepting a replicated entry costs at most two records.
///
/// It is still in memory. The point is not durability yet — it is that the
/// shape is the shape a device can serve, so wiring one underneath changes
/// where the bytes go and not what the store does. [`Self::after_crash`] is
/// that claim made testable: drop any suffix of the records and replay, which
/// is exactly what C28 says a crash can do.
///
/// # Order of writes
///
/// The record goes onto the device **before** the in-memory log is updated. A
/// crash between the two leaves memory behind the device, and recovery replays
/// the device, so nothing is lost. The other order leaves memory *ahead* of the
/// device — a store that believes an entry it never wrote down, which is the
/// failure `LogStore`'s durability requirement exists to forbid.
#[derive(Clone)]
pub struct RecordLogStore(Arc<Mutex<RecordInner>>);

struct RecordInner {
    /// The device. Only ever grows — C30.
    records: Vec<ExecRecord>,
    /// The log, kept equal to `replay_exec(&records)` — C27.
    log: Vec<ExecEntry>,
    /// How many records have been reported durable — C35. A crash may not go
    /// below this, and it only lags inside a multi-record operation.
    durable: usize,
}

/// **When the device has outgrown the log enough to be worth rewriting.**
///
/// A compacted device is `log.len() + 1` records — the marker, then one append
/// per entry — so compacting at twice that keeps the device within a constant
/// factor of the log and does amortised O(1) work per write: each compaction
/// costs `log.len() + 1` writes and cannot recur until at least `log.len() + 1`
/// more records have accumulated.
///
/// Two is a choice, not a derivation. Lower thrashes on a follower that is
/// being rewritten repeatedly; higher lets the device grow further between
/// rewrites. The bound is what matters and the constant is tunable.
fn worth_compacting(records: usize, entries: usize) -> bool {
    records > 2 * (entries + 1)
}

impl Default for RecordLogStore {
    fn default() -> Self {
        RecordLogStore::new()
    }
}

impl RecordLogStore {
    pub fn new() -> Self {
        RecordLogStore(Arc::new(Mutex::new(RecordInner {
            records: Vec::new(),
            log: Vec::new(),
            durable: 0,
        })))
    }

    /// Start from a device. This is recovery, and it is the whole of it:
    /// `replay_exec` and nothing else.
    pub fn recovered(records: Vec<ExecRecord>) -> Self {
        let log = replay_exec(&records);
        // Everything that survived is on the device, so it is durable.
        let durable = records.len();
        RecordLogStore(Arc::new(Mutex::new(RecordInner { records, log, durable })))
    }

    /// What is on the device.
    pub fn records(&self) -> Vec<ExecRecord> {
        self.0.lock().expect("record log lock").records.clone()
    }

    /// How many records are on the device. Distinct from `len()`, which is the
    /// number of *entries* — a truncation is a record and not an entry, so
    /// these diverge, and watching them diverge is what C31's compaction is
    /// for.
    pub fn device_len(&self) -> usize {
        self.0.lock().expect("record log lock").records.len()
    }

    /// How many records have been reported durable.
    ///
    /// Equal to `device_len()` whenever no operation is in flight, because
    /// every `LogStore` method here syncs before it returns. It lags only
    /// *inside* a two-record `overwrite`, which is the one window a crash can
    /// lose anything at all.
    pub fn durable_len(&self) -> usize {
        self.0.lock().expect("record log lock").durable
    }

    /// **The crash.** A new store recovered from the first `survived` records.
    ///
    /// C28 in executable form: the device keeps a prefix, recovery is `replay`
    /// of it, and what comes back is a log this store had.
    ///
    /// `survived` past the end is clamped, because a caller asking about more
    /// records than exist is asking about no crash at all. It is **not**
    /// clamped up to `durable`: this is a test facility, and a crash landing
    /// below the durable line is precisely what
    /// `theorem_durability_never_retreats` says cannot happen — so being able
    /// to ask for one is how a test can check that the store never puts itself
    /// in a position where it would matter. Between operations `durable`
    /// equals the record count, so no such point exists;
    /// `nothing_is_lost_between_operations` is the test that says so.
    pub fn after_crash(&self, survived: usize) -> Self {
        let all = self.records();
        let keep = if survived < all.len() { survived } else { all.len() };
        RecordLogStore::recovered(all[..keep].to_vec())
    }

    /// **Rewrite the device as pure appends**, which is C31 and C36.
    ///
    /// Two steps, and the order matters. First the **batch** — a
    /// `Truncate { len: 0 }` followed by one append per entry — is written and
    /// synced as a unit. Then the old generation is dropped, which on
    /// `pmemlog` is `advance_head` and here is a `drain`.
    ///
    /// The leading marker is what makes the middle state safe. Without it a
    /// crash between the two steps would leave the old records followed by the
    /// new generation, which replays to `log + log` — every entry twice.
    /// `theorem_a_staged_compaction_is_inert` is the proof that with it, the
    /// device means the same log before the reclaim and after it, so a crash
    /// on either side of that step recovers the same thing.
    ///
    /// The batch is synced **as one**: a crash inside it would leave the
    /// marker and a prefix of the log, which is a rewind and could go below
    /// the durable line. On `pmemlog` that is a single `append`, whose crash
    /// view of the **abstract log** is the log before it or after it and
    /// nothing between — earned by its CRC rather than given by byte-atomic
    /// hardware, since its own model permits any subset of 8-byte chunks to
    /// have been flushed. `crate::raft::store::store_write_batch` says this at
    /// length; the short version is that the guarantee is as strong as the two
    /// corruption assumptions `vendor/README.md` enumerates, and no
    /// stronger.
    ///
    /// What this does *not* do is schedule itself: nothing calls it, and a
    /// store that never compacts grows without bound. Stated in
    /// `crate::raft::store` and repeated here because this is where a reader
    /// would look for the bound.
    pub fn compact(&self) {
        let mut g = self.0.lock().expect("record log lock");

        // The batch: a marker that clears whatever came before, then one
        // append per entry.
        let mut batch: Vec<ExecRecord> = Vec::with_capacity(g.log.len() + 1);
        batch.push(ExecRecord { is_truncate: true, a: 0, b: 0 });
        batch.extend(
            g.log.iter().map(|e| ExecRecord { is_truncate: false, a: e.term, b: e.value }),
        );

        // **Installed as one.** Not `write_record` in a loop: every
        // intermediate state of that loop is the marker plus a *prefix* of the
        // log, which replays to a shorter log than the store had, and a crash
        // in the middle of it is data loss on an operation whose whole purpose
        // is to change nothing. `theorem_a_partial_batch_can_rewind` proves
        // that hazard is exact rather than theoretical.
        //
        // On a real `InfiniteLogImpl` this is one `append` of the encoded
        // batch, whose crash view is the device before the call or after it and
        // nothing between — `store_write_batch`, and the one property this
        // design asks of the device that it cannot itself check. Here the lock
        // gives the same guarantee: no reader sees a half-installed `records`.
        //
        // The old generation is dropped in the same step, which is sound
        // because the batch replays to the same log with it there and with it
        // gone (`theorem_after_compaction_the_old_records_are_dead`) — so the
        // reclaim is a no-op and needs no crash window of its own.
        g.records = batch;
        g.durable = g.records.len();
    }

    /// The whole log, for tests to compare against.
    pub fn entries(&self) -> Vec<LogEntry> {
        self.0
            .lock()
            .expect("record log lock")
            .log
            .iter()
            .map(|e| LogEntry { term: e.term, value: e.value })
            .collect()
    }
}

/// Put one record on the device, then apply it.
///
/// The only way this store changes. `apply_record` is the verified function
/// from `crate::raft::store`, so the in-memory log is not maintained by
/// hand-written logic that could disagree with `replay` — it is maintained by
/// the function `replay` is defined in terms of.
fn write_record(g: &mut RecordInner, r: ExecRecord) {
    g.records.push(r);
    apply_record(&mut g.log, r);
}

/// Everything written has landed. What `LogStore`'s *"durable before it
/// returns"* means, and the only thing that moves the line a crash may not go
/// below.
fn sync(g: &mut RecordInner) {
    g.durable = g.records.len();
}

/// **Rewrite the device if it has outgrown the log.**
///
/// Called after every write that syncs, which is the end of every `LogStore`
/// method. This is what closes the limitation C31 left open: compaction was
/// proved sound and nothing ran it, so a store that never compacted grew
/// without bound. It runs now, on the policy [`worth_compacting`] states.
///
/// Safe to call at the end of an operation and nowhere else: it installs its
/// batch atomically (C36), so it introduces no crash window of its own, and it
/// leaves the durable line at the end of the device — which is what the caller
/// was about to be promised anyway.
fn compact_if_worthwhile(g: &mut RecordInner) {
    if !worth_compacting(g.records.len(), g.log.len()) {
        return;
    }
    let mut batch: Vec<ExecRecord> = Vec::with_capacity(g.log.len() + 1);
    batch.push(ExecRecord { is_truncate: true, a: 0, b: 0 });
    batch.extend(g.log.iter().map(|e| ExecRecord { is_truncate: false, a: e.term, b: e.value }));
    g.records = batch;
    g.durable = g.records.len();
}

impl LogStore for RecordLogStore {
    fn len(&self) -> io::Result<u64> {
        Ok(self.0.lock().expect("record log lock").log.len() as u64)
    }

    fn entry_at(&self, index: u64) -> io::Result<Option<LogEntry>> {
        Ok(self
            .0
            .lock()
            .expect("record log lock")
            .log
            .get(index as usize)
            .map(|e| LogEntry { term: e.term, value: e.value }))
    }

    fn append(&self, entry: LogEntry) -> io::Result<u64> {
        let mut g = self.0.lock().expect("record log lock");
        write_record(&mut g, ExecRecord { is_truncate: false, a: entry.term, b: entry.value });
        sync(&mut g);
        compact_if_worthwhile(&mut g);
        Ok(g.log.len() as u64)
    }

    /// **One record when extending, two on a conflict**, which is C29 and
    /// `theorem_extending_the_log_costs_one_record`.
    ///
    /// `Peer::append_entries` calls this whenever the entry at `prefix` is not
    /// already the leader's — which covers both *extending past the end* and
    /// *replacing a divergent entry*, and those cost different amounts. When
    /// `prefix` is the current length there is no tail to delete, so the marker
    /// would be `Truncate { len: len }`: the identity. Writing it would double
    /// the cost of the steady state of replication for nothing, so it is not
    /// written.
    ///
    /// The branch that costs *nothing at all* is not here. `append_entries`
    /// decides whether the entry conflicts and does not call this if it does
    /// not, so a duplicate `AppendEntries` never reaches the device.
    fn overwrite(&self, prefix: u64, entry: LogEntry) -> io::Result<()> {
        let mut g = self.0.lock().expect("record log lock");
        if (prefix as usize) < g.log.len() {
            write_record(&mut g, ExecRecord { is_truncate: true, a: prefix, b: 0 });
        }
        write_record(&mut g, ExecRecord { is_truncate: false, a: entry.term, b: entry.value });
        // One sync, at the end, so the two records land together or not at
        // all. The window between them is the only place a crash can lose
        // anything, and what it leaves — the marker without the entry — is a
        // truncation and no more.
        sync(&mut g);
        compact_if_worthwhile(&mut g);
        Ok(())
    }
}

/// The node-facing protocol.
///
/// Three methods, and none of them takes a server number — see the module docs.
/// Standing for election, tallying votes and taking a term are *not* here: they
/// are things a server does to itself, and putting them on the wire would let a
/// peer declare somebody leader. They are inherent methods on [`Peer`], for the
/// same reason `force` is inherent on the ownership registry.
#[service(uses(super::{Appended, Ballot, LogEntry, Standing}))]
pub trait Consensus {
    /// `RequestVote`. The candidate is the caller.
    ///
    /// `last_term` and `last_index` are the candidate's log summary, and the
    /// voter judges them against its own. They are arguments rather than
    /// something the voter looks up, because a vote has to be decided on what
    /// was true when it was asked for — and because the voter cannot see the
    /// candidate's log at all.
    async fn request_vote(
        &self,
        ctx: Context,
        term: u64,
        last_term: u64,
        last_index: u64,
    ) -> Result<Ballot>;

    /// `AppendEntries`, one entry at a time. The leader is the caller.
    ///
    /// `prefix` is how many entries the leader believes the follower already
    /// agrees on, and `prev_term` is the term of the entry before that — the
    /// **consistency check**. A follower that accepts drops whatever it had
    /// beyond `prefix`.
    async fn append_entries(
        &self,
        ctx: Context,
        term: u64,
        prefix: u64,
        prev_term: u64,
        entry: LogEntry,
        leader_commit: u64,
    ) -> Result<Appended>;

    /// A leader asserting its term. The leader is the caller.
    ///
    /// **An `append_entries` with nothing in it**, which is what figure 2 makes
    /// it, and that is why it carries `leader_commit`. A leader commits only
    /// once a majority has acknowledged, so the request that *caused* the
    /// commit carried the commit point from before it; if no further command
    /// arrives, heartbeats are the only traffic left and a follower that
    /// learned nothing from them would hold an entry it never found out was
    /// committed, and so never apply it.
    async fn heartbeat(&self, ctx: Context, term: u64, leader_commit: u64) -> Result<Standing>;

    /// What term is this server in, and does it think it leads?
    async fn standing(&self, ctx: Context) -> Result<Standing>;
}

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

/// The server could not make a decision durable, so it did not make one.
///
/// The same code and the same reasoning as the ownership service's: this says
/// nothing about the protocol's state, so an auditor must not read it as a
/// guard having been evaluated. Here it is load-bearing rather than tidy —
/// answering a vote request the server could not write down is precisely the
/// failure that breaks Election Safety.
fn refuse_down(what: &str) -> Error {
    Error::new(what).set_code("DOWN")
}

/// The `u64` term space is exhausted.
fn exhausted() -> Error {
    Error::new("the term space is exhausted").set_code("NO")
}

fn refuse(why: RaftRefusal) -> Error {
    match why {
        RaftRefusal::Exhausted => exhausted(),
        RaftRefusal::AlreadyVoted => refuse_no("already voted in that term"),
        RaftRefusal::TermBehind => refuse_no("that term is behind mine"),
        RaftRefusal::NotCandidate => refuse_no("not standing for that term"),
        RaftRefusal::NoQuorum => refuse_no("not a majority"),
        RaftRefusal::NotHigher => refuse_no("that term is not ahead of mine"),
        RaftRefusal::AlreadyLeading => refuse_no("already leading a term"),
    }
}

// ---------------------------------------------------------------------------
// Durable state
// ---------------------------------------------------------------------------

/// The two things Raft requires on stable storage.
///
/// Exactly figure 2's "persistent state on all servers", minus the log:
/// `currentTerm` and `votedFor`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Persisted {
    pub current_term: u64,
    /// Who this server voted for **in `current_term`**. Cleared whenever the
    /// term advances, because a vote belongs to the term it was cast in.
    pub voted_for: Option<Id>,
}

/// Stable storage for [`Persisted`].
///
/// `save` must not return until the value is durable. An implementation that
/// returns early satisfies the type and breaks Election Safety, which is the
/// usual shape of this kind of interface and is stated here rather than left
/// to be inferred.
///
/// # A failed `save` is not a `save` that did not happen
///
/// **This is part of the system model, not a caveat.** `save` installs a value
/// and then makes the installation durable, and those are two operations: the
/// write-to-temporary, rename, fsync-the-directory sequence [`FileLog`] uses
/// can fail on the *last* step with the new value already visible to any later
/// `load`. So an `Err` from `save` means *"this value may or may not be
/// there"*, never *"it is not there"*.
///
/// The [`Peer`] handles that by never advancing its own record on a failed
/// `save` — so what it has acted on is always something it wrote down
/// successfully — and by asking the store what it actually holds, which is what
/// its `persist` does. Durable state may then be *ahead* of a running
/// server's memory, and that direction is the safe one: a server that restarts
/// believing it spent a vote it never cast refuses more than it had to, while
/// the converse votes twice.
pub trait Durable: Send + Sync + 'static {
    fn load(&self) -> io::Result<Persisted>;
    fn save(&self, state: Persisted) -> io::Result<()>;
}

/// Storage that survives the [`Peer`] but not the process.
///
/// Enough to reproduce the defect that matters — a server that comes back not
/// knowing what it voted for — without killing a process.
#[derive(Clone, Debug, Default)]
pub struct MemoryLog(Arc<Mutex<Persisted>>);

impl MemoryLog {
    pub fn new() -> Self {
        MemoryLog(Arc::new(Mutex::new(Persisted::default())))
    }
}

impl Durable for MemoryLog {
    fn load(&self) -> io::Result<Persisted> {
        Ok(*self.0.lock().expect("vote log lock"))
    }

    fn save(&self, state: Persisted) -> io::Result<()> {
        *self.0.lock().expect("vote log lock") = state;
        Ok(())
    }
}

/// Storage that survives the machine.
///
/// Temporary file, `fsync`, rename, `fsync` the directory — and the directory
/// sync is never skipped, including when the path is a bare filename whose
/// `Path::parent` is the empty path. Skipping it there was a real finding on
/// the ownership service's equivalent: it made durability depend on how the
/// caller spelled the path, and losing the rename resurrects the previous
/// state, which is the exact failure this type exists to prevent.
pub struct FileLog {
    path: PathBuf,
}

impl FileLog {
    pub fn new(path: impl AsRef<Path>) -> Self {
        FileLog { path: path.as_ref().to_path_buf() }
    }
}

impl Durable for FileLog {
    fn load(&self) -> io::Result<Persisted> {
        match fs::read_to_string(&self.path) {
            Ok(text) => {
                let mut parts = text.split_whitespace();
                let bad = || {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("{}: not a persisted Raft state", self.path.display()),
                    )
                };
                let current_term: u64 = parts.next().ok_or_else(bad)?.parse().map_err(|_| bad())?;
                let voted_for = match parts.next().ok_or_else(bad)? {
                    "-" => None,
                    other => Some(other.parse::<Id>().map_err(|_| bad())?),
                };
                Ok(Persisted { current_term, voted_for })
            }
            // Never written. Distinguished from a read failure on purpose: a
            // server may legitimately start with no history, and may not start
            // by *ignoring* a record it could not read.
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(Persisted::default()),
            Err(e) => Err(e),
        }
    }

    fn save(&self, state: Persisted) -> io::Result<()> {
        let tmp = self.path.with_extension("next");
        {
            let mut f = fs::File::create(&tmp)?;
            match state.voted_for {
                Some(c) => write!(f, "{} {}", state.current_term, c)?,
                None => write!(f, "{} -", state.current_term)?,
            }
            f.sync_all()?;
        }
        fs::rename(&tmp, &self.path)?;
        let dir = self.path.parent().unwrap_or_else(|| Path::new(""));
        let dir = if dir.as_os_str().is_empty() { Path::new(".") } else { dir };
        fs::File::open(dir)?.sync_all()?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// The audit log
// ---------------------------------------------------------------------------

/// One thing a server did. The record an auditor reads after the fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// Stood for election in a new term, voting for itself.
    Stood { term: u64 },
    /// Granted its vote.
    Granted { term: u64, to: Id },
    /// Refused one. Named by the *request's* term.
    RefusedVote { term: u64, to: Id },
    /// Counted a vote in its own favour.
    Counted { term: u64, from: Id },
    /// Took a term, with the tally that bought it.
    Led { term: u64, votes: u64 },
    /// Learned of a higher term and stepped down into it.
    SteppedDown { from_term: u64, to_term: u64 },
    /// The leader appended a client command at its own term.
    Appended { term: u64, index: u64 },
    /// A follower accepted an entry, and this is its log length afterwards.
    Accepted { term: u64, prefix: u64, len: u64 },
    /// A follower refused one — the consistency check, or a stale term.
    RefusedAppend { term: u64, prefix: u64 },
    /// The leader advanced the commit point.
    Committed { term: u64, upto: u64 },
}

// ---------------------------------------------------------------------------
// The server
// ---------------------------------------------------------------------------

struct Inner {
    /// The election record: role and term, whom this server voted for in that
    /// term, and — as a candidate — the votes it has counted, **a set**, because
    /// `is_majority`'s precondition is that the tally does not exceed the
    /// membership, and a list would let one enthusiastic peer vote twice.
    /// Verified code: each method on it is a model step
    /// (`proofs::election_core`).
    core: ElectionCore,
    /// How many entries are committed. A count, not an index — the same choice
    /// the model makes, and for the same reason.
    commit: u64,
    /// Per-follower replication progress, kept by a leader: how many entries
    /// each is known to hold. This is what a majority is counted over when the
    /// commit point advances.
    match_len: HashMap<Id, u64>,
    log: Vec<Event>,
}

/// One Raft server.
#[derive(Clone)]
pub struct Peer {
    inner: Arc<Mutex<Inner>>,
    /// Which server is calling, and which servers there are. The stated
    /// assumption; see the module docs and [`crate::identity`].
    identity: Arc<dyn Identity>,
    /// This server's own number.
    me: Id,
    store: Arc<dyn Durable>,
    /// The replicated log. A trait so that the protocol can be exercised
    /// without a disk, and so that a real one can be a real one.
    entries: Arc<dyn LogStore>,
}

impl Peer {
    /// A server that recovers whatever `store` remembers.
    ///
    /// **The term is read, not supplied.** A server that started at a term of
    /// its caller's choosing could re-enter a term it had already voted in,
    /// which is the same defect the ownership registry had when `new` took its
    /// epoch from the caller, and it breaks the same guarantee.
    pub fn new(
        identity: impl IntoIdentity,
        me: Id,
        store: Arc<dyn Durable>,
        entries: Arc<dyn LogStore>,
    ) -> io::Result<Self> {
        let identity = identity.into_identity();
        if !identity.knows(me) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("server {me} is not on the roster"),
            ));
        }
        let recovered = store.load()?;
        Ok(Peer {
            inner: Arc::new(Mutex::new(Inner {
                // A recovered server is always a follower. Raft has no durable
                // role, and inventing one would let a restarted leader go on
                // leading a term the cluster has moved past.
                core: ElectionCore::recovered(recovered.current_term, recovered.voted_for),
                // Volatile, per figure 2: a recovered server recomputes what is
                // committed from the leader rather than trusting a number it
                // wrote down. Starting at 0 costs a round trip and cannot be
                // wrong.
                commit: 0,
                match_len: HashMap::new(),
                log: Vec::new(),
            })),
            identity,
            me,
            store,
            entries,
        })
    }

    /// The log, for a caller that needs to read it (a leader deciding what to
    /// send, a test checking what landed).
    pub fn log_store(&self) -> &Arc<dyn LogStore> {
        &self.entries
    }

    /// The `(last term, length)` pair a vote request carries.
    pub fn summary(&self) -> Result<(u64, u64)> {
        self.entries.summary().map_err(|e| refuse_down(&format!("could not read the log: {e}")))
    }

    /// How many entries this server considers committed.
    pub fn commit(&self) -> u64 {
        self.inner.lock().expect("peer lock").commit
    }

    /// How many servers are in the cluster.
    ///
    /// The count is of **distinct server numbers**, not of roster entries. This
    /// one really is a cardinality question — a majority is about *how many* —
    /// unlike "is this a member", which is about the roster's values; the two
    /// were conflated once already in this repository and are kept visibly
    /// apart here. Counting entries would also be wrong in its own right the
    /// moment one server is reachable at two addresses, which is an ordinary
    /// thing for a server to be.
    fn members(&self) -> u64 {
        self.identity.nodes().into_iter().collect::<HashSet<Id>>().len() as u64
    }

    fn is_member(&self, n: Id) -> bool {
        self.identity.knows(n)
    }

    /// Which server is calling, from the connection rather than the request.
    fn caller(&self, ctx: &Context) -> Option<Id> {
        self.identity.caller(ctx)
    }

    /// Write the decision down before acting on it.
    ///
    /// **A failure here re-reads the store**, for the reason [`Durable`]'s docs
    /// give: `save` can fail with the value installed, and a server that went
    /// on as if nothing had happened could later write an *older* term over it.
    /// That older term is one this server did act on, so it is not unsafe — but
    /// it makes the durable record non-monotone, and a durable record that can
    /// go backwards is a thing no later reader can reason about. Asking the
    /// store settles it immediately: whatever is really there is adopted if it
    /// is ahead, and the caller still gets its error.
    ///
    /// The core calls this closure with the term and vote about to be adopted and
    /// moves only if it returns `true`; what the store complained of is left in
    /// `failed`, for [`Peer::down`] to turn into the refusal.
    fn saver<'a>(
        &'a self,
        failed: &'a mut Option<io::Error>,
    ) -> impl FnOnce(u64, Option<Id>) -> bool + 'a {
        move |current_term, voted_for| {
            match self.store.save(Persisted { current_term, voted_for }) {
                Ok(()) => true,
                Err(e) => {
                    *failed = Some(e);
                    false
                }
            }
        }
    }

    /// The refusal for a decision the store would not take: re-read it, as above,
    /// and say so.
    fn down(&self, g: &mut Inner, term: u64, failed: Option<io::Error>) -> Error {
        self.resync(g);
        match failed {
            Some(e) => refuse_down(&format!("could not persist term {term}: {e}")),
            None => refuse_down(&format!("could not persist term {term}")),
        }
    }

    /// Adopt whatever the store holds, if it is ahead of this server.
    ///
    /// A best-effort repair, and deliberately silent about its own failure: it
    /// runs on a path that is already returning an error, and a store that
    /// cannot be read leaves the server exactly where a store that was never
    /// read would — which is the state it is in anyway.
    fn resync(&self, g: &mut Inner) {
        let Ok(found) = self.store.load() else {
            return;
        };
        if found.current_term <= g.core.server.current_term {
            return;
        }
        let from_term = g.core.server.current_term;
        // A follower, for the same reason recovery produces one: there is no
        // durable role, and a term this server did not reach under its own
        // power is not a term it can be leading.
        g.core = ElectionCore::recovered(found.current_term, found.voted_for);
        g.log.push(Event::SteppedDown { from_term, to_term: found.current_term });
    }

    /// The audit log so far.
    pub fn log(&self) -> Vec<Event> {
        self.inner.lock().expect("peer lock").log.clone()
    }

    /// What this server believes about itself.
    pub fn standing_now(&self) -> Standing {
        let g = self.inner.lock().expect("peer lock");
        Standing {
            term: g.core.server.current_term,
            leading: g.core.leads(),
        }
    }

    /// **Stand for election in the next term**, voting for yourself.
    ///
    /// Inherent rather than on the trait: a timeout is a server's own clock
    /// going off, and a peer that could trigger it could keep the cluster in a
    /// permanent election.
    pub fn stand_for_election(&self) -> Result<u64> {
        let mut g = self.inner.lock().expect("peer lock");
        // Durable before anything else, and the self-vote goes down with the
        // term: they are one decision, and a server that recorded the term
        // without the vote could vote again in it after a restart. The core
        // hands both to the store and moves only if it took them.
        let mut failed = None;
        let term = match g.core.stand(self.me, self.saver(&mut failed)) {
            Ok(term) => term,
            Err(ElectRefusal::Refused(why)) => return Err(refuse(why)),
            Err(ElectRefusal::Down) => {
                let attempted = g.core.server.current_term.saturating_add(1);
                return Err(self.down(&mut g, attempted, failed));
            }
        };
        g.log.push(Event::Stood { term });

        // **A cluster of one is already a majority of itself.** No ballot can
        // ever arrive — there is nobody to ask — so a server that only took the
        // term when a reply came back would stand for ever. The check belongs
        // here rather than in a caller faking a ballot from itself, which would
        // be a caller putting a vote into the tally that nobody cast.
        let my_len = self
            .entries
            .len()
            .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?;
        // Counting the self-vote again is idempotent, and is what asks the core
        // whether one vote is already a majority.
        let counted = g.core.count(self.me, term, self.members());
        self.after_count(&mut g, counted, term, my_len);
        Ok(term)
    }

    /// **Read a peer's reply to `request_vote`.**
    ///
    /// Returns whether this server now leads.
    ///
    /// The `Ballot` itself is the argument, not a summary of it, and that is
    /// the point rather than an interface preference. A method that took only
    /// `(from, term)` would let a caller tally a peer that refused — or that
    /// was never asked — and a majority assembled that way elects a leader the
    /// model never elected, which breaks the `has_quorum == won_election`
    /// coupling that `crate::raft::proofs::refinement` names and with it
    /// Election Safety itself. The one way into the tally is a
    /// `Ballot::Granted` for the term being stood in.
    ///
    /// A `Ballot::Refused` carrying a higher term is the other half of Raft's
    /// term rule — *"if RPC request **or response** contains term T >
    /// currentTerm"* — and is adopted here, durably, exactly as an inbound
    /// request carrying it would be.
    pub fn count_ballot(&self, from: Id, term: u64, ballot: Ballot) -> Result<bool> {
        if !self.is_member(from) {
            return Err(refuse_err("no such server"));
        }
        let mut g = self.inner.lock().expect("peer lock");
        let granted = match ballot {
            Ballot::Granted(t) => t,
            Ballot::Refused(t) => {
                // Nothing to count, and possibly a term to learn. `step_down_to`
                // refuses a term that is not ahead, which is the common case.
                self.step_down_to(&mut g, t)?;
                return Ok(g.core.leads());
            },
        };
        if granted != term {
            // A ballot granted for some other term. Whatever it is, it is not a
            // vote in this one.
            return Err(refuse_no("that ballot is for another term"));
        }
        let my_len = self
            .entries
            .len()
            .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?;
        // A vote for a term this server has left is not counted. Not an error on
        // anyone's part — it is what a reply delayed past a new election looks
        // like — but a stale ballot must not elect somebody in a term it was
        // never cast for. The core decides, and says whether it counted.
        //
        // Every tallied voter is a member and the set holds each at most once,
        // so the count cannot exceed the membership — which is exactly
        // `is_majority`'s precondition, and the core checks it rather than
        // assuming it.
        let counted = g.core.count(from, term, self.members());
        if !counted.counted {
            return Ok(counted.leads);
        }
        g.log.push(Event::Counted { term, from });
        Ok(self.after_count(&mut g, counted, term, my_len))
    }

    /// Become leader of `term` if `votes` is a majority, and report whether
    /// this server leads either way.
    ///
    /// **`match_len` is rebuilt, not added to.** Figure 2 lists `matchIndex[]`
    /// under "volatile state on leaders" and says *reinitialized after
    /// election*, and the word is load-bearing: an acknowledgement collected
    /// during an earlier leadership says a peer held `n` entries *then*, and in
    /// the terms since, that peer's log and this one may both have been
    /// overwritten. Carried forward, those stale lengths can form a majority on
    /// their own and commit a current-term entry at a reused index that no peer
    /// ever acknowledged — a commit with nothing behind it.
    ///
    /// The refusal path returns whether this server leads *now*, which is not
    /// always `false`: a second ballot arriving after the election is won
    /// refuses because the role is no longer `Candidate`, and reporting that as
    /// "does not lead" would tell a caller draining its vote replies that it
    /// had lost an election it won.
    fn after_count(&self, g: &mut Inner, counted: Counted, term: u64, my_len: u64) -> bool {
        if counted.won {
            g.match_len = HashMap::new();
            // A leader holds its own whole log, which is where the
            // replication tally starts from.
            g.match_len.insert(self.me, my_len);
            let votes = g.core.tally.len() as u64;
            g.log.push(Event::Led { term, votes });
        }
        // Not a majority yet, or not standing any more — and the second of
        // those includes already having won.
        counted.leads
    }

    /// **A client command**, appended by a leader at its own term.
    ///
    /// Inherent rather than on the trait for the reason `stand_for_election` is:
    /// it is the leader acting, not a peer asking. Returns the index the entry
    /// landed at.
    pub fn append_command(&self, value: u64) -> Result<u64> {
        // The lock is held across the append, and that is the point rather than
        // an oversight: "am I the leader" and "what index does this land at"
        // must not be separable, or two concurrent appends both read the same
        // length and one of them is wrong about where its entry went.
        let mut g = self.inner.lock().expect("peer lock");
        if !g.core.leads() {
            return Err(refuse_no("not the leader"));
        }
        let term = g.core.server.current_term;
        let len = self
            .entries
            .append(LogEntry { term, value })
            .map_err(|e| refuse_down(&format!("could not append: {e}")))?;
        g.log.push(Event::Appended { term, index: len - 1 });
        // A leader trivially holds its own entries.
        g.match_len.insert(self.me, len);
        Ok(len - 1)
    }

    /// Record that `from` holds `len` entries, and advance the commit point if
    /// that made a majority.
    ///
    /// **The commit rule is the figure-8 one**: a majority holding the prefix is
    /// not enough on its own — the last entry of that prefix has to be from this
    /// leader's own term. A majority *holding* an entry is not a majority having
    /// *voted* on it, and committing on replica count alone lets a later leader
    /// overwrite the entry.
    pub fn record_match(&self, from: Id, len: u64) -> Result<u64> {
        if !self.is_member(from) {
            return Err(refuse_err("no such server"));
        }
        let mut g = self.inner.lock().expect("peer lock");
        if !g.core.leads() {
            return Err(refuse_no("not the leader"));
        }
        let term = g.core.server.current_term;
        let best = g.match_len.get(&from).copied().unwrap_or(0);
        if len > best {
            g.match_len.insert(from, len);
        }

        // Try each candidate length from the longest down. Small clusters and
        // short logs; clarity beats cleverness here.
        let mut upto = g.match_len.values().copied().max().unwrap_or(0);
        while upto > g.commit {
            let holders = g.match_len.values().filter(|&&l| l >= upto).count() as u64;
            let of_my_term = self
                .entries
                .term_at(upto - 1)
                .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?
                == Some(term);
            if of_my_term && is_majority(holders.min(self.members()), self.members()) {
                g.commit = upto;
                g.log.push(Event::Committed { term, upto });
                break;
            }
            upto -= 1;
        }
        Ok(g.commit)
    }

    /// **Read a peer's reply to `heartbeat`, or an answer to `standing`.**
    ///
    /// The term rule again, from the direction a leader learns it has been
    /// deposed: a partitioned leader that reconnects finds out from the replies
    /// to its own heartbeats, and without this there is no way to tell it.
    ///
    /// Returns whether this server still believes it leads.
    pub fn observe_standing(&self, seen: Standing) -> Result<bool> {
        let mut g = self.inner.lock().expect("peer lock");
        self.step_down_to(&mut g, seen.term)?;
        Ok(g.core.leads())
    }

    /// **Read a follower's reply to `append_entries`.**
    ///
    /// `Accepted` is replication progress, so it goes to [`Peer::record_match`]
    /// and may advance the commit point. `Rejected` is one of two different
    /// things wearing one name, and telling them apart is the caller's next
    /// move:
    ///
    /// * the term it carries is **ahead** — this server is a stale leader and
    ///   steps down here;
    /// * the term is not ahead — the follower failed the consistency check, and
    ///   the leader retries at a shorter prefix. That retry is the caller's, not
    ///   this method's: it is a decision about what to send next, and sending is
    ///   not something a `Peer` does.
    ///
    /// **`term` is the term the request went out in**, and a success that does
    /// not name this server's current term is dropped.
    ///
    /// Without that check a reply is indistinguishable from any other: an
    /// `Accepted(3)` carries a length and nothing that says *when*. A leader
    /// that stepped down and was later re-elected could receive an
    /// acknowledgement sent during its earlier leadership, count it against the
    /// log it has now — which the terms in between may have rewritten — and
    /// commit a current-term entry at a reused index that the acknowledging
    /// follower has never held.
    ///
    /// The term is the caller's own record of what it sent, exactly as
    /// [`Peer::count_ballot`]'s is. The alternative is to put it on the wire,
    /// which would be better and is a protocol change; this is the same check
    /// in the only place that already knows the answer.
    ///
    /// Returns `Some(commit)` when the reply advanced replication and `None`
    /// when it did not.
    pub fn observe_appended(&self, from: Id, reply: Appended) -> Result<Option<u64>> {
        match reply {
            Appended::Accepted(ack) => {
                {
                    let g = self.inner.lock().expect("peer lock");
                    // **The term comes off the wire, not from the caller.** A
                    // reply that crossed a leadership boundary names the term it
                    // was accepted at, and this server is entitled to count it
                    // only against the term it is in now — the log of any term in
                    // between may have been rewritten.
                    if g.core.server.current_term != ack.term
                        || !g.core.leads()
                    {
                        // An acknowledgement of a log this server no longer has,
                        // or one it is no longer entitled to count.
                        return Ok(None);
                    }
                }
                self.record_match(from, ack.len).map(Some)
            },
            Appended::Rejected(seen) => {
                let mut g = self.inner.lock().expect("peer lock");
                self.step_down_to(&mut g, seen)?;
                Ok(None)
            },
        }
    }

    /// Adopt a strictly higher term, durably, and drop to follower.
    ///
    /// Shared by `request_vote` and `heartbeat`, because Raft's rule is about
    /// any RPC: *"if RPC request or response contains term T > currentTerm, set
    /// currentTerm = T, convert to follower"*.
    fn step_down_to(&self, g: &mut Inner, term: u64) -> Result<()> {
        let from_term = g.core.server.current_term;
        // The vote is cleared as the term advances, and both go down together:
        // the core hands them to the store and moves only if it took them. A
        // term that is not actually higher is nothing to do.
        let mut failed = None;
        match g.core.step_down(term, self.saver(&mut failed)) {
            Ok(true) => {
                g.log.push(Event::SteppedDown { from_term, to_term: term });
                Ok(())
            }
            Ok(false) => Ok(()),
            Err(_) => Err(self.down(g, term, failed)),
        }
    }

    /// **Stop standing, because somebody else won the term you are standing
    /// in.**
    ///
    /// `step_down_to`'s blind spot, and figure 2's rule for candidates: an
    /// append or a heartbeat at an *equal* term comes from the server that won
    /// it, so a candidate that lost a split vote learns it lost. Without this
    /// the loser stays a candidate in a term already decided and times out into
    /// terms nobody needed, which is a liveness defect rather than a safety one
    /// — but it is the defect that makes a split vote expensive.
    ///
    /// **Nothing is persisted, because nothing durable changes.** The term does
    /// not move and the vote is kept: this server voted in this term, and a
    /// restart must still find that vote. `Follower` is the role a restart
    /// produces anyway.
    ///
    /// A leader is left alone; [`crate::raft::steps::follow_fires`] says why.
    fn yield_at(&self, g: &mut Inner, term: u64) {
        let from_term = g.core.server.current_term;
        if g.core.yield_to(term) {
            g.log.push(Event::SteppedDown { from_term, to_term: term });
        }
    }
}

impl Consensus for Peer {
    async fn request_vote(
        &self,
        ctx: Context,
        term: u64,
        last_term: u64,
        last_index: u64,
    ) -> Result<Ballot> {
        let Some(candidate) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("peer lock");
        // Read under the lock, with everything else this decision depends on: a
        // summary taken before the lock is an answer about a log that may have
        // moved by the time the vote is granted.
        let (my_last_term, my_len) = self.summary()?;

        // A higher term is adopted before the request is judged, so the vote is
        // considered in the term it was asked about.
        self.step_down_to(&mut g, term)?;

        // **The up-to-date check**, and the one guard that exists for the log
        // rather than for the election: a later last term wins, and at equal
        // last terms the longer log wins. Without it a server missing committed
        // entries could be elected and then overwrite them — the reason the log
        // restricts elections rather than the other way round.
        let up_to_date =
            last_term > my_last_term || (last_term == my_last_term && last_index >= my_len);
        // A log that is not up to date is refused by the core, with the rest.

        // Re-granting the *same* vote to the *same* candidate is a
        // retransmission, not a second vote.
        //
        // This is the one place the service is deliberately outside the model's
        // transition rather than inside it. `tr_grant_vote` requires
        // `!has_voted`, so it cannot fire here — but the model's `votes` is a
        // *set*, and re-inserting a vote it already holds changes nothing. The
        // reply is therefore a repeat of an earlier reply, exactly as
        // `tr_issue_grant` is a repeat of an earlier grant in the ownership
        // model, and refusing it instead would lose a vote to any dropped
        // packet.
        let repeat = g.core.server.current_term == term && g.core.voted_for == Some(candidate);

        // Decide, persist, *then* reply. A server that replies first and dies has
        // voted twice in one term as far as the cluster is concerned, and two
        // candidates can then each hold a majority. The core persists before it
        // moves, and answers a repeat without touching the store.
        let mut failed = None;
        match g.core.grant(candidate, term, up_to_date, self.saver(&mut failed)) {
            Ok(VoteOutcome::Granted) => {
                if !repeat {
                    g.log.push(Event::Granted { term, to: candidate });
                }
                Ok(Ballot::Granted(term))
            }
            Err(_) => Err(self.down(&mut g, term, failed)),
            Ok(VoteOutcome::Refused) => {
                g.log.push(Event::RefusedVote { term, to: candidate });
                Ok(Ballot::Refused(g.core.server.current_term))
            }
        }
    }

    async fn append_entries(
        &self,
        ctx: Context,
        term: u64,
        prefix: u64,
        prev_term: u64,
        entry: LogEntry,
        leader_commit: u64,
    ) -> Result<Appended> {
        let Some(_leader) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("peer lock");
        // The consistency check reads the log, and the write that follows
        // depends on what it read, so both happen under the one lock.
        let my_len = self
            .entries
            .len()
            .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?;
        let prev = if prefix == 0 {
            None
        } else {
            self.entries
                .term_at(prefix - 1)
                .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?
        };

        // A higher term is adopted first, so the request is judged in its own
        // term.
        self.step_down_to(&mut g, term)?;

        // A stale leader is refused and told the current term.
        if term < g.core.server.current_term {
            g.log.push(Event::RefusedAppend { term, prefix });
            return Ok(Appended::Rejected(g.core.server.current_term));
        }

        // The term is this server's own, so the sender won it: a candidate
        // stops standing. This is the role change `tr_append_entries` makes on
        // its follower, and `theorem_an_append_makes_its_receiver_a_follower`
        // is the sentence saying the model makes it too.
        self.yield_at(&mut g, term);

        // **The consistency check.** The follower takes the entry only if it
        // already agrees with the leader on the one before it — which is what
        // makes agreement at one index imply agreement at every earlier one,
        // and is the whole mechanism Log Matching is about.
        let agrees = if prefix == 0 {
            true
        } else {
            prefix <= my_len && prev == Some(prev_term)
        };
        if !agrees {
            g.log.push(Event::RefusedAppend { term, prefix });
            return Ok(Appended::Rejected(g.core.server.current_term));
        }

        // **Delete the suffix only if the entry there conflicts.** Figure 2's
        // rule 3 says *if an existing entry conflicts with a new one (same
        // index, different terms), delete it and all that follow* — and the
        // conditional is the whole of it. An unconditional truncation loses
        // entries to a request that told the follower nothing new: replaying an
        // append for index 0 against a log of `[e0, e1]` would leave `[e0]`,
        // throwing away `e1` because a duplicate packet arrived late.
        //
        // The read and the write are under the one lock, because a second
        // request interleaving between them would be truncating against an
        // answer that was true a moment ago — the class of bug the consistency
        // check exists to prevent.
        let occupant = if prefix < my_len {
            self.entries
                .term_at(prefix)
                .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?
        } else {
            None
        };
        let new_len = if occupant == Some(entry.term) {
            // Already there. By Log Matching an entry is determined by its
            // `(index, term)`, so this is the same entry and everything after
            // it stays.
            my_len
        } else {
            self.entries
                .overwrite(prefix, entry)
                .map_err(|e| refuse_down(&format!("could not write the log: {e}")))?;
            prefix + 1
        };

        // **The commit point cannot exceed the log.** Raft forbids commit going
        // backwards, and a truncation below it would be a committed entry being
        // deleted — the thing Leader Completeness is supposed to rule out and
        // which this repository does not yet prove. So the clamp is a guard
        // against a state the protocol says is unreachable and the proofs do
        // not yet say so: better a commit point that retreats than one naming
        // entries that are not there.
        if g.commit > new_len {
            g.commit = new_len;
        }

        // `min(leaderCommit, index of the last new entry)`, and never
        // backwards.
        let learned = if leader_commit < new_len { leader_commit } else { new_len };
        if learned > g.commit {
            g.commit = learned;
        }
        g.log.push(Event::Accepted { term, prefix, len: new_len });
        // The term this follower accepted at, which is `term`: `follow_step`
        // refuses anything behind and steps up to anything ahead, so by here
        // `g.core.server.current_term == term`. Stating it from the server's own
        // record rather than from the argument, so the reply cannot claim a term
        // the follower is not actually in.
        Ok(Appended::Accepted(Acceptance { term: g.core.server.current_term, len: new_len }))
    }

    async fn heartbeat(&self, ctx: Context, term: u64, leader_commit: u64) -> Result<Standing> {
        let Some(_leader) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("peer lock");
        let my_len = self
            .entries
            .len()
            .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?;
        self.step_down_to(&mut g, term)?;
        // A heartbeat is an `append_entries` with nothing in it, so it demotes
        // a candidate of its own term for the same reason and by the same step.
        self.yield_at(&mut g, term);

        // And it carries the commit point for the same reason an append does.
        // A stale leader's is ignored: its term lost, and so did what it
        // believed was decided.
        if term == g.core.server.current_term {
            let learned = if leader_commit < my_len { leader_commit } else { my_len };
            if learned > g.commit {
                g.commit = learned;
            }
        }
        Ok(Standing {
            term: g.core.server.current_term,
            leading: g.core.leads(),
        })
    }

    async fn standing(&self, ctx: Context) -> Result<Standing> {
        if self.caller(&ctx).is_none() {
            return Err(refuse_no("unknown caller"));
        }
        let g = self.inner.lock().expect("peer lock");
        Ok(Standing {
            term: g.core.server.current_term,
            leading: g.core.leads(),
        })
    }
}
