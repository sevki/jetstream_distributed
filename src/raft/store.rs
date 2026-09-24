//! **The durable log**: how a log that truncates lives on a device that cannot.
//!
//! Raft's log shrinks. Figure 2's rule 3 says *if an existing entry conflicts
//! with a new one, delete it and all that follow*, and
//! [`crate::raft::model::appended_log`] is that rule. Every durable log worth
//! trusting grows: `vendor/pmemlog`'s `AbstractInfiniteLogState` offers
//! `append` and `advance_head` — put bytes on the end, or forget bytes from the
//! front — and nothing that takes the tail back. That is not an oversight in
//! the vendored crate. It is what makes a crash-consistent log cheap: an append
//! that either happened or did not is one write; a tail that moves backwards is
//! a state the device has to be able to be caught in the middle of.
//!
//! So the tail does not move. This module is the reconciliation, and it is four
//! lines of idea:
//!
//! 1. the device holds a sequence of [`Record`]s, and only ever grows;
//! 2. a truncation is a *record*, [`Record::Truncate`], appended like any other;
//! 3. the log is [`replay`] of the records, computed on recovery;
//! 4. therefore the physical log is append-only and the logical log truncates.
//!
//! # What this buys, precisely
//!
//! * **Recovery needs no guessing.** [`store_recover`] *defines* the recovered
//!   log as `replay` of what survived, and [`theorem_recovery_is_exact`] is what
//!   makes that a definition rather than a hope: the in-memory log equals
//!   `replay` of the device at every point, so rebuilding it loses nothing that
//!   was written.
//! * **A crash can only rewind.** The device keeps a prefix; `replay` is total
//!   on every prefix; so what comes back is a log the store had, not a log no
//!   sequence of writes could produce.
//! * **Accepting an entry that is already there costs nothing.**
//!   [`theorem_accepting_an_entry_is_at_most_two_records`] says the no-conflict
//!   branch of `appended_log` writes *zero* records. That is the same
//!   conditional that `crate::raft::proofs::history` needed for Log Matching,
//!   showing up again as an operational fact: the check that makes the protocol
//!   safe is the check that makes the common case free.
//! * **Truncation is O(1) writes.** One record, whatever it deletes.
//!
//! # What it costs
//!
//! The device grows even when the log does not: a follower that thrashes
//! between two leaders writes a record per round and the log never shrinks by
//! itself. [`compacted`] is the way out — [`theorem_compaction_replays_the_same`]
//! says any record log is equivalent to one with no truncations in it, so a
//! store can rewrite itself as pure appends and let `advance_head` reclaim
//! what came before. This module proves the rewrite is sound; it does not
//! schedule it, and a store that never compacts grows without bound. That is a
//! stated limitation, not a hidden one.
//!
//! # What is modelled here and what is not
//!
//! Records, not bytes. `pmemlog` appends `Seq<u8>` and this module speaks
//! `Seq<Record>`; the encoding between them — and the theorem that any *byte*
//! prefix parses back to a record prefix — is the next layer down and is not
//! written yet. Until it is, nothing in this repository depends on
//! `vendor/pmemlog`, and the two corruption assumptions listed in its README
//! are not yet assumptions of anything proved here.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::raft::model::*;

verus! {

// ---------------------------------------------------------------------------
// What goes on the device
// ---------------------------------------------------------------------------

/// One thing written to the device.
///
/// Both variants are *appends*. That is the whole design: there is no record
/// that rewrites or removes an earlier one, so the device's job is the one job
/// a crash-consistent device can do well.
pub enum Record {
    /// One entry, at the end of whatever the log currently holds.
    Append { term: Term, value: nat },
    /// Everything from index `len` onwards is gone.
    ///
    /// Note what this does *not* say: it names no entry, and it is not a
    /// deletion of any particular record. It is a statement about the log that
    /// `replay` is building, made at the point in the sequence where it was
    /// written — which is why a later `Append` can put entries back above `len`
    /// and an earlier one is unaffected.
    Truncate { len: nat },
}

/// **The log is what the records replay to.**
///
/// Left fold over the device, oldest first. Written back-to-front — `drop_last`
/// and `last` — rather than front-to-back, because that is the direction an
/// append extends in, and it makes [`theorem_an_append_is_one_record`] hold by
/// unfolding rather than by induction.
///
/// A `Truncate` past the end is a no-op rather than an error: `min_nat` clamps
/// it. A store that writes one has a bug, but `replay` has to be **total** —
/// every prefix of a device has to mean something, because a crash can leave
/// any of them, and a recovery that can fail on a legal device state is a
/// recovery that cannot be trusted.
pub open spec fn replay(records: Seq<Record>) -> Seq<Entry>
    decreases records.len(),
{
    if records.len() == 0 {
        Seq::<Entry>::empty()
    } else {
        replay_step(replay(records.drop_last()), records.last())
    }
}

/// **One record applied to the log in hand.**
///
/// Split out of [`replay`] so that the executable [`apply_record`] can state
/// its postcondition against the log it was given rather than against a ghost
/// record sequence it would have to be handed. That matters beyond tidiness:
/// a function taking a `Ghost` argument cannot be called from ordinary Rust,
/// and the whole point of the executable layer is that the service calls it.
pub open spec fn replay_step(log: Seq<Entry>, r: Record) -> Seq<Entry> {
    match r {
        Record::Append { term, value } => log.push(Entry { term, value }),
        Record::Truncate { len } => log.take(min_nat(len, log.len()) as int),
    }
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

/// A server's log, in memory and on the device.
pub struct Store {
    /// What the server believes its log is, and answers questions from.
    pub log: Seq<Entry>,
    /// What is on the device, oldest record first. **Only ever grows**, which
    /// is [`theorem_the_device_is_append_only`].
    pub records: Seq<Record>,
}

/// **The one invariant**: memory agrees with the device.
///
/// Everything else in this module is about preserving it. It is what makes
/// [`store_recover`]'s definition of the recovered log a definition of the
/// *right* log rather than of some other log that happens to be computable.
pub open spec fn store_inv(s: Store) -> bool {
    s.log == replay(s.records)
}

/// A fresh store: no entries, no records.
pub open spec fn store_init(s: Store) -> bool {
    &&& s.log == Seq::<Entry>::empty()
    &&& s.records == Seq::<Record>::empty()
}

/// The store appends one entry.
pub open spec fn store_append(pre: Store, post: Store, e: Entry) -> bool {
    &&& post.records == pre.records.push(Record::Append { term: e.term, value: e.value })
    &&& post.log == pre.log.push(e)
}

/// The store cuts its log back to `len` entries.
///
/// `len <= pre.log.len()` is a guard and not a clamp: a store asking to
/// truncate past its own tail has misunderstood something, and the model should
/// say so rather than quietly do nothing. [`replay`] clamps anyway, because it
/// has to be total on device states this transition cannot produce — a device
/// is not only written by a correct store.
pub open spec fn store_truncate(pre: Store, post: Store, len: nat) -> bool {
    &&& len <= pre.log.len()
    &&& post.records == pre.records.push(Record::Truncate { len })
    &&& post.log == pre.log.take(len as int)
}

/// **The store crashes and comes back.**
///
/// `survived` is how many records reached the device: a crash keeps a
/// *prefix*, because that is what an append-only device offers and what
/// `pmemlog`'s write restriction enforces. The recovered log is not guessed,
/// reconciled or repaired — it is `replay` of what is there.
///
/// Nothing here says `survived == pre.records.len()`. A crash may lose the last
/// write, or the last ten; [`theorem_a_crash_can_only_rewind`] is what says
/// that whatever it loses, what comes back is a log the store legitimately had.
pub open spec fn store_recover(pre: Store, post: Store, survived: nat) -> bool {
    &&& survived <= pre.records.len()
    &&& post.records == pre.records.take(survived as int)
    &&& post.log == replay(post.records)
}

/// Any of the three.
pub open spec fn store_next(pre: Store, post: Store) -> bool {
    ||| exists|e: Entry| store_append(pre, post, e)
    ||| exists|len: nat| store_truncate(pre, post, len)
    ||| exists|survived: nat| store_recover(pre, post, survived)
}

// ---------------------------------------------------------------------------
// Accepting a replicated entry
// ---------------------------------------------------------------------------

/// **What a follower writes when it accepts one entry at `prefix`.**
///
/// The two branches are exactly `appended_log`'s, and the point of writing them
/// side by side is what the first branch costs: *nothing*. When the entry
/// already there carries the leader's term, figure 2's rule 3 does not fire,
/// the log does not change, and the device is not touched. A duplicate or
/// reordered `AppendEntries` — which is most of them, in a healthy cluster
/// under heartbeats — is a read and no write at all.
///
/// The other branch is two records and never more, whatever the size of the
/// tail it deletes.
pub open spec fn accept_records(follower: Seq<Entry>, leader: Seq<Entry>, prefix: nat) -> Seq<
    Record,
> {
    if prefix < follower.len() && follower[prefix as int].term == leader[prefix as int].term {
        Seq::<Record>::empty()
    } else {
        seq![
            Record::Truncate { len: prefix },
            Record::Append {
                term: leader[prefix as int].term,
                value: leader[prefix as int].value,
            },
        ]
    }
}

// ---------------------------------------------------------------------------
// Compaction
// ---------------------------------------------------------------------------

/// The same log, written as nothing but appends.
///
/// What a store rewrites itself to when the record count has outgrown the
/// entry count. [`theorem_compaction_replays_the_same`] is the soundness of
/// that rewrite; `pmemlog`'s `advance_head` is what then reclaims the records
/// before it.
pub open spec fn compacted(log: Seq<Entry>) -> Seq<Record>
    decreases log.len(),
{
    if log.len() == 0 {
        Seq::<Record>::empty()
    } else {
        compacted(log.drop_last()).push(
            Record::Append { term: log.last().term, value: log.last().value },
        )
    }
}

// ---------------------------------------------------------------------------
// The executable layer
// ---------------------------------------------------------------------------

/// A record, at `u64`.
///
/// One struct with a tag rather than an enum with two shapes, because that is
/// what goes on the wire — see `crate::raft::wire`, where every record is the
/// same seventeen bytes and a `Truncate`'s second field is padding. Keeping the
/// executable form the same shape as the encoded form means the encoder has no
/// case analysis of its own to get wrong.
#[derive(Clone, Copy)]
pub struct ExecRecord {
    /// `false` for an append, `true` for a truncation.
    pub is_truncate: bool,
    /// The term, or the new length.
    pub a: u64,
    /// The value, or padding.
    pub b: u64,
}

/// An entry, at `u64`.
#[derive(Clone, Copy)]
pub struct ExecEntry {
    pub term: u64,
    pub value: u64,
}

impl ExecRecord {
    /// The ghost record this stands for.
    pub open spec fn view(self) -> Record {
        if self.is_truncate {
            Record::Truncate { len: self.a as nat }
        } else {
            Record::Append { term: self.a as nat, value: self.b as nat }
        }
    }
}

impl ExecEntry {
    /// The ghost entry this stands for.
    pub open spec fn view(self) -> Entry {
        Entry { term: self.term as nat, value: self.value as nat }
    }
}

/// A sequence of executable records, as ghost records.
pub open spec fn record_seq(v: Seq<ExecRecord>) -> Seq<Record> {
    v.map_values(|r: ExecRecord| r.view())
}

/// A sequence of executable entries, as ghost entries.
pub open spec fn entry_seq(v: Seq<ExecEntry>) -> Seq<Entry> {
    v.map_values(|e: ExecEntry| e.view())
}

/// Drop everything from `len` onwards.
///
/// Written as a pop loop rather than `Vec::truncate` so that the postcondition
/// is proved from `Vec`'s own `pop` specification and nothing else. It is the
/// same work either way; this way the proof does not depend on which `Vec`
/// methods the standard library happens to have specifications for.
pub fn truncate_to(out: &mut Vec<ExecEntry>, len: usize)
    requires
        len <= old(out).len(),
    ensures
        final(out)@ == old(out)@.take(len as int),
{
    assert(old(out)@.take(old(out)@.len() as int) =~= old(out)@);
    while out.len() > len
        invariant
            len <= out@.len(),
            out@ == old(out)@.take(out@.len() as int),
        decreases out@.len() - len as int,
    {
        let ghost before = out@;
        let _ = out.pop();
        assert(out@ =~= before.drop_last());
        assert(old(out)@.take(out@.len() as int) =~= before.drop_last());
    }
}

/// **Apply one record to the log in hand.**
///
/// One step of [`replay`], executable. The postcondition is the spec function
/// applied to one more record, so `replay_exec`'s loop invariant is this
/// composed with itself and nothing else has to be re-argued.
pub fn apply_record(out: &mut Vec<ExecEntry>, r: ExecRecord)
    ensures
        entry_seq(final(out)@) == replay_step(entry_seq(old(out)@), r.view()),
{
    let ghost before = out@;
    if r.is_truncate {
        let target = if (r.a as usize) < out.len() {
            r.a as usize
        } else {
            out.len()
        };
        proof {
            // `min_nat` is what `replay_step` clamps with, and this is the same
            // choice made at `usize`.
            assert(entry_seq(before).len() == before.len());
            assert(min_nat(r.a as nat, entry_seq(before).len()) == target as nat);
        }
        truncate_to(out, target);
        assert(entry_seq(out@) =~= entry_seq(before).take(target as int));
    } else {
        out.push(ExecEntry { term: r.a, value: r.b });
        assert(entry_seq(out@) =~= entry_seq(before).push(
            Entry { term: r.a as nat, value: r.b as nat },
        ));
    }
}

/// **Rebuild the log from the device.**
///
/// What a recovering store runs, and the executable counterpart of [`replay`].
/// The postcondition says the two agree, which is what makes
/// `crate::raft::proofs::store`'s theorems statements about this code and not
/// only about a model of it.
pub fn replay_exec(records: &Vec<ExecRecord>) -> (out: Vec<ExecEntry>)
    ensures
        entry_seq(out@) == replay(record_seq(records@)),
{
    let mut out: Vec<ExecEntry> = Vec::new();
    assert(entry_seq(out@) =~= replay(record_seq(records@).take(0)));

    let mut i: usize = 0;
    while i < records.len()
        invariant
            i <= records@.len(),
            entry_seq(out@) == replay(record_seq(records@).take(i as int)),
        decreases records@.len() - i as int,
    {
        let r = records[i];
        proof {
            let rs = record_seq(records@).take(i as int);
            assert(record_seq(records@).take(i + 1) =~= rs.push(r.view()));
            assert(rs.push(r.view()).drop_last() =~= rs);
        }
        apply_record(&mut out, r);
        i = i + 1;
    }
    assert(record_seq(records@).take(records@.len() as int) =~= record_seq(records@));
    out
}

} // verus!
