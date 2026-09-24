//! **The durable log's theorems**: a log that truncates on a device that cannot.
//!
//! [`crate::raft::store`] claims four things. In order of how much they matter:
//!
//! 1. [`theorem_recovery_is_exact`] — memory and device never disagree, so
//!    rebuilding the log from the device loses nothing that was written. This
//!    is the one the other three are for.
//! 2. [`theorem_a_crash_can_only_rewind`] — what comes back after a crash is a
//!    log the store had, at the moment it had written that many records. A
//!    crash loses writes; it does not invent a state.
//! 3. [`theorem_accepting_an_entry_is_at_most_two_records`] — the model's
//!    `appended_log` is implementable here, at zero writes when the entry is
//!    already present and two when it is not.
//! 4. [`theorem_the_device_is_append_only`] — no normal operation moves the
//!    device's tail back, which is the property that lets this sit on
//!    `vendor/pmemlog` at all.
//!
//! Plus [`theorem_compaction_replays_the_same`], which is what stops the device
//! growing for ever.
//!
//! # A note on direction
//!
//! `replay` folds back-to-front (`drop_last`/`last`) and every induction here
//! goes the same way. That is not a style choice: an append extends the
//! *back*, so the fold's recursion and the operation's growth point are the
//! same place, and `theorem_an_append_is_one_record` falls out by unfolding
//! one step. Folded front-to-back it would need an induction over the whole
//! device for a fact about one write.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::raft::model::*;
use crate::raft::store::*;

verus! {

// ---------------------------------------------------------------------------
// One record at a time
// ---------------------------------------------------------------------------

/// **Appending an entry is appending one record.**
///
/// True by unfolding `replay` once — see the module note on direction.
pub proof fn theorem_an_append_is_one_record(records: Seq<Record>, e: Entry)
    ensures
        replay(records.push(Record::Append { term: e.term, value: e.value })) == replay(
            records,
        ).push(e),
{
    let rs = records.push(Record::Append { term: e.term, value: e.value });
    assert(rs.drop_last() =~= records);
    assert(replay(rs) =~= replay(records).push(e));
}

/// **Cutting the log back to `len` is appending one record**, whatever the size
/// of the tail it deletes.
pub proof fn theorem_a_truncation_is_one_record(records: Seq<Record>, len: nat)
    requires
        len <= replay(records).len(),
    ensures
        replay(records.push(Record::Truncate { len })) == replay(records).take(len as int),
{
    let rs = records.push(Record::Truncate { len });
    assert(rs.drop_last() =~= records);
    // The clamp in `replay` is inert here, which is the content of the
    // precondition: a store that respects `store_truncate`'s guard never
    // exercises it.
    assert(min_nat(len, replay(records).len()) == len);
    assert(replay(rs) =~= replay(records).take(len as int));
}

// ---------------------------------------------------------------------------
// Fitting
// ---------------------------------------------------------------------------

/// A fitting sequence plus a fitting record fits.
pub proof fn lemma_pushing_a_fitting_record_fits(rs: Seq<Record>, r: Record)
    requires
        records_fit(rs),
        record_fits(r),
    ensures
        records_fit(rs.push(r)),
{
    assert forall|i: int| 0 <= i < rs.push(r).len() implies record_fits(#[trigger] rs.push(r)[i]) by {
        if i < rs.len() {
            assert(rs.push(r)[i] == rs[i]);
        }
    }
}

/// And so does any prefix of one — which is what a crash leaves.
pub proof fn lemma_a_prefix_of_a_fitting_sequence_fits(rs: Seq<Record>, n: int)
    requires
        records_fit(rs),
        0 <= n <= rs.len(),
    ensures
        records_fit(rs.take(n)),
{
    assert forall|i: int| 0 <= i < rs.take(n).len() implies record_fits(#[trigger] rs.take(n)[i]) by {
        assert(rs.take(n)[i] == rs[i]);
    }
}

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// A fresh store agrees with its empty device.
pub proof fn theorem_a_fresh_store_agrees(s: Store)
    requires
        store_init(s),
    ensures
        store_inv(s),
{
    assert(replay(s.records) =~= Seq::<Entry>::empty());
}

/// **An append is a write and a sync**, and nothing else.
///
/// `store_append` is stated as one transition because that is what a caller
/// sees — `LogStore` promises durability before the method returns — and this
/// is the proof that the promise is kept by the two primitives the device
/// actually offers, rather than by a third thing the model made up.
pub proof fn theorem_an_append_is_a_write_then_a_sync(pre: Store, mid: Store, post: Store, e: Entry)
    requires
        store_write(pre, mid, Record::Append { term: e.term, value: e.value }),
        store_sync(mid, post),
    ensures
        store_append(pre, post, e),
{
    assert(mid.log == replay_step(pre.log, Record::Append { term: e.term, value: e.value }));
}

/// The same for a truncation.
pub proof fn theorem_a_truncation_is_a_write_then_a_sync(
    pre: Store,
    mid: Store,
    post: Store,
    len: nat,
)
    requires
        len <= pre.log.len(),
        store_write(pre, mid, Record::Truncate { len }),
        store_sync(mid, post),
    ensures
        store_truncate(pre, post, len),
{
    assert(min_nat(len, pre.log.len()) == len);
    assert(mid.log == replay_step(pre.log, Record::Truncate { len }));
}

/// **Recovery is exact.** Memory equals `replay` of the device before every
/// operation and after every operation — so the log rebuilt on recovery is the
/// log that was there, not a log that merely resembles it.
///
/// The `store_recover` case is the interesting one and it is interesting for
/// being trivial: `post.log == replay(post.records)` *is* the transition's
/// definition. That is the design working. Recovery does not have to reconcile
/// anything, because the device is the log and not a journal of intentions
/// about it.
pub proof fn theorem_recovery_is_exact(pre: Store, post: Store)
    requires
        store_inv(pre),
        store_next(pre, post),
    ensures
        store_inv(post),
{
    if exists|r: Record| store_write(pre, post, r) {
        let r = choose|r: Record| store_write(pre, post, r);
        assert(post.records.drop_last() =~= pre.records);
        lemma_pushing_a_fitting_record_fits(pre.records, r);
    } else if store_sync(pre, post) {
    } else if exists|e: Entry| store_append(pre, post, e) {
        let e = choose|e: Entry| store_append(pre, post, e);
        theorem_an_append_is_one_record(pre.records, e);
        lemma_pushing_a_fitting_record_fits(
            pre.records,
            Record::Append { term: e.term, value: e.value },
        );
    } else if exists|len: nat| store_truncate(pre, post, len) {
        let len = choose|len: nat| store_truncate(pre, post, len);
        theorem_a_truncation_is_one_record(pre.records, len);
        lemma_pushing_a_fitting_record_fits(pre.records, Record::Truncate { len });
    } else {
        // Recovery, where the invariant *is* the transition.
        assert(exists|survived: nat| store_recover(pre, post, survived));
        let survived = choose|survived: nat| store_recover(pre, post, survived);
        assert(store_recover(pre, post, survived));
        lemma_a_prefix_of_a_fitting_sequence_fits(pre.records, survived as int);
    }
}

// ---------------------------------------------------------------------------
// Durability
// ---------------------------------------------------------------------------

/// **Nothing reported durable is ever lost, by any transition, ever.**
///
/// The theorem the whole `durable` field exists for, and the one Raft needs:
/// a follower that answered `Accepted` has told its leader an entry is on
/// disk, and the leader may commit on the strength of that answer. If a
/// restart could take the entry back, the leader would have committed
/// something no longer written down — and Raft's safety argument would be
/// resting on a promise this layer did not keep.
///
/// Two clauses, and the second is the sharp one. The line never retreats, and
/// **everything below the line is unchanged, record for record**. A store that
/// kept the right *number* of records while rewriting one of them would
/// satisfy the first and fail the second.
pub proof fn theorem_durability_never_retreats(pre: Store, post: Store)
    requires
        store_inv(pre),
        store_next(pre, post),
    ensures
        post.durable >= pre.durable,
        post.records.take(pre.durable as int) == pre.records.take(pre.durable as int),
{
    if exists|r: Record| store_write(pre, post, r) {
        let r = choose|r: Record| store_write(pre, post, r);
        assert(post.records.take(pre.durable as int) =~= pre.records.take(pre.durable as int));
    } else if store_sync(pre, post) {
        assert(post.records.take(pre.durable as int) =~= pre.records.take(pre.durable as int));
    } else if exists|e: Entry| store_append(pre, post, e) {
        let e = choose|e: Entry| store_append(pre, post, e);
        assert(post.records.take(pre.durable as int) =~= pre.records.take(pre.durable as int));
    } else if exists|len: nat| store_truncate(pre, post, len) {
        let len = choose|len: nat| store_truncate(pre, post, len);
        assert(post.records.take(pre.durable as int) =~= pre.records.take(pre.durable as int));
    } else {
        assert(exists|survived: nat| store_recover(pre, post, survived));
        let survived = choose|survived: nat| store_recover(pre, post, survived);
        assert(store_recover(pre, post, survived));
        assert(post.records.take(pre.durable as int) =~= pre.records.take(pre.durable as int));
    }
}

/// **A crash keeps everything reported durable**, spelled out for the crash
/// alone since that is the transition anyone would doubt.
pub proof fn theorem_a_crash_keeps_everything_reported_durable(
    pre: Store,
    post: Store,
    survived: nat,
)
    requires
        store_inv(pre),
        store_recover(pre, post, survived),
    ensures
        post.records.len() >= pre.durable,
        post.records.take(pre.durable as int) == pre.records.take(pre.durable as int),
{
    assert(post.records.take(pre.durable as int) =~= pre.records.take(pre.durable as int));
}

/// The invariant survives any run./// The invariant survives any run.
pub proof fn theorem_the_store_always_agrees(tr: Seq<Store>)
    requires
        tr.len() > 0,
        store_init(tr[0]),
        forall|i: int| 0 <= i < tr.len() - 1 ==> store_next(#[trigger] tr[i], tr[i + 1]),
    ensures
        forall|i: int| 0 <= i < tr.len() ==> store_inv(#[trigger] tr[i]),
{
    assert forall|i: int| 0 <= i < tr.len() implies store_inv(#[trigger] tr[i]) by {
        lemma_prefix_agrees(tr, i);
    }
}

/// The induction behind [`theorem_the_store_always_agrees`], one index at a
/// time so that a failure names an index rather than a run.
proof fn lemma_prefix_agrees(tr: Seq<Store>, i: int)
    requires
        tr.len() > 0,
        store_init(tr[0]),
        forall|j: int| 0 <= j < tr.len() - 1 ==> store_next(#[trigger] tr[j], tr[j + 1]),
        0 <= i < tr.len(),
    ensures
        store_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        theorem_a_fresh_store_agrees(tr[0]);
    } else {
        lemma_prefix_agrees(tr, i - 1);
        assert(store_next(tr[i - 1], tr[i]));
        theorem_recovery_is_exact(tr[i - 1], tr[i]);
    }
}

// ---------------------------------------------------------------------------
// Crashes
// ---------------------------------------------------------------------------

/// **The device is append-only.** No normal operation moves its tail back: the
/// records that were there are still there, in order, at the same indices.
///
/// This is the property that lets the whole store sit on `vendor/pmemlog`,
/// whose `AbstractInfiniteLogState` offers `append` and `advance_head` and
/// nothing that shortens the tail. A `Record::Truncate` shortens the *log*; it
/// lengthens the device.
pub proof fn theorem_the_device_is_append_only(pre: Store, post: Store)
    requires
        (exists|e: Entry| store_append(pre, post, e)) || (exists|len: nat|
            store_truncate(pre, post, len)),
    ensures
        post.records.len() == pre.records.len() + 1,
        post.records.take(pre.records.len() as int) == pre.records,
{
    if exists|e: Entry| store_append(pre, post, e) {
        let e = choose|e: Entry| store_append(pre, post, e);
        assert(post.records.take(pre.records.len() as int) =~= pre.records);
    } else {
        let len = choose|len: nat| store_truncate(pre, post, len);
        assert(post.records.take(pre.records.len() as int) =~= pre.records);
    }
}

/// **A crash can only rewind.**
///
/// What comes back is `replay` of a prefix of the device — which is exactly the
/// log the store held at the moment it had written that many records, and it
/// took the same route to get there. Two things are being ruled out: a recovery
/// that produces a log no sequence of writes could have produced, and a
/// recovery that fails. `replay` is total on every sequence of records, so
/// there is no prefix a crash can leave that recovery cannot read.
///
/// The one hypothesis worth reading is that a crash keeps a *prefix*. That is
/// not free and it is not proved here — it is the property an append-only
/// device gives you, and on real hardware it is what `pmemlog`'s write
/// restriction enforces and what its corruption axioms rest on.
pub proof fn theorem_a_crash_can_only_rewind(pre: Store, post: Store, survived: nat)
    requires
        store_inv(pre),
        store_recover(pre, post, survived),
    ensures
        store_inv(post),
        post.records == pre.records.take(survived as int),
        post.log == replay(pre.records.take(survived as int)),
{
}

/// **Nothing before the crash point is lost.** A record that reached the device
/// is still the same record at the same index afterwards, so the recovered log
/// is built from the writes that survived and not from some reinterpretation of
/// them.
pub proof fn theorem_a_crash_keeps_what_reached_the_device(
    pre: Store,
    post: Store,
    survived: nat,
    i: int,
)
    requires
        store_recover(pre, post, survived),
        0 <= i < survived,
    ensures
        post.records[i] == pre.records[i],
{
}

// ---------------------------------------------------------------------------
// The Raft connection
// ---------------------------------------------------------------------------

/// **Accepting a replicated entry is at most two records**, and the model's
/// [`appended_log`] is what they replay to.
///
/// This is the theorem the module exists for: figure 2's rule 3, which deletes
/// a suffix, is implementable on a device that cannot delete anything.
///
/// Read the two branches for what they cost. The conflict branch is
/// `Truncate` then `Append` — two records, constant, however long the tail it
/// throws away. The other branch is **empty**: an `AppendEntries` whose entry
/// is already present writes nothing at all. That is not an optimisation bolted
/// on afterwards; it is the same conditional that
/// `crate::raft::proofs::history` needed to prove Log Matching, which is worth
/// noticing — the check that makes the protocol safe is the check that makes
/// the common case free.
pub proof fn theorem_accepting_an_entry_is_at_most_two_records(
    s: Store,
    leader: Seq<Entry>,
    prefix: nat,
)
    requires
        store_inv(s),
        prefix <= s.log.len(),
        prefix < leader.len(),
    ensures
        replay(s.records + accept_records(s.log, leader, prefix)) == appended_log(
            s.log,
            leader,
            prefix,
        ),
        accept_records(s.log, leader, prefix).len() <= 2,
{
    let follower = s.log;
    if prefix < follower.len() && follower[prefix as int].term == leader[prefix as int].term {
        // No conflict: no records, and `appended_log` leaves the log alone.
        assert(s.records + accept_records(follower, leader, prefix) =~= s.records);
    } else if prefix == follower.len() {
        // Extending. The marker would be the identity, so it is not written —
        // and `follower.take(follower.len())` is `follower`, which is why one
        // record lands on the same log two would have.
        let a = Record::Append {
            term: leader[prefix as int].term,
            value: leader[prefix as int].value,
        };
        assert(s.records + accept_records(follower, leader, prefix) =~= s.records.push(a));
        assert(Entry { term: leader[prefix as int].term, value: leader[prefix as int].value }
            == leader[prefix as int]);
        theorem_an_append_is_one_record(
            s.records,
            Entry { term: leader[prefix as int].term, value: leader[prefix as int].value },
        );
        assert(follower.take(prefix as int) =~= follower);
    } else {
        let t = Record::Truncate { len: prefix };
        let a = Record::Append {
            term: leader[prefix as int].term,
            value: leader[prefix as int].value,
        };
        assert(s.records + accept_records(follower, leader, prefix) =~= s.records.push(t).push(a));

        theorem_a_truncation_is_one_record(s.records, prefix);
        assert(replay(s.records.push(t)) == follower.take(prefix as int));

        // The entry the record carries is the leader's entry. Spelled out
        // because the record stores the two fields and not the struct, so
        // nothing tells Verus they are the same `Entry` unless it is asked.
        assert(Entry { term: leader[prefix as int].term, value: leader[prefix as int].value }
            == leader[prefix as int]);
        theorem_an_append_is_one_record(
            s.records.push(t),
            Entry { term: leader[prefix as int].term, value: leader[prefix as int].value },
        );
        assert(replay(s.records.push(t).push(a)) =~= follower.take(prefix as int).push(
            leader[prefix as int],
        ));
    }
}

/// **Extending the log costs one record, not two.**
///
/// The steady state of replication: a leader nobody is fighting sends entry
/// after entry at the end of the follower's log, and each one is a single
/// append. The marker a conflict would need is `Truncate { len: follower.len() }`,
/// which deletes nothing, and writing it anyway would double the cost of the
/// case that happens most.
pub proof fn theorem_extending_the_log_costs_one_record(
    follower: Seq<Entry>,
    leader: Seq<Entry>,
    prefix: nat,
)
    requires
        prefix == follower.len(),
        prefix < leader.len(),
    ensures
        accept_records(follower, leader, prefix).len() == 1,
        !(accept_records(follower, leader, prefix)[0] is Truncate),
{
}

/// The same, as a transition: a follower that accepts an entry lands with the
/// log the model says it should, and its device grew by at most two.
pub proof fn theorem_a_follower_accepts_with_at_most_two_writes(
    pre: Store,
    post: Store,
    leader: Seq<Entry>,
    prefix: nat,
)
    requires
        store_inv(pre),
        prefix <= pre.log.len(),
        prefix < leader.len(),
        post.records == pre.records + accept_records(pre.log, leader, prefix),
        post.log == appended_log(pre.log, leader, prefix),
        // It is a `LogStore` method, so it syncs before it answers. That is
        // what lets the follower reply `Accepted` — see
        // `theorem_a_follower_that_answers_accepted_has_written_it_down`.
        post.durable == post.records.len(),
    ensures
        store_inv(post),
        post.records.len() <= pre.records.len() + 2,
        post.records.take(pre.records.len() as int) == pre.records,
        post.durable >= pre.durable,
{
    theorem_accepting_an_entry_is_at_most_two_records(pre, leader, prefix);
    assert(post.records.take(pre.records.len() as int) =~= pre.records);
}

/// **A follower that answers `Accepted` has written the entry down**, and no
/// crash from there can take it back.
///
/// The sentence that connects this module to Raft's safety argument. A leader
/// counts an `Accepted` towards a majority and may commit on the strength of
/// it. This says the records the acceptance produced are below the durable
/// line by the time the answer goes out, so any legal recovery afterwards
/// returns the same device and the same log — not a prefix of it.
///
/// Take the `post.durable` hypothesis away — which is what `LogStore`'s
/// *"durable before it returns"* buys — and the conclusion fails immediately:
/// `survived` could be anything down to `pre.durable`, and the commit rule
/// would be counting a promise nobody made.
pub proof fn theorem_a_follower_that_answers_accepted_has_written_it_down(
    pre: Store,
    post: Store,
    later: Store,
    leader: Seq<Entry>,
    prefix: nat,
    survived: nat,
)
    requires
        store_inv(pre),
        prefix <= pre.log.len(),
        prefix < leader.len(),
        post.records == pre.records + accept_records(pre.log, leader, prefix),
        post.log == appended_log(pre.log, leader, prefix),
        // `LogStore`: durable before it returns.
        post.durable == post.records.len(),
        // And then a crash, at any point the model allows.
        store_recover(post, later, survived),
    ensures
        later.records == post.records,
        later.log == post.log,
{
    theorem_a_follower_accepts_with_at_most_two_writes(pre, post, leader, prefix);
    assert(survived == post.records.len());
    assert(later.records =~= post.records);
}

/// **A durable record is durable for ever.**
///
/// The same statement across a whole run rather than one step: a record below
/// the durable line at step `i` is the same record, at the same index, at
/// every step after it. Crashes included, however many of them.
///
/// This is what a leader is relying on when it commits, and it is the
/// difference between "a crash keeps a prefix" — which permits the empty
/// prefix — and a log worth building consensus on.
pub proof fn theorem_a_durable_record_is_durable_for_ever(
    tr: Seq<Store>,
    i: int,
    j: int,
    k: int,
)
    requires
        tr.len() > 0,
        store_init(tr[0]),
        forall|n: int| 0 <= n < tr.len() - 1 ==> store_next(#[trigger] tr[n], tr[n + 1]),
        0 <= i <= j < tr.len(),
        0 <= k < tr[i].durable,
    ensures
        k < tr[j].records.len(),
        tr[j].records[k] == tr[i].records[k],
        tr[j].durable >= tr[i].durable,
    decreases j - i,
{
    lemma_prefix_agrees(tr, i);
    if i == j {
    } else {
        lemma_prefix_agrees(tr, j - 1);
        theorem_a_durable_record_is_durable_for_ever(tr, i, j - 1, k);
        assert(store_next(tr[j - 1], tr[j]));
        theorem_durability_never_retreats(tr[j - 1], tr[j]);
        // The durable line at `j - 1` is at least the one at `i`, so index `k`
        // is below it, and what is below it is unchanged.
        assert(k < tr[j - 1].durable);
        assert(tr[j].records.take(tr[j - 1].durable as int) == tr[j - 1].records.take(
            tr[j - 1].durable as int,
        ));
        assert(tr[j].records.take(tr[j - 1].durable as int)[k] == tr[j].records[k]);
        assert(tr[j - 1].records.take(tr[j - 1].durable as int)[k] == tr[j - 1].records[k]);
    }
}

// ---------------------------------------------------------------------------
// Compaction
// ---------------------------------------------------------------------------

/// **Any log can be written as nothing but appends.**
///
/// Which is what stops the device growing for ever. A store whose record count
/// has outrun its entry count rewrites itself as `compacted(log)` — no
/// truncations, one record per entry — and `pmemlog`'s `advance_head` reclaims
/// everything before it.
///
/// This proves the rewrite is *sound*, and that is all it proves. Nothing here
/// schedules it, and a store that never compacts grows without bound. Said
/// plainly because the alternative is a reader assuming the bound exists.
pub proof fn theorem_compaction_replays_the_same(log: Seq<Entry>)
    ensures
        replay(compacted(log)) == log,
    decreases log.len(),
{
    if log.len() == 0 {
        assert(replay(compacted(log)) =~= log);
    } else {
        let head = log.drop_last();
        theorem_compaction_replays_the_same(head);
        theorem_an_append_is_one_record(compacted(head), log.last());
        assert(replay(compacted(log)) =~= head.push(log.last()));
        assert(head.push(log.last()) =~= log);
    }
}

/// **Appending a compacted log appends that log**, whatever was there before.
///
/// The induction the two compaction theorems below are built from. It is
/// stated over an arbitrary prefix `rs` rather than over the empty one because
/// that is the whole question: what the staged generation does to a device
/// that still holds the old one.
pub proof fn lemma_a_compacted_log_appends_itself(rs: Seq<Record>, log: Seq<Entry>)
    ensures
        replay(rs + compacted(log)) == replay(rs) + log,
    decreases log.len(),
{
    if log.len() == 0 {
        assert(rs + compacted(log) =~= rs);
        assert(replay(rs) + log =~= replay(rs));
    } else {
        let head = log.drop_last();
        let a = Record::Append { term: log.last().term, value: log.last().value };
        assert(a == Record::Append { term: log.last().term, value: log.last().value });
        assert(rs + compacted(log) =~= (rs + compacted(head)).push(a));

        lemma_a_compacted_log_appends_itself(rs, head);
        assert(Entry { term: log.last().term, value: log.last().value } == log.last());
        theorem_an_append_is_one_record(rs + compacted(head), log.last());
        assert(replay(rs + compacted(log)) =~= (replay(rs) + head).push(log.last()));
        assert((replay(rs) + head).push(log.last()) =~= replay(rs) + log);
    }
}

/// **A staged compaction is inert until the old generation is reclaimed.**
///
/// Codex's finding, and the sharpest of the three. Compaction on an
/// append-only device is two steps — write the new generation, reclaim the old
/// one — and a crash can land between them. Writing [`compacted`] alone would
/// leave `old_records ++ compacted(log)`, which replays to **`log + log`**:
/// the old generation still replays to `log`, and the new one appends it
/// again. `theorem_compaction_replays_the_same` would have been true and would
/// have licensed nothing, because it only covers the case where the rewrite
/// has already replaced what came before.
///
/// [`compaction_batch`]'s leading `Truncate { len: 0 }` is what fixes it. The
/// staged generation clears whatever preceded it, so the device replays to
/// `log` **with the old records still there**, which is this theorem, and to
/// `log` once they are gone, which is the next one. Both crash views agree,
/// and reclaiming becomes a no-op rather than a change.
pub proof fn theorem_a_staged_compaction_is_inert(records: Seq<Record>)
    ensures
        replay(records + compaction_batch(replay(records))) == replay(records),
{
    let log = replay(records);
    let cleared = records.push(Record::Truncate { len: 0 });
    assert(records + compaction_batch(log) =~= cleared + compacted(log));

    theorem_a_truncation_is_one_record(records, 0);
    assert(replay(cleared) =~= Seq::<Entry>::empty());

    lemma_a_compacted_log_appends_itself(cleared, log);
    assert(replay(cleared) + log =~= log);
}

/// **And once it has landed, the old generation is dead.**
///
/// The batch on its own replays to the same log, so dropping everything before
/// it changes nothing — which is exactly the licence to call `advance_head`.
/// Together with the theorem above: the device means `log` before the reclaim
/// and `log` after it, so a crash at either side of that step recovers the
/// same thing.
pub proof fn theorem_after_compaction_the_old_records_are_dead(records: Seq<Record>)
    ensures
        replay(compaction_batch(replay(records))) == replay(records),
        replay(compaction_batch(replay(records))) == replay(
            records + compaction_batch(replay(records)),
        ),
{
    let log = replay(records);
    let cleared = Seq::<Record>::empty().push(Record::Truncate { len: 0 });
    assert(compaction_batch(log) =~= cleared + compacted(log));

    theorem_a_truncation_is_one_record(Seq::<Record>::empty(), 0);
    assert(replay(cleared) =~= Seq::<Entry>::empty());

    lemma_a_compacted_log_appends_itself(cleared, log);
    assert(replay(cleared) + log =~= log);

    theorem_a_staged_compaction_is_inert(records);
}

/// The batch is one record longer than the log: the marker, then an append per
/// entry. So a store that compacts when the device outgrows the log by a
/// constant factor keeps the device within a constant factor of the log.
pub proof fn theorem_the_compaction_batch_is_one_longer_than_the_log(log: Seq<Entry>)
    ensures
        compaction_batch(log).len() == log.len() + 1,
{
    theorem_compaction_is_one_record_per_entry(log);
    assert(compaction_batch(log).len() == 1 + compacted(log).len());
}

/// **Compaction costs one record per entry, and no more.** The rewrite's size
/// is the log's size, so a store that compacts when the device outgrows the log
/// by a constant factor keeps the device within a constant factor of the log.
pub proof fn theorem_compaction_is_one_record_per_entry(log: Seq<Entry>)
    ensures
        compacted(log).len() == log.len(),
    decreases log.len(),
{
    if log.len() > 0 {
        theorem_compaction_is_one_record_per_entry(log.drop_last());
    }
}

/// And a compacted device has no truncation in it — which is what makes it
/// replayable by a reader that only understands appends, and what makes the
/// claim "the physical log is append-only" true of the *records* as well as of
/// the device.
pub proof fn theorem_compaction_leaves_no_truncations(log: Seq<Entry>)
    ensures
        forall|i: int|
            0 <= i < compacted(log).len() ==> !(#[trigger] compacted(log)[i] is Truncate),
    decreases log.len(),
{
    if log.len() > 0 {
        theorem_compaction_leaves_no_truncations(log.drop_last());
        let head = compacted(log.drop_last());
        assert forall|i: int|
            0 <= i < compacted(log).len() implies !(#[trigger] compacted(log)[i] is Truncate) by {
            if i < head.len() {
                assert(compacted(log)[i] == head[i]);
            }
        }
    }
}

} // verus!
