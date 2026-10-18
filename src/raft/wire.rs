//! **The record encoding**: `Seq<Record>` down to the `Seq<u8>` a device holds.
//!
//! [`crate::raft::store`] speaks records; `vendor/verified-storage/pmemlog` appends bytes. This
//! is the layer between, and it exists to make one theorem statable:
//! [`crate::raft::proofs::wire::theorem_a_torn_tail_is_a_record_prefix`] — **any
//! byte prefix parses back to a record prefix**.
//!
//! That is the theorem the store's crash argument rests on. `store_recover` is
//! written in terms of a *record* prefix, which is what an append-only log of
//! records would give you; a real device gives you a *byte* prefix, and a byte
//! prefix can cut a record in half. Without this theorem the store's crash
//! model is a hope about how writes land. With it, a torn record is simply not
//! there, and what is left is a record sequence the store legitimately had.
//!
//! # Fixed width, on purpose
//!
//! Seventeen bytes: one tag, then two little-endian `u64`s. A length prefix or
//! a varint would be smaller and would make the parser's totality an argument
//! rather than an observation — `bytes.len() / 17` is where the records end,
//! and no byte of a half-written record can be mistaken for the start of a
//! whole one. A log format whose recovery depends on the parser being clever is
//! a log format whose recovery has a bug in it.
//!
//! # No checksum, which constrains where this format may be used
//!
//! `pmemlog` CRCs what it stores, so a second checksum here would add bytes and
//! no guarantee. But that CRC is also the only thing making a seventeen-byte
//! record safe at all, and the reason is worth stating because "8-byte chunks"
//! invites the wrong fix.
//!
//! pmemlog's crash model permits **any subset of 8-byte chunks** to have been
//! flushed, so a write spanning `n` chunks has `2^n` partial outcomes: no record
//! wider than eight bytes is atomic *however it is aligned*. Padding these to
//! twenty-four would touch three whole chunks instead of three partial ones and
//! buy nothing, since chunk 0 and chunk 2 can land while chunk 1 does not. A
//! record wider than a chunk is detectable-or-not, never atomic.
//!
//! So these records inherit detection from the log they ride inside. Written
//! straight to a device they would need a checksum of their own, and alignment
//! would not substitute for one. **This format is sound inside pmemlog's log and
//! not on bare storage** — a constraint, not an omission. See
//! `vendor/README.md`.
//!
//! # The 64-bit boundary, stated
//!
//! [`Record`]'s fields are `nat` — unbounded, because
//! [`crate::raft::model`]'s terms are unbounded and a model that caps them is
//! a model that has an overflow bug the protocol does not. Bytes are not
//! unbounded. So the round trip is proved **conditional on [`record_fits`]**,
//! and a store must not write a record that does not fit.
//!
//! This is a real limitation and it is stated rather than assumed away: a
//! cluster that reaches term 2^64, or a client value that does not fit in 64
//! bits, is outside what this encoding can represent. The theorems say so in
//! their preconditions instead of quietly truncating.
#![allow(unused_imports)]
// `n` in `le_to_u64_exec` and `decode_record_exec` exists for Verus: it is read
// only inside `assert`, which an ordinary build erases.
#![allow(unused_variables)]

use vstd::prelude::*;

use crate::raft::model::*;
use crate::raft::store::*;

verus! {

/// One tag byte and two little-endian `u64`s.
///
/// A **`const`**, not a `spec fn`, so the executable encoder and the
/// specification read the same number. `vendor/verified-storage/pmemlog` does the same with
/// `crc_size`, and it is the same lesson `accepted_commit` taught earlier on
/// this branch: two copies of one constant drift, and did.
pub const RECORD_LEN: usize = 17;

/// `Record::Append`'s tag.
pub const TAG_APPEND: u8 = 0;

/// `Record::Truncate`'s tag.
pub const TAG_TRUNCATE: u8 = 1;

/// [`RECORD_LEN`] as a `nat`, for the specifications that count in `nat`.
pub open spec fn record_len() -> nat {
    RECORD_LEN as nat
}

/// [`TAG_APPEND`], for specifications.
pub open spec fn tag_append() -> u8 {
    TAG_APPEND
}

/// [`TAG_TRUNCATE`], for specifications.
pub open spec fn tag_truncate() -> u8 {
    TAG_TRUNCATE
}

// ---------------------------------------------------------------------------
// One `u64`
// ---------------------------------------------------------------------------

/// Eight bytes, least significant first.
pub open spec fn u64_to_le(x: u64) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
    ]
}

/// And back.
pub open spec fn le_to_u64(b: Seq<u8>) -> u64 {
    ((b[0] as u64) | ((b[1] as u64) << 8) | ((b[2] as u64) << 16) | ((b[3] as u64) << 24) | ((
    b[4] as u64) << 32) | ((b[5] as u64) << 40) | ((b[6] as u64) << 48) | ((b[7] as u64)
        << 56)) as u64
}

// ---------------------------------------------------------------------------
// One record
// ---------------------------------------------------------------------------

/// Seventeen bytes. `Truncate` pads its second field with zeroes rather than
/// being shorter, so that every record is the same size and the parser needs no
/// state.
pub open spec fn encode_record(r: Record) -> Seq<u8> {
    match r {
        Record::Append { term, value } => seq![tag_append()] + u64_to_le(term as u64) + u64_to_le(
            value as u64,
        ),
        Record::Truncate { len } => seq![tag_truncate()] + u64_to_le(len as u64) + u64_to_le(0),
    }
}

/// And back.
///
/// Anything that is not [`tag_append`] is read as a truncation. A device this
/// store wrote holds only the two tags; a device it did not is not this store's
/// device, and the parser's job is to be **total**, not to adjudicate. Totality
/// is what makes recovery unable to fail.
pub open spec fn decode_record(b: Seq<u8>) -> Record {
    if b[0] == tag_append() {
        Record::Append {
            term: le_to_u64(b.subrange(1, 9)) as nat,
            value: le_to_u64(b.subrange(9, 17)) as nat,
        }
    } else {
        Record::Truncate { len: le_to_u64(b.subrange(1, 9)) as nat }
    }
}

// ---------------------------------------------------------------------------
// The device
// ---------------------------------------------------------------------------

/// Every record, in order, concatenated.
///
/// Folded front-to-back, unlike [`replay`], because that is the direction the
/// parser reads in and the two inductions have to meet.
pub open spec fn encode(rs: Seq<Record>) -> Seq<u8>
    decreases rs.len(),
{
    if rs.len() == 0 {
        Seq::<u8>::empty()
    } else {
        encode_record(rs[0]) + encode(rs.skip(1))
    }
}

/// **Read as many whole records as are there, and stop.**
///
/// The trailing fewer-than-seventeen bytes are dropped without comment, which
/// is the whole design: a torn write leaves a partial record, a partial record
/// is not a record, and recovery is not asked to decide what half a record
/// meant.
pub open spec fn parse(bytes: Seq<u8>) -> Seq<Record>
    decreases bytes.len(),
{
    if bytes.len() < record_len() {
        Seq::<Record>::empty()
    } else {
        seq![decode_record(bytes.take(record_len() as int))] + parse(
            bytes.skip(record_len() as int),
        )
    }
}

/// **The log a device's bytes mean**: parse, then replay.
///
/// This composition is what a recovering store computes, and the only thing it
/// computes. Nothing is reconciled and nothing is repaired.
pub open spec fn recovered_log(bytes: Seq<u8>) -> Seq<Entry> {
    replay(parse(bytes))
}

// ---------------------------------------------------------------------------
// The executable encoder
// ---------------------------------------------------------------------------

/// Eight bytes, least significant first.
pub fn u64_to_le_exec(x: u64) -> (out: Vec<u8>)
    ensures
        out@ == u64_to_le(x),
{
    let out: Vec<u8> = vec![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
    ];
    assert(out@ =~= u64_to_le(x));
    out
}

/// And back, from eight bytes starting at `at`.
pub fn le_to_u64_exec(b: &[u8], at: usize) -> (x: u64)
    requires
        at + 8 <= b@.len(),
    ensures
        x == le_to_u64(b@.subrange(at as int, at + 8)),
{
    // **Bind the length into a `usize` first.** The precondition `at + 8 <=
    // b@.len()` is `nat` arithmetic and says nothing to the exec checker about
    // `at + 1` overflowing a `usize`. Binding `b.len()` gives the same fact in a
    // form that does: `at + 8 <= n` with `n: usize` bounds every index below.
    let n = b.len();
    assert(at + 8 <= n);

    let x = (b[at] as u64) | ((b[at + 1] as u64) << 8) | ((b[at + 2] as u64) << 16) | ((b[at + 3]
        as u64) << 24) | ((b[at + 4] as u64) << 32) | ((b[at + 5] as u64) << 40) | ((b[at + 6]
        as u64) << 48) | ((b[at + 7] as u64) << 56);
    assert(b@.subrange(at as int, at + 8).len() == 8);
    x
}

/// **Append one record's seventeen bytes to `out`.**
///
/// The primitive, taking `&mut Vec<u8>` rather than returning one, so
/// [`encode_exec`]'s loop needs no `Vec::append` and no inner copy loop —
/// the bytes go straight where they are wanted.
///
/// Seventeen direct pushes rather than a loop over [`u64_to_le_exec`], because
/// [`u64_to_le`] is a `seq![..]` literal and the postcondition then falls out by
/// extensionality. A copy loop would need an invariant to say the same thing,
/// and this is code that cannot be run locally.
pub fn push_record_exec(out: &mut Vec<u8>, r: ExecRecord)
    ensures
        final(out)@ == old(out)@ + encode_record(r.view()),
{
    let ghost before = out@;
    // A truncation's second field is padding, and `encode_record` writes zero
    // there, so this is the one place the two shapes differ.
    let tag = if r.is_truncate {
        TAG_TRUNCATE
    } else {
        TAG_APPEND
    };
    let b = if r.is_truncate {
        0u64
    } else {
        r.b
    };
    let a = r.a;

    out.push(tag);
    out.push((a & 0xff) as u8);
    out.push(((a >> 8) & 0xff) as u8);
    out.push(((a >> 16) & 0xff) as u8);
    out.push(((a >> 24) & 0xff) as u8);
    out.push(((a >> 32) & 0xff) as u8);
    out.push(((a >> 40) & 0xff) as u8);
    out.push(((a >> 48) & 0xff) as u8);
    out.push(((a >> 56) & 0xff) as u8);
    out.push((b & 0xff) as u8);
    out.push(((b >> 8) & 0xff) as u8);
    out.push(((b >> 16) & 0xff) as u8);
    out.push(((b >> 24) & 0xff) as u8);
    out.push(((b >> 32) & 0xff) as u8);
    out.push(((b >> 40) & 0xff) as u8);
    out.push(((b >> 48) & 0xff) as u8);
    out.push(((b >> 56) & 0xff) as u8);
    assert(out@ =~= before + encode_record(r.view()));
}

/// One record's bytes, on their own.
pub fn encode_record_exec(r: ExecRecord) -> (out: Vec<u8>)
    ensures
        out@ == encode_record(r.view()),
        out@.len() == record_len(),
{
    let mut out: Vec<u8> = Vec::with_capacity(RECORD_LEN);
    push_record_exec(&mut out, r);
    assert(out@ =~= encode_record(r.view()));
    out
}

/// **Read one record from `at`.**
///
/// The padding a `Truncate` carries is not preserved, because the ghost
/// [`Record`] has no field for it — and `encode_record` writes zero there, so a
/// device this store wrote round-trips byte for byte anyway.
pub fn decode_record_exec(bytes: &[u8], at: usize) -> (r: ExecRecord)
    requires
        at + 17 <= bytes@.len(),
    ensures
        r.view() == decode_record(bytes@.subrange(at as int, at + 17)),
{
    // Same reason as in `le_to_u64_exec`: the `nat` precondition does not bound
    // the `usize` additions, and binding the length does.
    let n = bytes.len();
    assert(at + RECORD_LEN <= n);

    let tag = bytes[at];
    let a = le_to_u64_exec(bytes, at + 1);
    let b = le_to_u64_exec(bytes, at + 9);
    proof {
        let sub = bytes@.subrange(at as int, at + 17);
        assert(sub[0] == tag);
        assert(sub.subrange(1, 9) =~= bytes@.subrange(at + 1, at + 9));
        assert(sub.subrange(9, 17) =~= bytes@.subrange(at + 9, at + 17));
    }
    if tag == TAG_APPEND {
        ExecRecord { is_truncate: false, a, b }
    } else {
        ExecRecord { is_truncate: true, a, b: 0 }
    }
}

/// **Every record's bytes, in order** — the device a store with these records
/// would hold.
pub fn encode_exec(records: &[ExecRecord]) -> (out: Vec<u8>)
    ensures
        out@ == encode(record_seq(records@)),
{
    let ghost rs = record_seq(records@);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(rs.skip(0) =~= rs);
        assert(out@ + encode(rs) =~= encode(rs));
    }

    while i < records.len()
        invariant
            i <= records@.len(),
            rs == record_seq(records@),
            out@ + encode(rs.skip(i as int)) == encode(rs),
        decreases records@.len() - i as int,
    {
        let ghost before = out@;
        push_record_exec(&mut out, records[i]);
        proof {
            // `encode` folds front-to-back, so one step off the remainder is one
            // record's bytes and the rest.
            assert(rs.skip(i as int)[0] == records@[i as int].view());
            assert(rs.skip(i as int).skip(1) =~= rs.skip(i + 1));
            assert(encode(rs.skip(i as int)) =~= encode_record(records@[i as int].view()) + encode(
                rs.skip(i + 1),
            ));
            assert(out@ =~= before + encode_record(records@[i as int].view()));
            assert(out@ + encode(rs.skip(i + 1)) =~= before + encode(rs.skip(i as int)));
        }
        i += 1;
    }
    proof {
        assert(rs.skip(i as int) =~= Seq::<Record>::empty());
        assert(encode(rs.skip(i as int)) =~= Seq::<u8>::empty());
        assert(out@ =~= encode(rs));
    }
    out
}

/// **Read as many whole records as are there, and stop.**
///
/// The executable [`parse`], and what a recovering store runs on the bytes a
/// device hands back. The trailing fewer-than-seventeen bytes are dropped
/// without comment, which is C32: a torn write leaves a partial record, and a
/// partial record is not a record.
pub fn parse_exec(bytes: &[u8]) -> (out: Vec<ExecRecord>)
    ensures
        record_seq(out@) == parse(bytes@),
{
    let mut out: Vec<ExecRecord> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(bytes@.skip(0) =~= bytes@);
        assert(record_seq(out@) =~= Seq::<Record>::empty());
        assert(record_seq(out@) + parse(bytes@.skip(0)) =~= parse(bytes@));
    }

    // `17 <= bytes.len() - i` rather than `i + 17 <= bytes.len()`: the
    // invariant gives `i <= len`, so the subtraction is safe, while the
    // addition could overflow `usize` for a device near the address space.
    while RECORD_LEN <= bytes.len() - i
        invariant
            i <= bytes@.len(),
            record_seq(out@) + parse(bytes@.skip(i as int)) == parse(bytes@),
        decreases bytes@.len() - i as int,
    {
        let ghost before = out@;
        let r = decode_record_exec(bytes, i);
        proof {
            let b = bytes@.skip(i as int);
            assert(b.len() >= record_len());
            assert(b.take(record_len() as int) =~= bytes@.subrange(i as int, i + 17));
            assert(b.skip(record_len() as int) =~= bytes@.skip(i + 17));
            assert(parse(b) =~= seq![decode_record(bytes@.subrange(i as int, i + 17))] + parse(
                bytes@.skip(i + 17),
            ));
        }
        out.push(r);
        proof {
            assert(record_seq(out@) =~= record_seq(before) + seq![r.view()]);
            assert(record_seq(out@) + parse(bytes@.skip(i + 17)) =~= record_seq(before) + parse(
                bytes@.skip(i as int),
            ));
        }
        i += RECORD_LEN;
    }
    proof {
        assert(bytes@.skip(i as int).len() < record_len());
        assert(parse(bytes@.skip(i as int)) =~= Seq::<Record>::empty());
        assert(record_seq(out@) =~= parse(bytes@));
    }
    out
}

} // verus!
