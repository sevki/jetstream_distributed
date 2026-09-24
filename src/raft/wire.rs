//! **The record encoding**: `Seq<Record>` down to the `Seq<u8>` a device holds.
//!
//! [`crate::raft::store`] speaks records; `vendor/pmemlog` appends bytes. This
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
//! No checksum here. That is not an omission: `pmemlog` CRCs what it stores and
//! its two corruption assumptions are what make that worth doing, so a second
//! checksum at this layer would add bytes and no guarantee.
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

use vstd::prelude::*;

use crate::raft::model::*;
use crate::raft::store::*;

verus! {

/// One tag byte and two little-endian `u64`s.
pub open spec fn record_len() -> nat {
    17
}

/// `Record::Append`'s tag.
pub open spec fn tag_append() -> u8 {
    0
}

/// `Record::Truncate`'s tag.
pub open spec fn tag_truncate() -> u8 {
    1
}

/// **Whether a record can be written at all.** See the module note on the
/// 64-bit boundary.
pub open spec fn record_fits(r: Record) -> bool {
    match r {
        Record::Append { term, value } => term <= u64::MAX && value <= u64::MAX,
        Record::Truncate { len } => len <= u64::MAX,
    }
}

/// Every record in the sequence fits.
pub open spec fn records_fit(rs: Seq<Record>) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> record_fits(#[trigger] rs[i])
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

} // verus!
