//! **The encoding's theorems**: the round trip, and the torn tail.
//!
//! Two results, and the second is the one that matters.
//!
//! [`theorem_parse_of_encode`] is the round trip: what was written is what is
//! read. Necessary, and not interesting — an encoding that failed this would be
//! broken in a way testing finds in a minute.
//!
//! [`theorem_a_torn_tail_is_a_record_prefix`] is the one that is hard to test
//! and easy to get wrong: **cut the bytes anywhere and what parses is a prefix
//! of the records**. Anywhere. Not at a record boundary, not at a boundary the
//! device promised — anywhere at all, including the middle of a `u64`.
//!
//! That is what `crate::raft::store`'s crash argument needs and cannot state
//! for itself. `store_recover` is written over a *record* prefix; a device
//! hands back a *byte* prefix; and a byte prefix can cut a record in half. This
//! theorem is the bridge, and without it the store's crash model would be an
//! assumption about how writes land dressed up as a definition.
//!
//! It is proved for **every** `k`, not for multiples of seventeen, which is the
//! whole point: the fixed width means a half-written record cannot be mistaken
//! for a whole one, so recovery does not need the device to tear tidily.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::raft::model::*;
// A **glob**, not `use ...::theorem_the_store_always_agrees`. A `proof fn` is
// erased when `verus!` expands for an ordinary build, so a named import of one
// resolves under Verus and fails under `cargo build` — which is how the
// services job found this and the proof job did not. A glob import of an
// absent name is not an error.
use crate::raft::proofs::store::*;
use crate::raft::store::*;
use crate::raft::wire::*;

verus! {

/// **`record_len()` is seventeen.**
///
/// Trivial, and needed. `record_len()` is now `RECORD_LEN as nat` rather than a
/// bare literal — so that the executable encoder and the specification read the
/// same constant — and the `by (nonlinear_arith)` steps below want the value,
/// not the definition. Stating it once as a lemma is cheaper than hoping each
/// solver call unfolds the cast.
pub proof fn lemma_record_len_is_seventeen()
    ensures
        record_len() == 17,
        record_len() as int == 17,
{
    assert(RECORD_LEN == 17);
}

// ---------------------------------------------------------------------------
// Sequence plumbing
// ---------------------------------------------------------------------------

/// Taking the first part of a concatenation gives the first part back.
pub proof fn lemma_take_the_front(a: Seq<u8>, b: Seq<u8>)
    ensures
        (a + b).take(a.len() as int) == a,
        (a + b).skip(a.len() as int) == b,
{
    assert((a + b).take(a.len() as int) =~= a);
    assert((a + b).skip(a.len() as int) =~= b);
}

/// Cutting a concatenation inside its first part cuts the first part.
pub proof fn lemma_cut_inside_the_front(a: Seq<u8>, b: Seq<u8>, k: int)
    requires
        0 <= k <= a.len(),
    ensures
        (a + b).take(k) == a.take(k),
{
    assert((a + b).take(k) =~= a.take(k));
}

/// Cutting a concatenation past its first part keeps all of it and cuts the
/// second.
pub proof fn lemma_cut_past_the_front(a: Seq<u8>, b: Seq<u8>, k: int)
    requires
        a.len() <= k <= a.len() + b.len(),
    ensures
        (a + b).take(k) == a + b.take(k - a.len()),
{
    assert((a + b).take(k) =~= a + b.take(k - a.len()));
}

// ---------------------------------------------------------------------------
// One `u64`
// ---------------------------------------------------------------------------

/// **Eight bytes, least significant first, and back again.**
///
/// The one place in this repository where the solver is asked a question about
/// bits rather than about sequences. `by(bit_vector)` is not an escape hatch:
/// it is a second decision procedure for a decidable theory, and it proves the
/// goal rather than assuming it.
pub proof fn lemma_le_round_trip(x: u64)
    ensures
        le_to_u64(u64_to_le(x)) == x,
{
    let b = u64_to_le(x);
    assert(b.len() == 8);
    assert(le_to_u64(b) == ((((x & 0xff) as u8) as u64) | (((((x >> 8) & 0xff) as u8) as u64) << 8)
        | (((((x >> 16) & 0xff) as u8) as u64) << 16) | (((((x >> 24) & 0xff) as u8) as u64) << 24)
        | (((((x >> 32) & 0xff) as u8) as u64) << 32) | (((((x >> 40) & 0xff) as u8) as u64) << 40)
        | (((((x >> 48) & 0xff) as u8) as u64) << 48) | (((((x >> 56) & 0xff) as u8) as u64)
        << 56)) as u64);
    assert(((((x & 0xff) as u8) as u64) | (((((x >> 8) & 0xff) as u8) as u64) << 8) | (((((x >> 16)
        & 0xff) as u8) as u64) << 16) | (((((x >> 24) & 0xff) as u8) as u64) << 24) | (((((x >> 32)
        & 0xff) as u8) as u64) << 32) | (((((x >> 40) & 0xff) as u8) as u64) << 40) | (((((x >> 48)
        & 0xff) as u8) as u64) << 48) | (((((x >> 56) & 0xff) as u8) as u64) << 56)) as u64
        == x) by (bit_vector);
}

// ---------------------------------------------------------------------------
// One record
// ---------------------------------------------------------------------------

/// Every record is seventeen bytes, whichever it is. This is the property the
/// parser's totality rests on.
pub proof fn lemma_a_record_is_seventeen_bytes(r: Record)
    ensures
        encode_record(r).len() == record_len(),
{
}

/// **A record survives the round trip**, provided it fits — see
/// `crate::raft::wire`'s note on the 64-bit boundary.
pub proof fn lemma_a_record_round_trips(r: Record)
    requires
        record_fits(r),
    ensures
        decode_record(encode_record(r)) == r,
{
    match r {
        Record::Append { term, value } => {
            let a = u64_to_le(term as u64);
            let b = u64_to_le(value as u64);
            let bytes = seq![tag_append()] + a + b;
            assert(bytes[0] == tag_append());
            assert(bytes.subrange(1, 9) =~= a);
            assert(bytes.subrange(9, 17) =~= b);
            lemma_le_round_trip(term as u64);
            lemma_le_round_trip(value as u64);
            assert(le_to_u64(a) as nat == term);
            assert(le_to_u64(b) as nat == value);
        },
        Record::Truncate { len } => {
            let a = u64_to_le(len as u64);
            let bytes = seq![tag_truncate()] + a + u64_to_le(0);
            assert(bytes[0] == tag_truncate());
            assert(tag_truncate() != tag_append());
            assert(bytes.subrange(1, 9) =~= a);
            lemma_le_round_trip(len as u64);
            assert(le_to_u64(a) as nat == len);
        },
    }
}

// ---------------------------------------------------------------------------
// The device
// ---------------------------------------------------------------------------

/// The encoding is seventeen bytes per record, exactly.
///
/// Which is what makes `bytes.len() / 17` the record count, and the parser's
/// stopping condition an observation rather than an argument.
pub proof fn theorem_the_encoding_is_fixed_width(rs: Seq<Record>)
    ensures
        encode(rs).len() == rs.len() * record_len(),
    decreases rs.len(),
{
    lemma_record_len_is_seventeen();
    if rs.len() > 0 {
        theorem_the_encoding_is_fixed_width(rs.skip(1));
        lemma_a_record_is_seventeen_bytes(rs[0]);
    }
}

/// **What was written is what is read.**
pub proof fn theorem_parse_of_encode(rs: Seq<Record>)
    requires
        records_fit(rs),
    ensures
        parse(encode(rs)) == rs,
    decreases rs.len(),
{
    if rs.len() == 0 {
        assert(encode(rs) =~= Seq::<u8>::empty());
        assert(parse(encode(rs)) =~= rs);
    } else {
        let head = encode_record(rs[0]);
        let tail = encode(rs.skip(1));
        lemma_a_record_is_seventeen_bytes(rs[0]);
        assert(encode(rs) == head + tail);
        assert(encode(rs).len() >= record_len());

        lemma_take_the_front(head, tail);
        assert(encode(rs).take(record_len() as int) == head);
        assert(encode(rs).skip(record_len() as int) == tail);

        assert(records_fit(rs.skip(1))) by {
            assert forall|i: int| 0 <= i < rs.skip(1).len() implies record_fits(
                #[trigger] rs.skip(1)[i],
            ) by {
                assert(rs.skip(1)[i] == rs[i + 1]);
            }
        }
        assert(record_fits(rs[0]));
        lemma_a_record_round_trips(rs[0]);
        theorem_parse_of_encode(rs.skip(1));

        assert(parse(encode(rs)) =~= seq![rs[0]] + rs.skip(1));
        assert(seq![rs[0]] + rs.skip(1) =~= rs);
    }
}

/// **Cut the bytes anywhere and a record prefix comes back.**
///
/// The crash theorem. `k` is any byte count at all — a torn write lands where
/// it lands, and nothing in this statement asks it to land on a boundary. What
/// parses is the first `k / 17` records: every record whose bytes are all
/// there, and no part of one whose bytes are not.
///
/// Together with `crate::raft::proofs::store::theorem_a_crash_can_only_rewind`
/// this is the whole crash argument. A device hands back some prefix of the
/// bytes; that prefix is some prefix of the records; `replay` of a record
/// prefix is a log the store had. No step of that chain asks the device for
/// anything more than "you keep a prefix of what I wrote".
pub proof fn theorem_a_torn_tail_is_a_record_prefix(rs: Seq<Record>, k: int)
    requires
        records_fit(rs),
        0 <= k <= encode(rs).len(),
    ensures
        parse(encode(rs).take(k)) == rs.take(k / (record_len() as int)),
    decreases rs.len(),
{
    lemma_record_len_is_seventeen();
    theorem_the_encoding_is_fixed_width(rs);
    if rs.len() == 0 {
        assert(encode(rs) =~= Seq::<u8>::empty());
        assert(k == 0);
        assert(parse(encode(rs).take(k)) =~= rs.take(0));
    } else {
        let head = encode_record(rs[0]);
        let tail = encode(rs.skip(1));
        lemma_a_record_is_seventeen_bytes(rs[0]);
        assert(encode(rs) == head + tail);
        assert(head.len() == record_len());

        if k < record_len() as int {
            // Not even the first record is whole, so nothing parses — and
            // `k / 17` is zero, which is the same statement.
            lemma_cut_inside_the_front(head, tail, k);
            assert(encode(rs).take(k).len() == k);
            assert(encode(rs).take(k).len() < record_len());
            assert(k / (record_len() as int) == 0) by (nonlinear_arith)
                requires
                    0 <= k < record_len() as int,
            ;
            assert(parse(encode(rs).take(k)) =~= rs.take(0));
        } else {
            // The first record is whole. Peel it and recurse on the rest.
            lemma_cut_past_the_front(head, tail, k);
            assert(encode(rs).take(k) == head + tail.take(k - record_len() as int));

            let rest = head + tail.take(k - record_len() as int);
            assert(rest.len() >= record_len());
            lemma_take_the_front(head, tail.take(k - record_len() as int));
            assert(rest.take(record_len() as int) == head);
            assert(rest.skip(record_len() as int) == tail.take(k - record_len() as int));

            assert(records_fit(rs.skip(1))) by {
                assert forall|i: int| 0 <= i < rs.skip(1).len() implies record_fits(
                    #[trigger] rs.skip(1)[i],
                ) by {
                    assert(rs.skip(1)[i] == rs[i + 1]);
                }
            }
            assert(record_fits(rs[0]));
            lemma_a_record_round_trips(rs[0]);
            theorem_a_torn_tail_is_a_record_prefix(rs.skip(1), k - record_len() as int);

            // `(k - 17) / 17 == k / 17 - 1`, which is where the index bookkeeping
            // lands: one record consumed here, the rest by the recursion.
            assert((k - record_len() as int) / (record_len() as int) == k / (record_len() as int)
                - 1) by (nonlinear_arith)
                requires
                    record_len() as int <= k,
                    record_len() == 17,
            ;
            assert(parse(encode(rs).take(k)) =~= seq![rs[0]] + rs.skip(1).take(
                k / (record_len() as int) - 1,
            ));
            assert(seq![rs[0]] + rs.skip(1).take(k / (record_len() as int) - 1) =~= rs.take(
                k / (record_len() as int),
            ));
        }
    }
}

/// **Every reachable store is encodable, so the two halves compose.**
///
/// Codex's second finding, and what it was really about. `records_fit` began
/// life as a precondition on the theorems above, which sounds like a
/// statement about records and is really a statement about *which theorems may
/// be invoked*: a store could reach a state holding a record too wide to
/// write, and no invariant would have ruled it out — the encoding theorems
/// would simply have stopped applying, quietly, exactly where they were
/// needed.
///
/// `records_fit` is now a guard on the write transitions and a clause of
/// `store_inv`, so it holds of every reachable store, and this is the theorem
/// that spends it: take any store satisfying the invariant, and its device
/// round-trips through the encoding and survives a tear at any byte.
pub proof fn theorem_a_reachable_store_is_encodable(s: Store, k: int)
    requires
        store_inv(s),
        0 <= k <= encode(s.records).len(),
    ensures
        parse(encode(s.records)) == s.records,
        parse(encode(s.records).take(k)) == s.records.take(k / (record_len() as int)),
        replay(parse(encode(s.records))) == s.log,
{
    theorem_parse_of_encode(s.records);
    theorem_a_torn_tail_is_a_record_prefix(s.records, k);
}

/// And the same for a whole run: no reachable store is unwritable.
pub proof fn theorem_no_reachable_store_is_unwritable(tr: Seq<Store>, i: int)
    requires
        tr.len() > 0,
        store_init(tr[0]),
        forall|n: int| 0 <= n < tr.len() - 1 ==> store_next(#[trigger] tr[n], tr[n + 1]),
        0 <= i < tr.len(),
    ensures
        records_fit(tr[i].records),
        parse(encode(tr[i].records)) == tr[i].records,
{
    theorem_the_store_always_agrees(tr);
    assert(store_inv(tr[i]));
    theorem_parse_of_encode(tr[i].records);
}

/// **The whole chain, in one statement.** Whatever prefix of the bytes a crash
/// leaves, the log recovered from it is `replay` of a prefix of the records
/// that were written — a log the store had, reached the way it reached it.
pub proof fn theorem_recovery_from_a_torn_device(rs: Seq<Record>, k: int)
    requires
        records_fit(rs),
        0 <= k <= encode(rs).len(),
    ensures
        exists|j: nat|
            j <= rs.len() && recovered_log(encode(rs).take(k)) == #[trigger] replay(
                rs.take(j as int),
            ),
{
    lemma_record_len_is_seventeen();
    theorem_the_encoding_is_fixed_width(rs);
    theorem_a_torn_tail_is_a_record_prefix(rs, k);
    let j = (k / (record_len() as int)) as nat;
    assert(j <= rs.len()) by (nonlinear_arith)
        requires
            0 <= k <= rs.len() * record_len(),
            record_len() == 17,
            j == k / (record_len() as int),
    ;
    assert(recovered_log(encode(rs).take(k)) == replay(rs.take(j as int)));
}

} // verus!
