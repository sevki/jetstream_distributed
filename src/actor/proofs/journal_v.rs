//! The journal's arithmetic: what counting and folding do when an entry is
//! pushed, and how a count grows along a prefix.
//!
//! Pure facts about `Seq<Entry>`, with no actor, no ownership and no step in
//! sight. [`crate::actor::proofs::invariant`] spends them.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;

use crate::actor::model::*;
use crate::ownership::model::*;

verus! {

/// Pushing an entry and then dropping the last one gives the journal back.
pub proof fn lemma_push_then_drop_last(j: Seq<Entry>, e: Entry)
    ensures
        j.push(e).drop_last() =~= j,
        j.push(e).last() == e,
{
}

/// **Pushing an entry adds one to its sender's count, and nothing to anyone
/// else's.**
pub proof fn lemma_accepted_from_push(j: Seq<Entry>, e: Entry, s: HostId)
    ensures
        accepted_from(j.push(e), s) == accepted_from(j, s) + if e.env.sender == s {
            1nat
        } else {
            0nat
        },
{
    lemma_push_then_drop_last(j, e);
}

/// **The state after an append is the behaviour applied to the state before.**
///
/// The fold is a fold: appending a message is exactly one application of the
/// behaviour, so a host that recomputes the state from the journal and one that
/// has been applying messages as they arrived cannot disagree.
pub proof fn lemma_state_of_push(j: Seq<Entry>, e: Entry)
    ensures
        state_of(j.push(e)) == apply(state_of(j), e.env.body),
{
    lemma_push_then_drop_last(j, e);
}

/// The prefix one longer is the prefix pushed with the next entry.
pub proof fn lemma_take_next(j: Seq<Entry>, i: int)
    requires
        0 <= i < j.len(),
    ensures
        j.take(i + 1) =~= j.take(i).push(j[i]),
{
}

/// Taking the whole journal gives the journal.
pub proof fn lemma_take_all(j: Seq<Entry>)
    ensures
        j.take(j.len() as int) =~= j,
{
}

/// **Counting one more entry from `s` is counting what the prefix had, plus one
/// if that entry is `s`'s.**
pub proof fn lemma_accepted_from_next(j: Seq<Entry>, i: int, s: HostId)
    requires
        0 <= i < j.len(),
    ensures
        accepted_from(j.take(i + 1), s) == accepted_from(j.take(i), s) + if j[i].env.sender == s {
            1nat
        } else {
            0nat
        },
{
    lemma_take_next(j, i);
    lemma_accepted_from_push(j.take(i), j[i], s);
}

/// **A count never falls as the prefix grows.**
pub proof fn lemma_accepted_from_monotone(j: Seq<Entry>, a: int, b: int, s: HostId)
    requires
        0 <= a <= b <= j.len(),
    ensures
        accepted_from(j.take(a), s) <= accepted_from(j.take(b), s),
    decreases b - a,
{
    if a < b {
        lemma_accepted_from_next(j, a, s);
        lemma_accepted_from_monotone(j, a + 1, b, s);
    }
}

} // verus!
