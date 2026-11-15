//! **A proposal, packed into one integer so that the larger integer is the better one.**
//!
//! QuePaxa's recorders aggregate with `max` ([`crate::quepaxa::isr_spec::agg`]), and
//! what the protocol needs a recorder to report is the *best* proposal it was given.
//! The two agree if a proposal is encoded so that integer order is the paper's
//! order: higher priority wins, at equal priority the higher proposer id wins, and at
//! equal proposer the higher value wins (the last is only to make the order total; one
//! proposer proposes one value per round).
//!
//! The encoding is the paper's "fixed-width binary format, concatenated":
//! priority in the top 32 bits, proposer in the next 32, value in the low 64.
//!
//! # What is verified
//!
//! * [`unpack`] inverts [`pack`], and every integer unpacks to a proposal that packs
//!   back to it, so a recorder's reply, an integer, names exactly one proposal
//!   ([`lemma_split_is_inverse`], [`unpack`]);
//! * packing preserves the order: `pack(a) < pack(b)` exactly when `a` ranks below `b`
//!   ([`lemma_pack_order`]), so the maximum of a set of packed proposals is the best
//!   proposal in it;
//! * a proposal at the leader's priority [`LEADER`] outranks every proposal below it
//!   ([`lemma_the_leader_outranks`]).
#![allow(unused_imports)]

use vstd::prelude::*;

verus! {

/// The priority reserved for the designated leader's proposals: higher than any random
/// priority, so a leader's proposal that reaches a quorum first dominates.
pub const LEADER: u32 = 0xFFFF_FFFFu32;

/// A proposal: how much it matters, who made it, and what it proposes.
#[derive(Clone, Copy)]
pub struct Proposal {
    /// Higher wins. Random in `1..LEADER`, except the leader's, which is [`LEADER`].
    pub priority: u32,
    /// The proposer's index in the configuration. Breaks a tie in priority.
    pub proposer: u32,
    /// What is being proposed: a batch id, or a value.
    pub value: u64,
}

/// `a` ranks below `b`: lower priority, or equal priority and lower proposer, or equal
/// both and lower value.
pub open spec fn ranks_below(a: Proposal, b: Proposal) -> bool {
    ||| a.priority < b.priority
    ||| (a.priority == b.priority && a.proposer < b.proposer)
    ||| (a.priority == b.priority && a.proposer == b.proposer && a.value < b.value)
}

/// The integer a proposal packs to: the fields from the top down, in weights of `2^96`,
/// `2^64` and `1`.
pub open spec fn key(p: Proposal) -> int {
    (p.priority as int) * 0x1_0000_0000_0000_0000_0000_0000 + (p.proposer as int)
        * 0x1_0000_0000_0000_0000 + (p.value as int)
}

/// **Splitting a packed integer gives its fields back**, when each field is below the
/// next weight up.
pub proof fn lemma_split_is_inverse(pri: int, prop: int, val: int)
    requires
        0 <= pri,
        0 <= prop < 0x1_0000_0000,
        0 <= val < 0x1_0000_0000_0000_0000,
    ensures
        (pri * 0x1_0000_0000_0000_0000_0000_0000 + prop * 0x1_0000_0000_0000_0000 + val)
            / 0x1_0000_0000_0000_0000_0000_0000 == pri,
        ((pri * 0x1_0000_0000_0000_0000_0000_0000 + prop * 0x1_0000_0000_0000_0000 + val)
            / 0x1_0000_0000_0000_0000) % 0x1_0000_0000 == prop,
        (pri * 0x1_0000_0000_0000_0000_0000_0000 + prop * 0x1_0000_0000_0000_0000 + val)
            % 0x1_0000_0000_0000_0000 == val,
{
}

/// Pack a proposal: priority, proposer, value, from the top bit down.
pub fn pack(p: Proposal) -> (r: u128)
    ensures
        r as int == key(p),
{
    (p.priority as u128) * 0x1_0000_0000_0000_0000_0000_0000u128 + (p.proposer as u128)
        * 0x1_0000_0000_0000_0000u128 + (p.value as u128)
}

/// Unpack an integer into the proposal it names: `pack` of the result is `r`.
pub fn unpack(r: u128) -> (p: Proposal)
    ensures
        key(p) == r as int,
{
    let priority = (r / 0x1_0000_0000_0000_0000_0000_0000u128) as u32;
    let proposer = ((r / 0x1_0000_0000_0000_0000u128) % 0x1_0000_0000u128) as u32;
    let value = (r % 0x1_0000_0000_0000_0000u128) as u64;
    Proposal { priority, proposer, value }
}

/// **Packing preserves the order.** `pack(a) < pack(b)` exactly when `a` ranks below
/// `b`, so the maximum integer in a set is the best proposal in it.
pub proof fn lemma_pack_order(a: Proposal, b: Proposal)
    ensures
        (key(a) < key(b)) <==> ranks_below(a, b),
{
}

/// **A leader's proposal outranks every proposal of lower priority**, whoever made it
/// and whatever it proposes.
pub proof fn lemma_the_leader_outranks(leader: Proposal, other: Proposal)
    requires
        leader.priority == LEADER,
        other.priority < LEADER,
    ensures
        key(other) < key(leader),
{
    lemma_pack_order(other, leader);
}

} // verus!
