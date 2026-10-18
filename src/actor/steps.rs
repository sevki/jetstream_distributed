//! The actor's decisions, executable and verified.
//!
//! The same shape as [`crate::raft::steps`] and [`crate::swim::steps`]: each
//! decision a host makes is a small `u64` function whose postcondition is stated
//! in terms of [`crate::actor::model`], and [`crate::actor::proofs::refinement`]
//! ties those postconditions to the model's transitions.
//!
//! # What a step sees
//!
//! Answers, not records. [`accept_step`] is handed whether the fence admits the
//! host (the ownership layer's own verified `may_write_step` answers that), whether
//! the message was sent, and two numbers — the message's sequence number and how
//! many messages the journal already holds from its sender. It does no I/O and
//! holds no lock. It does not see the journal, which is why the count is an
//! argument: counting is a fact about the journal that the host establishes, and
//! [`crate::actor::proofs::refinement`] states the correspondence as a hypothesis
//! rather than assuming it.
//!
//! # The places `u64` is not `nat`
//!
//! Sequence numbers and counts are unbounded in the model and `u64` here. A step
//! that could not count further refuses with [`ActorRefusal::Exhausted`] rather
//! than wrapping: a wrapped sequence number would be a *repeat*, and a repeat is
//! what the whole of [`crate::actor::proofs::delivery`] says cannot be accepted.
//! The actor's state is taken modulo the word ([`crate::actor::model::word`]) in
//! the model itself, so [`apply_step`] has no narrower reading to refuse.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::model::*;

verus! {

/// Why a step did not fire. The protocol's reasons only.
#[derive(Clone, Copy)]
pub enum ActorRefusal {
    /// The fence refuses this host: it is not the owner, or its epoch is behind.
    Fenced,
    /// No such message was ever sent.
    NotSent,
    /// Already accepted: its sequence number is below the count from its sender.
    Duplicate,
    /// Not yet its turn: its sequence number is above the count from its sender.
    AheadOfItsTurn,
    /// The `u64` sequence space is exhausted. See the module docs.
    Exhausted,
}

/// [`as_accept`]'s guard, minus liveness: the fence admits the host, the message
/// was sent, and its sequence number is exactly the count already accepted from
/// its sender.
pub open spec fn accept_fires(may_write: bool, was_sent: bool, seq: nat, accepted: nat) -> bool {
    &&& may_write
    &&& was_sent
    &&& seq == accepted
}

/// May the host append this message?
///
/// The refusals are ordered: the fence first, because a host that is not the
/// owner has no business learning anything about the journal; then whether the
/// message exists; then which side of its turn it is on.
pub fn accept_step(may_write: bool, was_sent: bool, seq: u64, accepted: u64) -> (r: Result<
    (),
    ActorRefusal,
>)
    ensures
        match r {
            Ok(_) => accept_fires(may_write, was_sent, seq as nat, accepted as nat) && accepted
                < u64::MAX,
            Err(why) => !accept_fires(may_write, was_sent, seq as nat, accepted as nat) || ((why is
            Exhausted) && accepted == u64::MAX),
        },
{
    if !may_write {
        Err(ActorRefusal::Fenced)
    } else if !was_sent {
        Err(ActorRefusal::NotSent)
    } else if seq < accepted {
        Err(ActorRefusal::Duplicate)
    } else if seq > accepted {
        Err(ActorRefusal::AheadOfItsTurn)
    } else if accepted == u64::MAX {
        Err(ActorRefusal::Exhausted)
    } else {
        Ok(())
    }
}

/// What sequence number does a sender's next message carry? Its counter, unless
/// the counter cannot go on.
pub fn send_step(next: u64) -> (r: Result<u64, ActorRefusal>)
    ensures
        match r {
            Ok(seq) => seq == next && next < u64::MAX,
            Err(why) => next == u64::MAX && (why is Exhausted),
        },
{
    if next == u64::MAX {
        Err(ActorRefusal::Exhausted)
    } else {
        Ok(next)
    }
}

/// The actor's behaviour at the machine: [`apply`], in the word the state lives
/// in.
pub fn apply_step(state: u64, body: u64) -> (r: u64)
    ensures
        r as nat == apply(state as nat, body as nat),
{
    // 128 bits holds `state * 31 + body` for any two 64-bit inputs, so the
    // reduction is exact rather than a wrap.
    let wide = (state as u128) * 31 + (body as u128);
    (wide % 18446744073709551616u128) as u64
}

} // verus!
