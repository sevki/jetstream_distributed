//! **The interface every consensus protocol in this crate implements.**
//!
//! [`crate::raft`] and [`crate::quepaxa`] reach agreement in unrelated ways, and each
//! has a wire protocol of its own (`RequestVote` and `AppendEntries`; recorders and
//! their registers). A consumer should depend on neither. What a consumer wants from
//! consensus is one thing: **a log that every replica agrees on.** [`ReplicatedLog`]
//! is that, and nothing else.
//!
//! ```text
//! propose(value)  ->  Decision { slot, value }    "your value is at this slot"
//! decided(slot)   ->  Some(value)                 "this is what was decided there"
//! committed()     ->  n                           "slots 0..n are decided, no gaps"
//! ```
//!
//! # The contract
//!
//! Every implementation is held to the same properties, by one test written against
//! the trait and run on each of them (`tests/consensus_contract.rs`):
//!
//! 1. **Agreement.** If two replicas both report `decided(slot)`, they report the
//!    same value. This is the property a consumer builds on.
//! 2. **Validity.** A decided value was proposed by some caller.
//! 3. **A decision is visible to the replica that returned it.** If `propose(v)`
//!    returns `Decision { slot, value: v }`, then that replica's `decided(slot)` is
//!    `Some(v)` from then on.
//! 4. **No two proposals share a slot.** Two successful `propose` calls with
//!    different values return different slots.
//! 5. **`committed` is a prefix.** If `committed()` is `n`, every slot below `n` is
//!    decided at that replica.
//! 6. **A decision never changes.** Once `decided(slot)` is `Some(v)` it is `Some(v)`
//!    for as long as the replica runs.
//!
//! Termination is **not** a property of the contract. A protocol is entitled to refuse
//! ([`ProposeError`]) when it cannot make progress, and whether it eventually succeeds
//! is the protocol's own claim: Raft's rests on a leader being elected, QuePaxa's on
//! its randomisation. The contract test checks that a cluster in which nothing fails
//! does decide, which is a test and not a proof.
//!
//! # What this does not say
//!
//! * **It is not a specification.** The properties above are tested of each
//!   implementation, on simulated and in-process runs. What each protocol proves of
//!   its own model is in its own Reference page, and those statements are not the
//!   same: Raft's State Machine Safety is proved with a hypothesis and QuePaxa's
//!   agreement is proved over an ideal broadcast. There is no spec-level interface
//!   that both instantiate, because a shared theorem would have to hide that.
//! * **Values are `u64`.** A value is a batch id or a command handle, as it is in the
//!   protocols. What it means is the consumer's.
//! * **Failure model.** Crash-stop, with fewer than half the replicas failed. A replica
//!   that restarts and forgets its state is outside it, for every implementation here.
#![allow(unused_imports)]

use std::fmt;

use jetstream::prelude::async_trait;

/// A value, decided at a slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Decision {
    /// Where in the log.
    pub slot: u64,
    /// What was decided there. For a successful `propose(v)` this is `v`.
    pub value: u64,
}

/// Why a proposal was not decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProposeError {
    /// This replica is not placed to propose (Raft: it is not the leader). Try another.
    NotPlaced(String),
    /// A quorum could not be reached, or the attempt gave up. Nothing is known about
    /// whether the value was decided: a later `decided` may find it.
    Unavailable(String),
}

impl fmt::Display for ProposeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProposeError::NotPlaced(why) => write!(f, "not placed to propose: {why}"),
            ProposeError::Unavailable(why) => write!(f, "unavailable: {why}"),
        }
    }
}

impl std::error::Error for ProposeError {}

/// A log every replica agrees on. See the [module docs](self) for the contract.
#[async_trait]
pub trait ReplicatedLog: Send + Sync {
    /// Append `value`. Resolves with the slot it was decided at, once it is.
    ///
    /// An `Err` does not say the value was *not* decided, only that this call cannot
    /// say it was; the value may still appear in the log.
    async fn propose(&self, value: u64) -> Result<Decision, ProposeError>;

    /// What this replica knows was decided at `slot`, if it knows.
    async fn decided(&self, slot: u64) -> Option<u64>;

    /// How many slots, counted from 0, this replica knows are decided with no gap.
    async fn committed(&self) -> u64;
}
