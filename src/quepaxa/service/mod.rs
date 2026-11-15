//! **QuePaxa's concrete protocol**, over Jetstream.
//!
//! The paper's Algorithm 4 (the proposer) and the recorder it talks to, plus
//! [`QuePaxaLog`], which runs the proposer slot after slot to give the
//! [`ReplicatedLog`](crate::consensus::ReplicatedLog) every consensus protocol here
//! implements.
//!
//! # The split
//!
//! * [`Recorder`] is the wire protocol: **`record(slot, step, value)`** answers with the
//!   recorder's register's current step, first value and prior aggregate, and
//!   **`learn(slot, value)`** tells it what was decided. The register is
//!   [`crate::quepaxa::isr::Isr`], **verified** to answer what the paper's
//!   specification answers; [`RecorderNode`] is the plain Rust around it (who may call,
//!   which slots exist).
//! * [`proposer`] is Algorithm 4. Its decisions are a pure function
//!   ([`proposer::absorb`]) of the proposer's state and the replies from a quorum, and
//!   [`proposer::Proposer`] is the I/O around it. **Transcribed from the paper and
//!   tested, not verified**: nothing here proves that this code provides the broadcast
//!   the abstract algorithm assumes (see the Reference, Q-rows).
//! * [`QuePaxaLog`] picks the next slot, proposes there, moves on when another value
//!   won it, and tells the other replicas what was decided.
//!
//! # What is assumed
//!
//! * **Crash-stop.** A recorder's register is its consensus state. It is in memory here,
//!   so a recorder that restarts has forgotten what it promised, which the protocol's
//!   safety does not survive. Fewer than half the replicas may crash, for good.
//! * **Identity is the connection's**, against a roster fixed at construction, as in the
//!   other services: **an address is not a credential.** A member may record any
//!   proposal, including another proposer's, because proposals are relayed; this is
//!   a crash-fault protocol and a member that lies is outside it.
//! * **No timeouts in the protocol.** A proposer waits for a quorum of replies. A call to a
//!   crashed recorder fails or never answers, and the proposer does not wait for it.
//!   A caller that wants to give up wraps [`QuePaxaLog::propose`] in its own timeout.
//!
//! # What is not here
//!
//! The leader fast path is [`proposer::Config::leader`], used in a slot's first round;
//! there is no leader *election* and no multi-armed-bandit choice of leader. Hedging is
//! one delay per proposer before it starts. Slots are never forgotten, so a recorder's
//! memory grows with the log.
#![allow(unused_imports)]

mod log;
pub mod proposer;
mod recorder;

pub use log::QuePaxaLog;
pub use proposer::{Config, Proposer};
pub use recorder::RecorderNode;

use jetstream::prelude::*;

/// What a recorder answers to a `record`: the register's current step, the first value
/// recorded at that step, and the aggregate (maximum) of the step before it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Reply {
    /// The register's current step. At least the step asked about.
    pub step: u64,
    /// The first value recorded at that step (a packed proposal, never `0` once a value
    /// has been recorded).
    pub first: u128,
    /// The aggregate of the values recorded at the step before. `0` if none.
    pub prior: u128,
}

/// The recorder's wire protocol.
///
/// Neither method names the caller: who is calling is the connection's. See the
/// module docs.
#[service(uses(super::{Reply}))]
pub trait Recorder {
    /// Record the packed proposal `value` at `step` of `slot`, and answer.
    ///
    /// `value` must not be `0`, which is the register's "nothing recorded".
    async fn record(&self, ctx: Context, slot: u64, step: u64, value: u128) -> Result<Reply>;

    /// `value` was decided at `slot`. Idempotent; a different value for a slot already
    /// learned is refused.
    async fn learn(&self, ctx: Context, slot: u64, value: u64) -> Result<()>;
}

/// Not something this caller may ask for.
pub(crate) fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

/// The request names something the protocol does not have, or contradicts it.
pub(crate) fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}
