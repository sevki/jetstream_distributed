//! **Raft**: terms, votes, quorums, and the log.
//!
//! The same exclusivity statement as [`crate::ownership`] — at most one
//! authoritative party per generation — bought a completely different way.
//! Ownership *assumes* an atomic registry hands the epoch out; Raft *builds*
//! exclusivity out of counting, because any two majorities share a voter and a
//! voter votes once per term.
//!
//! * [`model`]   — state space and transition relation, election and log.
//! * [`steps`]   — the election decisions as executable `u64` functions.
//! * [`store`]   — the durable log: how a log that truncates lives on a device
//!                 that cannot.
//! * [`proofs`]  — Election Safety, a run in which an election happens, and
//!                 what one replication step gives you.
//! * `service`   — the protocol over Jetstream RPC, behind the `service`
//!                 feature.
//!
//! **Election Safety and Log Matching are proved; Leader Completeness and State
//! Machine Safety are not.** [`model`]'s docs say exactly where that line falls
//! and why it is where it is.

pub mod model;
pub mod proofs;
pub mod steps;
pub mod store;

#[cfg(feature = "service")]
pub mod service;
