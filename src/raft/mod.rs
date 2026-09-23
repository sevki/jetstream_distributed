//! **Raft leader election**: terms, votes, quorums.
//!
//! The same exclusivity statement as [`crate::ownership`] — at most one
//! authoritative party per generation — bought a completely different way.
//! Ownership *assumes* an atomic registry hands the epoch out; Raft *builds*
//! exclusivity out of counting, because any two majorities share a voter and a
//! voter votes once per term.
//!
//! * [`model`]   — state space and transition relation.
//! * [`steps`]   — the election decisions as executable `u64` functions.
//! * [`proofs`]  — Election Safety, and a run in which an election happens.
//! * `service`   — the protocol over Jetstream RPC, behind the `service`
//!                 feature.

pub mod model;
pub mod proofs;
pub mod steps;

#[cfg(feature = "service")]
pub mod service;
