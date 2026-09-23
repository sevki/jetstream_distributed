//! # distributed-ownership
//!
//! A small, machine-checked model of **exclusive mutable ownership across
//! machines**, written in [Verus](https://github.com/verus-lang/verus).
//!
//! ```text
//! Rust:                  at most one mutable reference
//! Distributed ownership: at most one authoritative mutable owner
//! ```
//!
//! This is *not* an extension of Rust's borrow checker across machines. It is a
//! runtime protocol; what is formally verified is the protocol's exclusivity
//! and fencing properties, not the behaviour of the code that obeys it.
//!
//! Layering:
//!
//! * [`model`]     - state space and transition relation (no specification).
//! * [`fencing`]   - epochs: `current_epoch`, `valid_fence`, staleness.
//! * [`ownership`] - `may_mutate`, tokens, the system invariant.
//! * [`transfer`]  - the multi-step ownership handover and its lemmas.
//! * [`raymond`]   - Raymond's mutual-exclusion routing layer, kept strictly
//!                   separate from ownership semantics.
//! * [`raft`]      - Raft leader election: terms, votes, quorums. The same
//!                   exclusivity statement as [`ownership`], bought by counting
//!                   rather than by assuming an atomic registry.
//! * [`composed`]  - the two layers as one state machine, where the coupling
//!                   between them is a guard rather than an assumption.
//! * [`proofs`]    - the theorems. Everything claimed in `README.md` lives here.
//! * [`steps`]     - the protocol's transitions as executable `u64` functions,
//!                   each proved to agree with the model's `tr_*` step.
//! * [`exec`]      - the `u64` fence check, proved to agree with the model.
#![allow(unused_imports)]

pub mod composed;
pub mod exec;
pub mod fencing;
pub mod model;
pub mod ownership;
pub mod proofs;
pub mod raft;
pub mod raymond;
pub mod steps;
pub mod transfer;
