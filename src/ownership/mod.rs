//! **Exclusive mutable ownership across machines**, with epoch fencing.
//!
//! ```text
//! Rust:                  at most one mutable reference
//! Distributed ownership: at most one authoritative mutable owner
//! ```
//!
//! Everything about this protocol lives here: the model, the specification, the
//! proofs, the executable steps and the Jetstream service that runs them.
//!
//! * [`model`]    — state space and transition relation, and nothing else. It
//!   does not import the specification layer, so a specification
//!   cannot be quietly weakened to fit the model.
//! * [`fencing`]  — epochs: `current_epoch`, `valid_fence`, staleness.
//! * [`spec`]     — `may_mutate`, tokens, the system invariant.
//! * [`transfer`] — the multi-step handover and its lemmas.
//! * [`steps`]    — the transitions as executable `u64` functions.
//! * [`exec`]     — the `u64` fence check a *node* runs against its own belief,
//!   which is a different thing from the fence a registry runs.
//! * [`registry`] — the registry's record as verified code: the actor's state,
//!   the grants published and the writes landed, with one method per step and a
//!   contract that is the model's transition, grants included.
//! * [`proofs`]   — the theorems.
//! * `service`    — the protocol over Jetstream RPC, behind the `service`
//!   feature.

pub mod exec;
pub mod fencing;
pub mod model;
pub mod proofs;
pub mod registry;
pub mod spec;
pub mod steps;
pub mod transfer;

#[cfg(feature = "service")]
pub mod service;
