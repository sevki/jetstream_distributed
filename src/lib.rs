//! # distributed-ownership
//!
//! Machine-checked distributed protocols, and the Jetstream services that speak
//! them.
//!
//! ```text
//! Rust:                  at most one mutable reference
//! Distributed ownership: at most one authoritative mutable owner
//! ```
//!
//! This is *not* an extension of Rust's borrow checker across machines. It is a
//! set of runtime protocols; what is formally verified is each protocol's
//! safety properties, not the behaviour of every line of code that obeys them.
//!
//! # Layout
//!
//! One directory per algorithm, and each one holds **the whole of that
//! algorithm**: its model, its proofs, its executable steps and its service.
//!
//! * [`ownership`] — exclusive mutable ownership with epoch fencing.
//! * [`raymond`]   — Raymond's mutual-exclusion routing layer.
//! * [`composed`]  — the two above as one machine, with the coupling between
//!                   them proved rather than assumed.
//! * [`raft`]      — consensus, where exclusivity is bought by counting
//!                   instead of by assuming an atomic registry.
//! * [`actor`]     — a distributed actor: a journal fenced by ownership, so one
//!                   host at a time, each message once, in order, and state that
//!                   survives a handover.
//! * [`swim`]      — gossip membership, which buys neither exclusivity nor
//!                   agreement, and promises only that disagreements resolve.
//! * [`temporal`]  — not an algorithm: the small temporal logic (leads-to, weak
//!                   fairness, WF1) that [`actor::mailbox`]'s liveness theorem
//!                   is stated in.
//!
//! Within each, `model` defines only the state space and the transition
//! relation and never imports the specification layer, so a specification
//! cannot be quietly weakened to fit the model.
//!
//! # The `service` feature
//!
//! The services are part of their algorithm's directory rather than a crate of
//! their own, and they are behind a **non-default feature** for one reason: the
//! verified build must not depend on Jetstream. `verus --crate-type=lib
//! src/lib.rs` and `cargo verus verify` both run with the feature off, so the
//! proofs are checked against a crate whose dependency graph is `vstd` and
//! nothing else, while `--features service` builds the same modules against the
//! same verified step functions.
//!
//! It also keeps the toolchain question honest. `rust-toolchain.toml` pins the
//! Rust release the Verus build was made against, and that pin exists so the
//! proofs verify — not so a service is stuck on it. The services are built with
//! `cargo +stable`, which is what Jetstream tracks.
#![allow(unused_imports)]

pub mod actor;
pub mod composed;
pub mod ownership;
pub mod raft;
pub mod raymond;
pub mod swim;
pub mod temporal;
