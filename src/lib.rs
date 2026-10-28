//! # jetstream_distributed
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
//!   them proved rather than assumed.
//! * [`raft`]      — consensus, where exclusivity is bought by counting
//!   instead of by assuming an atomic registry.
//! * [`actor`]     — a distributed actor: a journal fenced by ownership, so one
//!   host at a time, each message once, in order, and state that
//!   survives a handover.
//! * [`membership`] — what a consumer of any membership protocol reads (who the
//!   peers are; for a failure detector, each member's standing), written once so
//!   that it does not name SWIM. `service` feature.
//! * [`hyparview`] — membership by two small views (who to gossip with), not a
//!   table of the cluster: one node, so far, with its handlers proved.
//! * [`swim`]      — gossip membership, which buys neither exclusivity nor
//!   agreement, and promises only that disagreements resolve.
//! * [`protocol`]  — not an algorithm: the labelled-step shape every model above
//!   has, written once as a trait; [`protocol_agreement`] proves each model's
//!   instance is the model it describes.
//! * [`temporal`]  — not an algorithm: the small temporal logic (leads-to, weak
//!   fairness, WF1) that [`actor::mailbox`]'s liveness theorem
//!   is stated in.
//!
//! Within each, `model` defines only the state space and the transition
//! relation and never imports the specification layer, so a specification
//! cannot be quietly weakened to fit the model.
//!
//! # The `service` feature
//!
//! The services are part of their algorithm's directory rather than a crate of
//! their own, and they are behind a **feature** for one reason: the verified
//! build must not depend on Jetstream. The feature is on by default, so depending
//! on the crate gives you the services; `verus --crate-type=lib src/lib.rs` does
//! not read features at all and `cargo verus verify --no-default-features` turns
//! it off, so the proofs are checked against a crate whose dependency graph is
//! `vstd` and nothing else, while the default build compiles the same modules
//! against the same verified step functions.
//!
//! It also keeps the toolchain question honest. `rust-toolchain.toml` pins the
//! Rust release the Verus build was made against, and that pin exists so the
//! proofs verify — not so a service is stuck on it. The services are built with
//! `cargo +stable`, which is what Jetstream tracks.
#![allow(unused_imports)]
// The proofs and specs are written inside `verus!`, so in an ordinary build
// (`cargo doc` included) `spec fn`s, `proof fn`s and the like do not exist, and
// the docs that link to them — `[`as_accept`]`, `[`inv_fifo`]` — cannot resolve.
// They resolve under Verus. Real items link by path, and the check stays on
// everywhere the ghost code is kept.
#![cfg_attr(not(verus_keep_ghost), allow(rustdoc::broken_intra_doc_links))]

pub mod actor;
pub mod composed;
pub mod compute;
// Vivaldi coordinates need `rand` and a wire format, so they are with the services.
pub mod hyparview;
pub mod id;
#[cfg(feature = "service")]
pub mod membership;
#[cfg(feature = "service")]
pub mod monitoring;
pub mod ownership;
pub mod raft;
pub mod raymond;
pub mod scheduling;
pub mod swim;
#[path = "protocol_t.rs"]
pub mod protocol;
#[path = "protocol_v.rs"]
pub mod protocol_agreement;
#[path = "temporal_t.rs"]
pub mod temporal;
