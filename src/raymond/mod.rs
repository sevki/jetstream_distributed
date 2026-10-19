//! **Raymond's mutual-exclusion routing layer**, kept strictly separate from
//! ownership semantics.
//!
//! Routing decides where a privilege *is*; it does not decide who may mutate
//! anything. Keeping the two apart is what lets
//! [`proofs::routing_layer`] state that a node which
//! believes it holds the privilege, and does not, still cannot mutate the
//! actor.
//!
//! * [`model`]  — the routing state machine.
//! * [`steps`]  — the routing decisions as executable `u64` functions.
//! * [`exec`]   — the routing record as verified code: [`exec::RayTable`] has a
//!   view that is a model state, and each method is a model step by contract,
//!   each refusal a step the model could not take.
//! * [`proofs`] — exclusivity of the critical section, acyclicity of the
//!   holder pointers, the routing run, and that [`steps`] agrees
//!   with [`model`].
//! * `service`  — the routing layer over Jetstream RPC, behind the `service`
//!   feature.

pub mod exec;
pub mod model;
pub mod proofs;
pub mod steps;

#[cfg(feature = "service")]
pub mod service;
