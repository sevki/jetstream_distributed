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
//! * [`proofs`] — exclusivity of the critical section, acyclicity of the
//!                holder pointers, and the routing run.

pub mod model;
pub mod proofs;
