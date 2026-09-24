//! **Ownership and Raymond as one state machine.**
//!
//! Not an algorithm of its own: the composition of two, with the coupling
//! between them expressed as a guard rather than as an assumption. That is the
//! whole point of the directory — a layered system is only as good as the
//! coupling, and here the coupling is a checked thing.
//!
//! * [`model`]  — both layers as a single machine.
//! * [`proofs`] — the coupling as an invariant, and an end-to-end handover
//!                across both layers.

pub mod model;
pub mod proofs;
