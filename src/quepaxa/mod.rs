//! **QuePaxa**: consensus whose liveness does not depend on timeouts (Tennage et
//! al., SOSP 2023).
//!
//! Where [`crate::raft`] elects a leader and times out to replace a dead one,
//! QuePaxa runs a randomised asynchronous algorithm in which simultaneous
//! proposers help each other instead of interfering, so there is no view change to
//! time out into. This is the first piece, built the way [`crate::swim`] and
//! [`crate::hyparview`] were: the abstract algorithm first, with what it proves
//! said plainly, and the concrete protocol after.
//!
//! * [`model`]  — the paper's abstract algorithm over an ideal threshold broadcast
//!   (`tcast`), as a [`Protocol`](crate::protocol::Protocol).
//! * [`proofs`] — agreement and validity of that algorithm, from `tcast`'s two
//!   guarantees and nothing else.
//! * [`isr_spec`] — the recorder's register as the paper specifies it, keeping its
//!   whole history (Algorithm 2).
//! * [`isr`]    — the same register in four integers (Algorithm 3), verified to
//!   answer exactly what the specification answers.
//!
//! **Not here yet**: the concrete protocol (recorders, interval summary registers,
//! proposers that catch up), so that `tcast`'s guarantees are assumed here and not
//! derived; a service; the leader fast path and the hedging schedule; and any
//! statement about termination, which the paper makes with probability one and this
//! crate has no probability to state.

#[allow(clippy::new_without_default)]
#[path = "isr_v.rs"]
pub mod isr;
#[path = "isr_t.rs"]
pub mod isr_spec;
#[path = "model_t.rs"]
pub mod model;
pub mod proofs;
#[path = "proposal_v.rs"]
pub mod proposal;
#[cfg(feature = "service")]
pub mod service;
