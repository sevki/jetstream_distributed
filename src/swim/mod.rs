//! **SWIM**: gossip-based failure detection and membership dissemination, in
//! the shape [hashicorp/memberlist](https://github.com/hashicorp/memberlist)
//! implements it.
//!
//! Raft and the ownership protocol both buy exclusivity — one leader, one
//! owner — at the cost of a majority round-trip on the critical path. SWIM
//! buys neither. It is a *membership* protocol, not a consensus one: every
//! node keeps its own view of who else is alive, those views disagree with
//! each other all the time, and the protocol's only promise is that
//! disagreements resolve rather than compound. That promise is the entire
//! content of this module.
//!
//! # What is here, and what is not
//!
//! [`model`] is the anti-entropy core: the merge rule memberlist's `state.go`
//! applies whenever a gossip message, a probe timeout or a self-refutation
//! updates what a node believes about a peer. It is deliberately the *first*
//! piece rather than the whole protocol, for the reason [`model`]'s own docs
//! give: it is the one piece a full SWIM implementation cannot get away with
//! getting wrong, because every other piece — the probe schedule, indirect
//! pings, piggybacked dissemination — is built on the assumption that this
//! merge converges no matter what order messages arrive in or how many times
//! they are replayed.
//!
//! Not here yet: the probe timer, indirect-ping fallback, and the piggyback
//! encoding that actually moves records between nodes. Those are a real
//! network protocol with real timing, and belong in a `service` built on top
//! of this core once it exists — the same order this repository built Raft
//! in, model and proofs first.
//!
//! * [`model`]  — state space: a member's record, the merge rule, one
//!                transition (`tr_gossip`) and the run it generates.
//! * [`proofs`] — the merge algebra, and what it buys once lifted to a run.

pub mod model;
pub mod proofs;
