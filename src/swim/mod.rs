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
//! updates what a node believes about a peer. It is the piece a full SWIM
//! implementation cannot get away with getting wrong, because everything else —
//! the probe schedule, indirect pings, piggybacked dissemination — is built on
//! the assumption that this merge converges no matter what order messages
//! arrive in or how many times they are replayed.
//!
//! Following it, in the order this repository built Raft in:
//!
//! * [`steps`]   — the merge and the refutation as executable `u64` functions,
//!   verified against the model.
//! * [`exec`]    — the node's table as verified code: `learn` is the model's
//!   `tr_gossip`, and `hear` is it twice when the record that changed is the
//!   node's own.
//! * `service`   — the protocol over Jetstream RPC, behind the `service`
//!   feature: a `Membership` trait with `ping` and `sync`.
//!
//! Not here yet: the probe timer, the indirect-ping fallback, and the piggyback
//! *selection* that decides which records ride on which probe. Those are a real
//! network protocol with real timing, and nothing in [`model`] says anything
//! about timing. A `service::Node` is a verified table ([`exec::SwimTable`]) behind
//! a roster and a lock that answers its peers; the roster, lock and log are not
//! verified; the loop that picks a peer, waits out a timeout
//! and calls `suspect` is the caller's.
//!
//! * [`model`]  — state space: a member's record, the merge rule, one
//!   transition (`tr_gossip`) and the run it generates.
//! * [`proofs`] — the merge algebra, and what it buys once lifted to a run.

#[path = "exec_v.rs"]
pub mod exec;
#[path = "model_t.rs"]
pub mod model;
pub mod proofs;
#[path = "steps_v.rs"]
pub mod steps;

#[cfg(feature = "service")]
pub mod service;
