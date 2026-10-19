//! **A distributed actor**: private state, a mailbox, and a host that can
//! change — with the guarantees an actor is supposed to have proved rather than
//! promised.
//!
//! An actor in a single process is single-threaded by construction, so it never
//! needs to say what it guarantees. Spread over machines it does, and the
//! guarantees are exactly the ones a single process gets for free:
//!
//! * **one thing at a time** — at most one host processes its messages, now and
//!   across handovers;
//! * **each message once** — a message the network delivers twice is processed
//!   once;
//! * **in the order sent** — messages from one sender are processed in the
//!   order that sender sent them, with none skipped;
//! * **state that survives** — moving the actor to another host moves its
//!   state, exactly.
//!
//! # How this is built
//!
//! The actor's state is not held by its host. It is a **journal**: the sequence
//! of messages the actor has accepted, in order, and its state is a fold over
//! that sequence ([`model::state_of`]). Appending to the journal is the one
//! thing a host does that matters, and it is **fenced by the ownership
//! protocol**: [`model::as_accept`] requires [`crate::ownership::spec::can_mutate`]
//! at the host's epoch, so a host that is not the owner, or is the owner of a
//! generation that has been superseded, cannot append. Everything the actor
//! guarantees follows from three facts:
//!
//! 1. only the owner at the current epoch can append (the ownership layer's
//!    exclusivity and fencing, used as-is);
//! 2. an append is accepted only if the message's sequence number is exactly
//!    the number of messages already accepted from that sender;
//! 3. the journal is only ever extended, never rewritten.
//!
//! * [`model`]  — the state space and transition relation, and nothing else.
//!   The one thing it borrows is the ownership layer's definition
//!   of who may mutate, which is the point.
//! * [`steps`]  — the host's decisions as executable `u64` functions.
//! * [`proofs`] — the invariant, the guarantees above as theorems, and that
//!   [`steps`] agrees with [`model`].
//! * `service`  — the actor over Jetstream RPC, behind the `service` feature.
//!
//! # What is not claimed
//!
//! **Delivery.** The network may delay, duplicate and reorder; nothing here says
//! a message is ever delivered, or that a sender retries. These are safety
//! properties: whatever is processed is processed once, in order, by one host.
//! An out-of-order arrival is *refused*, not buffered, so the sender (or the
//! mailbox in front of the host) must retry in order for anything to make
//! progress. That is the same line the other protocols here draw between safety
//! and liveness.

pub mod mailbox;
#[path = "model_t.rs"]
pub mod model;
pub mod proofs;
#[path = "steps_v.rs"]
pub mod steps;

#[cfg(feature = "service")]
pub mod service;
