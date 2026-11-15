//! **HyParView**: membership by two small views instead of a table.
//!
//! Where [`crate::swim`] keeps a record and a verdict on every member, HyParView
//! keeps a handful of peers to gossip with (the active view) and a reserve (the
//! passive view). Nothing here judges a node alive or dead.
//!
//! This is the first piece, built the way [`crate::swim`] was: [`model`] is one
//! node's views and the handlers that maintain them; [`proofs`] says what they
//! keep true. See [`model`] for what is not here yet.
//!
//! * [`model`]  — a node's two views, the four handlers, and the messages they send.
//! * [`exec`]   — the views as verified code: each handler returns the messages to
//!   send, and is a step of the model for any history.
//! * [`proofs`] — the views stay bounded, disjoint, and free of the node itself.

#[path = "exec_v.rs"]
pub mod exec;
#[path = "model_t.rs"]
pub mod model;
pub mod proofs;
