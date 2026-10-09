//! Raymond's routing layer, as a Jetstream service.
//!
//! The same split the other services make: the *decisions* are the verified
//! functions in [`crate::raymond::steps`], which
//! `crate::raymond::proofs::refinement` ties to the model's transitions, and
//! this file is the part around them — who is calling, what a message carries,
//! and the table the decisions read.
//!
//! # What this hosts, and what it does not
//!
//! A [`Router`] holds the whole routing record — every node's holder pointer,
//! queue, `asked` and `using` flags, the set of requests ever sent, and where the
//! privilege is — under one lock. That is the model's own shape (`Raymond` is
//! one struct) and the same shape as the ownership `Registry`, which holds
//! `System::actors` in one process: **this checks Raymond's rules, it does not
//! distribute them.** A deployment where each node keeps only its own entries
//! and messages carry the rest is a different system with a different failure
//! model, and nothing in `crate::raymond::model` says it is refined by this one.
//! The model has the global record, so the service does.
//!
//! What the record buys is the thing the model needs it for: `privilege`, the
//! authoritative fact that is *not* any node's belief. A stale holder is a node
//! whose `holder` entry says it has the privilege and whose `privilege` does not;
//! the router can tell them apart, which is why [`Routing::assign_privilege`]
//! reads both. A standalone router never creates one — seizure is the composed
//! machine's step, because the revocation that justifies it is visible there —
//! so `crate::composed::service` is where that case lives.
//!
//! # What goes on the wire
//!
//! One method per labelled model step a *node* takes, each acting on the
//! **caller's own entries**:
//!
//! | model step | method | acts at |
//! | --- | --- | --- |
//! | `RequestCs { node }` | [`Routing::request_cs`] | the caller |
//! | `MakeRequest { node }` | [`Routing::make_request`] | the caller |
//! | `ReceiveRequest { at, from }` | [`Routing::receive_request`] | the caller (`at`) |
//! | `AssignPrivilege { node, head }` | [`Routing::assign_privilege`] | the caller (`node`) |
//! | `EnterCs { node }` | [`Routing::enter_cs`] | the caller |
//! | `ExitCs { node }` | [`Routing::exit_cs`] | the caller |
//!
//! **No method takes the acting node's number.** `receive_request` does take
//! `from`, and that is not the same thing: `from` is the node the request is
//! *about*, checked against the router's own record of what has been sent, so
//! naming a node that never sent one is refused rather than believed.
//!
//! # The assumption this rests on, stated
//!
//! The same one the other services state: a caller is identified by
//! [`Context::remote`] against a roster fixed at construction, and an address is
//! not a credential.

mod refusal;
mod router;

pub use router::{Event, Router};

use jetstream::prelude::*;

/// What a node can see of its own routing entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Standing {
    /// The next hop towards the privilege. Equal to the caller's own number
    /// when the caller *believes* it holds it.
    pub holder: u64,
    /// A request towards `holder` is outstanding.
    pub asked: bool,
    /// The caller is inside its critical section.
    pub using: bool,
    /// How many requests are queued behind the caller.
    pub queued: u64,
    /// The caller *actually* holds the privilege, as opposed to believing it.
    pub privileged: bool,
}

/// The node-facing protocol.
///
/// Six transitions, six methods, and none takes the acting node's number — see
/// the module docs.
#[service(uses(super::{Standing}))]
pub trait Routing {
    /// What do my own entries say?
    async fn standing(&self, ctx: Context) -> Result<Standing>;

    /// `RequestCs`: I want the privilege. Queues the caller behind itself.
    async fn request_cs(&self, ctx: Context) -> Result<()>;

    /// `MakeRequest`: forward my request one hop towards the privilege.
    /// Returns where it goes — the holder pointer, resolved *now*, which is
    /// what the model records.
    async fn make_request(&self, ctx: Context) -> Result<u64>;

    /// `ReceiveRequest`: a request `from` sent to me arrives. May be delivered
    /// more than once, in any order, and after the privilege has moved — that is
    /// the model's, and it costs fairness, not safety.
    async fn receive_request(&self, ctx: Context, from: u64) -> Result<()>;

    /// `AssignPrivilege`: I hold the privilege and am not using it, so I hand
    /// it to the head of my queue. Returns who got it.
    async fn assign_privilege(&self, ctx: Context) -> Result<u64>;

    /// `EnterCs`: I believe I hold the privilege and I am at the head of my own
    /// queue.
    async fn enter_cs(&self, ctx: Context) -> Result<()>;

    /// `ExitCs`: I am done.
    async fn exit_cs(&self, ctx: Context) -> Result<()>;
}
