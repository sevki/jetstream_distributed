//! SWIM's membership protocol, as a Jetstream service.
//!
//! The same split the other two services make: the *decisions* are the verified
//! functions in [`crate::swim::steps`] — [`merge_step`](crate::swim::steps::merge_step) and
//! [`refute_step`](crate::swim::steps::refute_step),
//! which `crate::swim::proofs::refinement` ties to the model's `tr_gossip` — and
//! this file is the part around them: who is allowed to speak, what a message
//! carries, and what a node does to itself.
//!
//! # What goes on the wire, and what does not
//!
//! [`Membership`] is two methods, and both do the same thing to the receiver:
//! merge every [`Update`] in the message into the node's table. They differ in
//! what comes back.
//!
//! * [`Membership::ping`] answers with the receiver's records for the members
//!   the message mentioned, plus its own. That is SWIM's ping/ack with the
//!   dissemination piggybacked on it: the sender learns, in the same round
//!   trip, whether the receiver knew something newer.
//! * [`Membership::sync`] answers with the receiver's whole table. That is
//!   memberlist's push/pull — the anti-entropy that repairs what the piggyback
//!   missed.
//!
//! Suspecting a peer, declaring it dead and refuting an accusation are **not**
//! on the wire, for the reason `stand_for_election` is not on Raft's. They are
//! things a node does about its own view, and putting them in the trait would
//! let any caller make this node believe anything. A node suspects a peer
//! because *its own* probe failed ([`Node::suspect`]); it refutes because it
//! was told something false about *itself* ([`Node::apply`] does it, inline,
//! the moment a merge changes the node's own record).
//!
//! # Joining and leaving
//!
//! [`Node::new`] builds a node that knows only itself. There is no roster and no
//! join call. A join is the first `ping` or `sync` naming a sender the node has
//! not met ([`Membership::ping`] and [`Membership::sync`] carry the sender's
//! `Id`); the `sync` reply is the whole table, so the newcomer learns who is
//! there; and the others hear of it by gossip, which a node accepts about members
//! it has not met, up to [`MAX_UPDATES`].
//!
//! A node leaves by calling [`Node::leave`], which records it as
//! [`Liveness::Left`] and returns that record to tell its peers. `Left` out-ranks
//! every failure verdict at the same incarnation
//! (`crate::swim::proofs::merge::theorem_a_departure_outlasts_every_report_at_or_below_it`),
//! so a suspicion timer that was already running cannot turn a departure into a
//! failure. A node stopped without leaving is, to the cluster, a node that died.
//!
//! Who may be a member is not settled here: SWIM says nothing about it. Members
//! are never forgotten (a departed member's record is what keeps stale reports
//! from reviving it) and are bounded by [`MAX_UPDATES`].
//!
//! # What a node does not need to write down
//!
//! Raft's server and the ownership registry both keep a durable record, because
//! forgetting it breaks their safety. This node keeps none, and that is
//! deliberate rather than an omission: **incarnations are self-correcting.** A
//! node that restarts begins at incarnation 0; the first peer to tell it what
//! the cluster believes about it — `Dead` at 3, say — is a message about *this
//! node* that out-ranks its record, and [`Node::apply`] answers it with
//! incarnation 4. The restart costs a round trip, not correctness. (If it did
//! not, a durable incarnation would be needed and would be the first thing to
//! add; `tests/swim_membership.rs::a_restarted_node_is_told_what_it_was_and_outranks_it`
//! is the run that shows it is not.)
//!
//! # The assumption this rests on, stated
//!
//! **The sender is whoever the message says it is, and nothing here checks.** The
//! service does no authentication: it does not look at the connection, and it has
//! no opinion on who may join or who has been revoked. SWIM's own failure model is
//! crash faults, not Byzantine ones, and this service does not pretend otherwise:
//! any member may gossip about *any* member, so a member that lies about a third
//! party is believed, and a caller that lies about itself is believed too.
//!
//! Keeping outsiders out is a separate concern, and it lives somewhere else: in
//! front of this service (the transport, a gateway, a policy that decides who may
//! reach it) or beside it. Nothing about membership, a record that says `Dead` or
//! `Left`, is a security decision either, and none is made from one.
//!
//! # What is still not here
//!
//! The probe timer — *when* a node decides to ping whom — and the indirect-ping
//! fallback (`ping_req`) are not in this file. A node here is a table that obeys
//! the merge rule and answers its peers; the loop that picks a peer, waits out a
//! timeout, and calls [`Node::suspect`] and [`Node::declare_dead`] with the
//! incarnation it started from is the caller's. That is where timing
//! lives, and nothing in `crate::swim::model` says anything about timing.

mod node;
mod refusal;

use std::sync::Arc;

pub use node::{Event, Node};

use crate::{
    id::Id,
    swim::steps::{ExecRecord, ExecStatus},
};
use jetstream::prelude::*;

/// The most updates one message may carry.
///
/// A message is a wire-supplied `Vec`, and a node merges every element under a
/// lock, so an unbounded one is an unbounded stall. A table holds one record
/// per member, so a message with more entries than that is mostly repeating
/// itself; the cap is generous for any real cluster and small enough that
/// refusing is cheap.
pub const MAX_UPDATES: usize = 1024;

/// A member's standing, on the wire.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub enum Liveness {
    Alive,
    Suspect,
    Dead,
    /// The member announced its own departure. See `Node::leave`.
    Left,
}

/// One record about one member: *this is what I believe about `node`*.
///
/// The subject is a field. Who is speaking is a field of the call (`from`), not of
/// the record: a message says who sent it, and a record says who it is about.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Update {
    pub node: Id,
    pub incarnation: u64,
    pub status: Liveness,
}

impl Update {
    pub(super) fn record(self) -> ExecRecord {
        ExecRecord {
            incarnation: self.incarnation,
            status: match self.status {
                Liveness::Alive => ExecStatus::Alive,
                Liveness::Suspect => ExecStatus::Suspect,
                Liveness::Dead => ExecStatus::Dead,
                Liveness::Left => ExecStatus::Left,
            },
        }
    }

    pub(super) fn of(node: Id, r: ExecRecord) -> Update {
        Update {
            node,
            incarnation: r.incarnation,
            status: match r.status {
                ExecStatus::Alive => Liveness::Alive,
                ExecStatus::Suspect => Liveness::Suspect,
                ExecStatus::Dead => Liveness::Dead,
                ExecStatus::Left => Liveness::Left,
            },
        }
    }
}

/// The node-facing protocol.
///
/// Both methods say who is sending. The sender is part of the message, and the
/// service takes it at its word: see the module docs for what that does and does
/// not mean.
#[service(uses(super::{Id, Update}))]
pub trait Membership {
    /// SWIM's ping from `from`, with the dissemination piggybacked.
    ///
    /// Merges `updates` into the receiver's table and answers with the
    /// receiver's records for every member those updates mentioned, plus its own
    /// — so the caller finds out in one round trip whether the receiver knew
    /// something newer, and the receiver's own record is evidence it is up.
    async fn ping(&self, ctx: Context, from: Id, updates: Vec<Update>) -> Result<Vec<Update>>;

    /// Push/pull from `from`: merge `updates`, answer with the receiver's whole
    /// table.
    ///
    /// The anti-entropy pass. A piggyback carries only what a node happened to
    /// have on hand; this is how two nodes that have drifted apart converge
    /// without waiting for the right rumour to come along.
    async fn sync(&self, ctx: Context, from: Id, updates: Vec<Update>) -> Result<Vec<Update>>;
}

impl<T: Membership> Membership for Arc<T> {
    async fn ping(&self, ctx: Context, from: Id, updates: Vec<Update>) -> Result<Vec<Update>> {
        T::ping(self, ctx, from, updates).await
    }

    async fn sync(&self, ctx: Context, from: Id, updates: Vec<Update>) -> Result<Vec<Update>> {
        T::sync(self, ctx, from, updates).await
    }
}
