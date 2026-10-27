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
//! [`Node::new`] builds a closed cluster: the members are the ones it was given.
//! [`Node::admitting`] builds one that grows, with an [`Admission`] policy from a
//! caller's address to the member number that address may be. There is no join
//! call. A join is the first `ping` or `sync` from an address the policy lets in;
//! the `sync` reply is the whole table, so the newcomer learns who is there; and
//! the others hear of it by gossip, which an open node accepts about members it
//! was not built with and a closed node refuses. The member number comes from the
//! policy and the connection, never from the request.
//!
//! A node leaves by calling [`Node::leave`], which records it as
//! [`Liveness::Left`] and returns that record to tell its peers. `Left` out-ranks
//! every failure verdict at the same incarnation
//! (`crate::swim::proofs::merge::theorem_a_departure_outlasts_every_report_at_or_below_it`),
//! so a suspicion timer that was already running cannot turn a departure into a
//! failure. A node stopped without leaving is, to the cluster, a node that died.
//!
//! What is *not* settled here is who the policy should admit: SWIM says nothing
//! about that. Members are never forgotten (a departed member's record is what
//! keeps stale reports from reviving it) and are bounded by [`MAX_UPDATES`].
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
//! The same one the other services state. A caller is identified by
//! [`Context::remote`] against the roster the node holds, and **an address
//! is not a credential**. What is worth saying about SWIM specifically is how
//! little the identity buys: any member may gossip about *any* member,
//! so a member that lies about a third party is believed. SWIM's own
//! failure model is crash faults, not Byzantine ones, and this service does not
//! pretend otherwise; what it does enforce is that an address the roster and the
//! admission policy do not accept cannot join the conversation.
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

pub use node::{Admission, Event, Node};

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
/// The subject is a field and the sender is not. Who is speaking arrives with
/// the connection, as in the other services; who is being spoken *about* is the
/// content, and has to be.
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
/// Two methods, and neither takes a node number for the *sender* — see the
/// module docs.
#[service(uses(super::{Update}))]
pub trait Membership {
    /// SWIM's ping, with the dissemination piggybacked.
    ///
    /// Merges `updates` into the receiver's table and answers with the
    /// receiver's records for every member those updates mentioned, plus its own
    /// — so the caller finds out in one round trip whether the receiver knew
    /// something newer, and the receiver's own record is evidence it is up.
    async fn ping(&self, ctx: Context, updates: Vec<Update>) -> Result<Vec<Update>>;

    /// Push/pull: merge `updates`, answer with the receiver's whole table.
    ///
    /// The anti-entropy pass. A piggyback carries only what a node happened to
    /// have on hand; this is how two nodes that have drifted apart converge
    /// without waiting for the right rumour to come along.
    async fn sync(&self, ctx: Context, updates: Vec<Update>) -> Result<Vec<Update>>;
}
