//! What a consumer of a membership protocol may rely on, whichever protocol it is.
//!
//! SWIM keeps a full table with a verdict on every member. HyParView keeps a small
//! random partial view and makes no verdict at all. A placement layer that only
//! needs to know *which hosts are worth placing on* should not care which of them
//! it is talking to, so it is written against the two traits here, not against
//! SWIM's `Node`:
//!
//! * [`PeerSampling`], the part every membership protocol offers: who this node
//!   is, and which other members it would exchange gossip with right now.
//! * [`FailureDetector`], what SWIM adds on top: a [`Liveness`] verdict on every
//!   member it has heard of, including the ones it no longer gossips with.
//!
//! A protocol with no verdicts implements the first and not the second, and a
//! consumer that asks for [`FailureDetector`] says, in its type, that it needs them.
//!
//! # What this is not
//!
//! These are the *local* view of a node, the thing a consumer reads. They are not a
//! wire protocol: how nodes talk is each protocol's own (SWIM's is
//! `crate::swim::service::Swim`). Nor are they verified. Verus checks SWIM's merge
//! rule and executable steps; this layer is plain Rust, and what each method
//! returns is stated in its doc and held by `tests/membership_contract.rs`, which
//! runs the same checks against any implementation.
//!
//! There is deliberately no spec-level counterpart yet. A view of a protocol's
//! state is only worth defining against a property that reads it, and with SWIM the
//! only implementation the shared part could not be told from SWIM's own. It arrives
//! with the second implementation.

use jetstream::prelude::*;

use crate::id::Id;

/// A member's standing, as a failure detector reports it, and on the wire.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub enum Liveness {
    Alive,
    Suspect,
    Dead,
    /// The member announced its own departure. See `swim::service::Node::leave`.
    Left,
}

/// The part of a membership protocol every implementation offers.
pub trait PeerSampling {
    /// This node's own number.
    fn local(&self) -> Id;

    /// The members this node would exchange gossip with right now.
    ///
    /// Never contains [`local`](PeerSampling::local), and never repeats a member.
    /// What it excludes beyond that is the protocol's own business: SWIM leaves out
    /// the members it believes dead or departed; a partial-view protocol returns its
    /// active view.
    fn peers(&self) -> Vec<Id>;
}

/// A [`PeerSampling`] that also passes a verdict on the members it has heard of.
pub trait FailureDetector: PeerSampling {
    /// What this node believes about `node`, or `None` for a node it has not heard
    /// of. It does have a standing: [`local`](PeerSampling::local) is `Alive` to
    /// itself unless it has left.
    fn standing(&self, node: Id) -> Option<Liveness>;

    /// Every member this node has heard of, with its standing, each once.
    ///
    /// A superset of [`peers`](PeerSampling::peers): it keeps the members a node no
    /// longer gossips with, because a consumer that acts on a departure has to hear
    /// that it happened. Agrees with [`standing`](FailureDetector::standing).
    fn standings(&self) -> Vec<(Id, Liveness)>;
}
