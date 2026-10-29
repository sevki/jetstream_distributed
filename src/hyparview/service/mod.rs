//! HyParView as a service-side node: [`HvTable`]'s verified handlers, a lock, and a
//! source of the random choices.
//!
//! The same split [`crate::swim::service`] makes. The *decisions* are
//! [`HvTable`]'s methods, which `crate::hyparview::exec` proves to be steps of the
//! model for any history; this file is what is around them: where the random
//! choices come from, one lock so a handler reads and writes the views as one step,
//! and the [`PeerSampling`] a consumer reads.
//!
//! # What this is
//!
//! A **transport-free** node. [`Node::handle`] takes a message and returns the
//! messages to send; it does no I/O, so a test, a simulated network or a real
//! transport can sit in front of it. There is no wire protocol here yet.
//!
//! # What this is not
//!
//! * **Proved.** Each handler is `HvTable`'s verified method; this layer is plain
//!   Rust. That the node's views stay well-formed is proved for the table. That the
//!   cluster's active views are symmetric is **neither stated nor proved**: it is a
//!   property of several nodes and is checked by `tests/hyparview_cluster.rs`,
//!   which is a test of a simulated run.
//! * **Authenticated.** [`Node::handle`] is told who a message is from, as an
//!   argument. That is the transport's job, and who it believes is
//!   [#66](https://github.com/sevki/jetstream_distributed/issues/66)'s question;
//!   a caller that lies here can put any node in this node's views.
//! * **Symmetric under concurrent joins.** A `Neighbor` is always granted, so one
//!   that overlaps a `Disconnect` between the same two nodes can restore a link the
//!   other end is about to drop, leaving it one-sided for good. The cluster tests
//!   pin one such interleaving (`an_overlapping_neighbor_and_disconnect_leave_a_one_sided_link`).
//!   Closing it needs a handshake the model does not have.
//! * **Complete.** There is no shuffle and no promotion on failure, as in the model.

use std::sync::{Arc, Mutex};

use rand::rngs::StdRng;
use rand::{RngExt as _, SeedableRng as _};

pub use super::exec::ExecParams;
use super::exec::{ExecMsg, HvTable, Picks};
use crate::id::Id;
use crate::membership::PeerSampling;

/// A message a node receives. Who it is from is not in it; see [`Node::handle`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Message {
    /// "I am joining, and you are my contact." The sender is the newcomer.
    Join,
    /// "`new` is joining; take it on, or walk it `ttl` more hops." The sender is
    /// the active peer that passed it on.
    ForwardJoin { new: Id, ttl: u64 },
    /// "I am dropping the link between us."
    Disconnect,
    /// "Please add me to your active view."
    Neighbor,
}

/// A message to send, and to whom.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Outgoing {
    pub to: Id,
    pub message: Message,
}

impl From<ExecMsg> for Outgoing {
    fn from(m: ExecMsg) -> Self {
        match m {
            ExecMsg::ForwardJoin { to, new, ttl } => Outgoing {
                to,
                message: Message::ForwardJoin { new, ttl },
            },
            ExecMsg::Disconnect { to } => Outgoing {
                to,
                message: Message::Disconnect,
            },
            ExecMsg::Neighbor { to } => Outgoing {
                to,
                message: Message::Neighbor,
            },
        }
    }
}

struct Inner {
    table: HvTable,
    rng: StdRng,
}

impl Inner {
    /// The paper leaves these choices to the node; any value is a correct one, so
    /// they are random.
    fn picks(&mut self) -> Picks {
        Picks {
            victim: self.rng.random_range(0..usize::MAX),
            evict: self.rng.random_range(0..usize::MAX),
            next: self.rng.random_range(0..usize::MAX),
        }
    }
}

/// One HyParView node. Cloning shares the node.
#[derive(Clone)]
pub struct Node {
    me: Id,
    params: ExecParams,
    inner: Arc<Mutex<Inner>>,
}

impl Node {
    /// A node with empty views. `seed` makes its random choices repeatable.
    pub fn new(me: Id, params: ExecParams, seed: u64) -> Self {
        Node {
            me,
            params,
            inner: Arc::new(Mutex::new(Inner {
                table: HvTable::new(),
                rng: StdRng::seed_from_u64(seed),
            })),
        }
    }

    /// Join the overlay through `contact`: take it as an active peer, and return the
    /// [`Message::Join`] to send it. A node does not join through itself.
    pub fn join_via(&self, contact: Id) -> Vec<Outgoing> {
        if contact == self.me {
            return Vec::new();
        }
        let mut g = self.inner.lock().unwrap();
        let Picks { victim, evict, .. } = g.picks();
        let dropped = g.table.add_active(
            self.me,
            self.params.active_cap,
            self.params.passive_cap,
            contact,
            victim,
            evict,
        );
        let mut out = vec![Outgoing {
            to: contact,
            message: Message::Join,
        }];
        out.extend(dropped.map(|to| Outgoing {
            to,
            message: Message::Disconnect,
        }));
        out
    }

    /// Run the handler for `message`, which the transport says is from `from`, and
    /// return the messages to send.
    ///
    /// A `Join` or `Neighbor` from this node itself is dropped: the model has no
    /// step for it. A `ForwardJoin` from a node that is not an active peer is the
    /// model's own no-op (a replay after that peer was dropped), so the table
    /// handles it.
    pub fn handle(&self, from: Id, message: Message) -> Vec<Outgoing> {
        let mut g = self.inner.lock().unwrap();
        let picks = g.picks();
        let (me, p) = (self.me, self.params);
        let out = match message {
            Message::Join if from != me => g.table.join(me, p, from, picks),
            Message::Neighbor if from != me => g.table.neighbor(me, p, from, picks),
            Message::Disconnect => g.table.disconnect(me, p, from, picks),
            Message::ForwardJoin { new, ttl } => g.table.forward_join(me, p, new, ttl, from, picks),
            _ => Vec::new(),
        };
        out.into_iter().map(Outgoing::from).collect()
    }

    /// The passive view: peers this node has heard of and does not gossip with.
    pub fn passive(&self) -> Vec<Id> {
        self.inner.lock().unwrap().table.passive_peers()
    }
}

impl PeerSampling for Node {
    fn local(&self) -> Id {
        self.me
    }

    /// The active view.
    fn peers(&self) -> Vec<Id> {
        self.inner.lock().unwrap().table.active_peers()
    }
}
