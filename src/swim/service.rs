//! SWIM's membership protocol, as a Jetstream service.
//!
//! The same split the other two services make: the *decisions* are the verified
//! functions in [`crate::swim::steps`] — [`merge_step`] and [`refute_step`],
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
//! [`Context::remote`] against a roster fixed at construction, and **an address
//! is not a credential**. What is worth saying about SWIM specifically is how
//! little the identity buys: any rostered caller may gossip about *any* member,
//! so a rostered node that lies about a third party is believed. SWIM's own
//! failure model is crash faults, not Byzantine ones, and this service does not
//! pretend otherwise; what it does enforce is that a stranger cannot join the
//! conversation.
//!
//! # What is still not here
//!
//! The probe timer — *when* a node decides to ping whom — and the indirect-ping
//! fallback (`ping_req`) are not in this file. A node here is a table that obeys
//! the merge rule and answers its peers; the loop that picks a peer, waits out a
//! timeout, and calls [`Node::suspect`] is the caller's. That is where timing
//! lives, and nothing in `crate::swim::model` says anything about timing.

use std::collections::{BTreeSet, HashMap};
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use crate::swim::steps::{
    key_geq_exec, merge_step, refute_step, ExecRecord, ExecStatus, SwimRefusal,
};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
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
}

/// One record about one member: *this is what I believe about `node`*.
///
/// The subject is a field and the sender is not. Who is speaking arrives with
/// the connection, as in the other services; who is being spoken *about* is the
/// content, and has to be.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Update {
    pub node: u64,
    pub incarnation: u64,
    pub status: Liveness,
}

impl Update {
    fn record(self) -> ExecRecord {
        ExecRecord {
            incarnation: self.incarnation,
            status: match self.status {
                Liveness::Alive => ExecStatus::Alive,
                Liveness::Suspect => ExecStatus::Suspect,
                Liveness::Dead => ExecStatus::Dead,
            },
        }
    }

    fn of(node: u64, r: ExecRecord) -> Update {
        Update {
            node,
            incarnation: r.incarnation,
            status: match r.status {
                ExecStatus::Alive => Liveness::Alive,
                ExecStatus::Suspect => Liveness::Suspect,
                ExecStatus::Dead => Liveness::Dead,
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

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

/// Not something this caller may ask for.
fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

/// The request names something that does not exist, or is not one the protocol
/// has.
fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

/// The incarnation space is exhausted.
///
/// The model counts incarnations in `nat`; this counts them in `u64`. See
/// [`crate::swim::steps::refute_step`].
fn exhausted() -> Error {
    Error::new("the incarnation space is exhausted").set_code("NO")
}

fn refuse(why: SwimRefusal) -> Error {
    match why {
        SwimRefusal::Exhausted => exhausted(),
    }
}

// ---------------------------------------------------------------------------
// The node
// ---------------------------------------------------------------------------

/// What a node did, for an audit and for tests that check *why* a record is
/// what it is rather than only that it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// A message changed what this node believes about `about`.
    Learned {
        about: u64,
        incarnation: u64,
        status: Liveness,
    },
    /// This node was told something about itself that out-ranked its own
    /// record, and answered with this incarnation.
    Refuted { incarnation: u64 },
}

struct Inner {
    /// One record per member that has ever been heard about. A member with no
    /// entry is exactly a member at its fresh record — the model's `record_of`
    /// says the same.
    table: HashMap<u64, ExecRecord>,
    log: Vec<Event>,
}

/// One SWIM node.
#[derive(Clone)]
pub struct Node {
    inner: Arc<Mutex<Inner>>,
    /// Connection address to member number. The stated assumption; see the
    /// module docs.
    roster: Arc<HashMap<IpAddr, u64>>,
    /// This node's own number.
    me: u64,
}

fn fresh() -> ExecRecord {
    crate::swim::steps::fresh_exec_record()
}

/// `a` and `b` are the same record.
///
/// Two records tie on key exactly when they are equal — `status_rank` is
/// injective, `crate::swim::proofs::merge::lemma_key_geq_antisymmetric` — so
/// asking the verified comparison both ways is asking for equality, and it keeps
/// the unverified code from growing a comparison of its own.
fn same(a: ExecRecord, b: ExecRecord) -> bool {
    key_geq_exec(a, b) && key_geq_exec(b, a)
}

impl Node {
    /// A node that knows nobody yet but its roster.
    ///
    /// Every member starts at its fresh record. Nothing is read from disk; see
    /// "What a node does not need to write down" in the module docs.
    pub fn new(roster: HashMap<IpAddr, u64>, me: u64) -> io::Result<Self> {
        if !roster.values().any(|&n| n == me) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("node {me} is not on the roster"),
            ));
        }
        Ok(Node {
            inner: Arc::new(Mutex::new(Inner {
                table: HashMap::new(),
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
            me,
        })
    }

    /// This node's own number.
    pub fn id(&self) -> u64 {
        self.me
    }

    /// What this node believes about `node`, or `None` for a non-member.
    pub fn record(&self, node: u64) -> Option<Update> {
        if !self.is_member(node) {
            return None;
        }
        let g = self.inner.lock().expect("node lock");
        Some(Update::of(
            node,
            g.table.get(&node).copied().unwrap_or_else(fresh),
        ))
    }

    /// The whole table, one record per member, in member order.
    pub fn view(&self) -> Vec<Update> {
        let g = self.inner.lock().expect("node lock");
        self.view_locked(&g)
    }

    /// What this node has done, oldest first.
    pub fn log(&self) -> Vec<Event> {
        self.inner.lock().expect("node lock").log.clone()
    }

    /// **A probe of `node` failed**: believe it suspect, at the incarnation this
    /// node last heard for it.
    ///
    /// Inherent rather than on the trait, so that nobody can make this node
    /// suspect anything: a node suspects a peer because *its own* probe timed
    /// out. Returns whether that changed what the node believes — suspecting
    /// something already suspect, or already dead, changes nothing.
    pub fn suspect(&self, node: u64) -> Result<bool> {
        self.accuse(node, ExecStatus::Suspect)
    }

    /// **A suspicion timed out**: believe `node` dead, at the incarnation this
    /// node last heard for it.
    pub fn declare_dead(&self, node: u64) -> Result<bool> {
        self.accuse(node, ExecStatus::Dead)
    }

    /// Merge a batch of updates, as a received message would.
    ///
    /// Public so a node can be fed what it learned by other means — a pull it
    /// made itself, a reply it was handed — through the same door a peer's
    /// message uses. Atomic: a batch naming a non-member is refused whole, so a
    /// half-applied message is not a state this node can be in.
    pub fn apply(&self, updates: &[Update]) -> Result<()> {
        let mut g = self.inner.lock().expect("node lock");
        self.apply_locked(&mut g, updates)
    }

    fn apply_locked(&self, g: &mut Inner, updates: &[Update]) -> Result<()> {
        if updates.len() > MAX_UPDATES {
            return Err(refuse_err("too many updates in one message"));
        }
        if updates.iter().any(|u| !self.is_member(u.node)) {
            return Err(refuse_err("an update names a node that is not a member"));
        }
        for u in updates {
            self.merge_one(g, *u)?;
        }
        Ok(())
    }

    fn is_member(&self, node: u64) -> bool {
        self.roster.values().any(|&n| n == node)
    }

    /// Which member is calling, from the connection rather than the request.
    fn caller(&self, ctx: &Context) -> Option<u64> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) => self.roster.get(addr).copied(),
            _ => None,
        }
    }

    fn view_locked(&self, g: &Inner) -> Vec<Update> {
        let members: BTreeSet<u64> = self.roster.values().copied().collect();
        members
            .into_iter()
            .map(|n| Update::of(n, g.table.get(&n).copied().unwrap_or_else(fresh)))
            .collect()
    }

    fn accuse(&self, node: u64, status: ExecStatus) -> Result<bool> {
        if node == self.me {
            return Err(refuse_no("a node does not accuse itself"));
        }
        if !self.is_member(node) {
            return Err(refuse_err("not a member"));
        }
        let mut g = self.inner.lock().expect("node lock");
        let held = g.table.get(&node).copied().unwrap_or_else(fresh);
        let before = g.log.len();
        self.merge_one(
            &mut g,
            Update::of(
                node,
                ExecRecord {
                    incarnation: held.incarnation,
                    status,
                },
            ),
        )?;
        Ok(g.log.len() != before)
    }

    /// Merge one update. The only place a table entry is written.
    ///
    /// The merge is [`merge_step`], the verified function. What this adds is the
    /// one thing the model leaves to the node: if the record that just changed
    /// is this node's *own*, somebody has said something about it that
    /// out-ranks what it believes, and it answers with [`refute_step`] — an
    /// `Alive` one incarnation above the accusation — merged in through the same
    /// door, so the refutation is a gossip step like any other
    /// (`proofs::refinement::theorem_a_refutation_is_a_gossip_step`).
    fn merge_one(&self, g: &mut Inner, u: Update) -> Result<()> {
        let held = g.table.get(&u.node).copied().unwrap_or_else(fresh);
        let merged = merge_step(held, u.record());
        if same(merged, held) {
            return Ok(());
        }
        g.table.insert(u.node, merged);
        g.log.push(Event::Learned {
            about: u.node,
            incarnation: merged.incarnation,
            status: Update::of(u.node, merged).status,
        });
        if u.node == self.me {
            let refutation = refute_step(merged.incarnation).map_err(refuse)?;
            let after = merge_step(merged, refutation);
            g.table.insert(self.me, after);
            g.log.push(Event::Refuted {
                incarnation: after.incarnation,
            });
        }
        Ok(())
    }

    /// The reply to a `ping`: the receiver's records for the members the message
    /// mentioned, plus its own, each once, in member order.
    fn ack(&self, g: &Inner, mentioned: &[Update]) -> Vec<Update> {
        let mut about = BTreeSet::from([self.me]);
        about.extend(mentioned.iter().map(|u| u.node));
        about
            .into_iter()
            .map(|n| Update::of(n, g.table.get(&n).copied().unwrap_or_else(fresh)))
            .collect()
    }
}

impl Membership for Node {
    async fn ping(&self, ctx: Context, updates: Vec<Update>) -> Result<Vec<Update>> {
        if self.caller(&ctx).is_none() {
            return Err(refuse_no("unknown caller"));
        }
        let mut g = self.inner.lock().expect("node lock");
        self.apply_locked(&mut g, &updates)?;
        Ok(self.ack(&g, &updates))
    }

    async fn sync(&self, ctx: Context, updates: Vec<Update>) -> Result<Vec<Update>> {
        if self.caller(&ctx).is_none() {
            return Err(refuse_no("unknown caller"));
        }
        let mut g = self.inner.lock().expect("node lock");
        self.apply_locked(&mut g, &updates)?;
        Ok(self.view_locked(&g))
    }
}
