//! The node: a table that obeys the merge rule, and answers its peers.

use std::collections::{BTreeSet, HashMap};
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use super::refusal::{refuse, refuse_err, refuse_no};
use super::{Liveness, Membership, Update, MAX_UPDATES};
use crate::swim::steps::{key_geq_exec, merge_step, refute_step, ExecRecord, ExecStatus};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

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
