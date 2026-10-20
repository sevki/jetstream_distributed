//! The node: a table that obeys the merge rule, and answers its peers.

use std::collections::{BTreeSet, HashMap};
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use super::refusal::{refuse, refuse_err, refuse_no};
use super::{Liveness, MAX_UPDATES, Membership, Update};
use crate::id::Id;
use crate::swim::exec::SwimTable;
use crate::swim::steps::{ExecRecord, ExecStatus, key_geq_exec};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// What a node did, for an audit and for tests that check *why* a record is
/// what it is rather than only that it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// A message changed what this node believes about `about`.
    Learned {
        about: Id,
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
    table: SwimTable,
    log: Vec<Event>,
}

/// One SWIM node.
#[derive(Clone)]
pub struct Node {
    inner: Arc<Mutex<Inner>>,
    /// Connection address to member number. The stated assumption; see the
    /// module docs.
    roster: Arc<HashMap<IpAddr, Id>>,
    /// This node's own number.
    me: Id,
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
    pub fn new(roster: HashMap<IpAddr, Id>, me: Id) -> io::Result<Self> {
        if !roster.values().any(|&n| n == me) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("node {me} is not on the roster"),
            ));
        }
        // A `sync` reply is the whole table, and the node that asked feeds it
        // through `apply`, which refuses more than `MAX_UPDATES` entries. A
        // roster bigger than that could never complete its own push/pull, so it
        // is refused here rather than discovered there.
        let members: BTreeSet<Id> = roster.values().copied().collect();
        if members.len() > MAX_UPDATES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "{} members exceed the {MAX_UPDATES}-update message limit",
                    members.len()
                ),
            ));
        }
        Ok(Node {
            inner: Arc::new(Mutex::new(Inner {
                table: SwimTable::new(),
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
            me,
        })
    }

    /// This node's own number.
    pub fn id(&self) -> Id {
        self.me
    }

    /// What this node believes about `node`, or `None` for a non-member.
    pub fn record(&self, node: Id) -> Option<Update> {
        if !self.is_member(node) {
            return None;
        }
        let g = self.inner.lock().expect("node lock");
        Some(Update::of(node, g.table.get(node)))
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

    /// **A probe of `node` failed**: believe it suspect, at `incarnation` — the
    /// one this node had recorded for it *when the probe began*.
    ///
    /// The incarnation is an argument, not something re-read here, and that is
    /// the point: a probe is slow, and a refutation can land while it is in
    /// flight. A suspicion at the old incarnation then loses to the refutation
    /// in [`merge_step`] and changes nothing; one that re-read the table would
    /// accuse the *new* incarnation of a failure it never had.
    ///
    /// Inherent rather than on the trait, so that nobody can make this node
    /// suspect anything: a node suspects a peer because *its own* probe timed
    /// out. Returns whether that changed what the node believes.
    pub fn suspect(&self, node: Id, incarnation: u64) -> Result<bool> {
        let accusation = ExecRecord {
            incarnation,
            status: ExecStatus::Suspect,
        };
        self.accuse(node, accusation, None)
    }

    /// **A suspicion timed out**: believe `node` dead — but only if it is still
    /// suspect at `incarnation`, the one the timer was started for.
    ///
    /// A timer that outlives its suspicion is a no-op. If the node refuted in
    /// the meantime its record is `Alive` at a higher incarnation, and declaring
    /// *that* dead would kill an incarnation nobody suspected. The check is made
    /// under the same lock as the write, so an RPC cannot slip a refutation in
    /// between the two.
    pub fn declare_dead(&self, node: Id, incarnation: u64) -> Result<bool> {
        let accusation = ExecRecord {
            incarnation,
            status: ExecStatus::Dead,
        };
        let still_suspect = ExecRecord {
            incarnation,
            status: ExecStatus::Suspect,
        };
        self.accuse(node, accusation, Some(still_suspect))
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

    fn is_member(&self, node: Id) -> bool {
        self.roster.values().any(|&n| n == node)
    }

    /// Which member is calling, from the connection rather than the request.
    fn caller(&self, ctx: &Context) -> Option<Id> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) => self.roster.get(addr).copied(),
            _ => None,
        }
    }

    fn view_locked(&self, g: &Inner) -> Vec<Update> {
        let members: BTreeSet<Id> = self.roster.values().copied().collect();
        members
            .into_iter()
            .map(|n| Update::of(n, g.table.get(n)))
            .collect()
    }

    /// Merge an accusation about a peer, if `required` (when given) is still
    /// exactly what this node holds for it.
    fn accuse(
        &self,
        node: Id,
        accusation: ExecRecord,
        required: Option<ExecRecord>,
    ) -> Result<bool> {
        if node == self.me {
            return Err(refuse_no("a node does not accuse itself"));
        }
        if !self.is_member(node) {
            return Err(refuse_err("not a member"));
        }
        let mut g = self.inner.lock().expect("node lock");
        let held = g.table.get(node);
        if required.is_some_and(|r| !same(held, r)) {
            return Ok(false);
        }
        let before = g.log.len();
        self.merge_one(&mut g, Update::of(node, accusation))?;
        Ok(g.log.len() != before)
    }

    /// Merge one update. The only place the table is written, and it is
    /// [`SwimTable::hear`]: the verified merge, and — if the record that changed
    /// is this node's *own*, so somebody has said something about it that
    /// out-ranks what it believes — the refutation, an `Alive` one incarnation
    /// above the accusation, merged in through the same door. Both are gossip
    /// steps (`proofs::table::theorem_hearing_oneself_accused_is_two_gossip_steps`).
    /// What this adds is the audit log.
    fn merge_one(&self, g: &mut Inner, u: Update) -> Result<()> {
        match g.table.hear(u.node, u.record(), self.me) {
            Ok(heard) => {
                if let Some(merged) = heard.learned {
                    g.log.push(Event::Learned {
                        about: u.node,
                        incarnation: merged.incarnation,
                        status: Update::of(u.node, merged).status,
                    });
                }
                if let Some(after) = heard.refuted {
                    g.log.push(Event::Refuted {
                        incarnation: after.incarnation,
                    });
                }
                Ok(())
            }
            Err(why) => {
                // The accusation was merged and could not be answered.
                let merged = g.table.get(u.node);
                g.log.push(Event::Learned {
                    about: u.node,
                    incarnation: merged.incarnation,
                    status: Update::of(u.node, merged).status,
                });
                Err(refuse(why))
            }
        }
    }

    /// The reply to a `ping`: the receiver's records for the members the message
    /// mentioned, plus its own, each once, in member order.
    fn ack(&self, g: &Inner, mentioned: &[Update]) -> Vec<Update> {
        let mut about = BTreeSet::from([self.me]);
        about.extend(mentioned.iter().map(|u| u.node));
        about
            .into_iter()
            .map(|n| Update::of(n, g.table.get(n)))
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
