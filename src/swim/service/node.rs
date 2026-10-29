//! The node: a table that obeys the merge rule, and answers its peers.

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use super::refusal::{refuse, refuse_err, refuse_no};
use super::{Liveness, MAX_UPDATES, Membership, Update};
use crate::id::Id;
use crate::swim::exec::SwimTable;
use crate::swim::steps::{ExecRecord, ExecStatus, key_geq_exec};
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
    /// This node announced its own departure, at this incarnation.
    Departed { incarnation: u64 },
}

struct Inner {
    /// Every member number this node knows of, itself included: those that have
    /// called, and those only heard about. Never shrinks, so a departed member's
    /// record is kept and goes on out-ranking stale reports of it.
    members: BTreeSet<Id>,
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
    /// A node that knows only itself.
    ///
    /// Everyone else is learned: a member is whoever a message says is sending
    /// it, and whoever a member says exists (see [`Node::ping`] and
    /// [`Node::apply`]). Every member starts at its fresh record. Nothing is read
    /// from disk; see "What a node does not need to write down" in the module docs.
    ///
    /// Who may call is not the node's to say, and it does not check.
    pub fn new(me: Id) -> Self {
        Node {
            inner: Arc::new(Mutex::new(Inner {
                members: BTreeSet::from([me]),
                table: SwimTable::new(),
                log: Vec::new(),
            })),
            me,
        }
    }

    /// This node's own number.
    pub fn id(&self) -> Id {
        self.me
    }

    /// What this node believes about `node`, or `None` for a non-member.
    pub fn record(&self, node: Id) -> Option<Update> {
        let g = self.inner.lock().expect("node lock");
        if !g.members.contains(&node) {
            return None;
        }
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

    /// **This node is leaving**: record itself as [`Liveness::Left`] at the
    /// incarnation it holds, and return that record to be told to the peers.
    ///
    /// Written through the table's own merge, *not* through the path a received
    /// message takes, because that path answers a record that out-ranks the
    /// node's own with a refutation, and the whole point here is that this one
    /// is not refuted. `Left` out-ranks every status at the same incarnation
    /// (`proofs::merge::theorem_a_departure_outlasts_every_report_at_or_below_it`),
    /// so nothing already in flight can undo it; only this node itself, restarting
    /// and refuting with a higher incarnation, can come back.
    ///
    /// Leaving changes this node's belief and nothing else. Telling anybody is the
    /// caller's: `ping` or `sync` a peer with the returned update, and a peer that
    /// hears it knows this member left, which is not the same as having failed.
    /// A node that leaves and tells nobody is, to the cluster, a node that died.
    pub fn leave(&self) -> Update {
        let mut g = self.inner.lock().expect("node lock");
        let held = g.table.get(self.me);
        let departure = ExecRecord {
            incarnation: held.incarnation,
            status: ExecStatus::Left,
        };
        if g.table.learn(self.me, departure) {
            g.log.push(Event::Departed {
                incarnation: held.incarnation,
            });
        }
        Update::of(self.me, g.table.get(self.me))
    }

    /// Merge a batch of updates, as a received message would.
    ///
    /// Public so a node can be fed what it learned by other means — a pull it
    /// made itself, a reply it was handed — through the same door a peer's
    /// message uses. Atomic: a batch that would take the node past [`MAX_UPDATES`]
    /// members is refused whole, so a half-applied message is not a state this
    /// node can be in.
    pub fn apply(&self, updates: &[Update]) -> Result<()> {
        let mut g = self.inner.lock().expect("node lock");
        self.apply_locked(&mut g, updates, None)
    }

    /// `caller` is a member being admitted by this very request, if any: counted
    /// against the bound and added with the others, so that a request refused for
    /// being over the bound admits nobody.
    ///
    /// A node takes the word of a member about who else exists, the same trust it
    /// already gives a member's word about anyone's status, and bounds how many it
    /// will hold. Who may *be* a member is not decided here: it is decided by
    /// whoever identified the caller.
    fn apply_locked(&self, g: &mut Inner, updates: &[Update], caller: Option<Id>) -> Result<()> {
        if updates.len() > MAX_UPDATES {
            return Err(refuse_err("too many updates in one message"));
        }
        let strangers: BTreeSet<Id> = updates
            .iter()
            .map(|u| u.node)
            .chain(caller)
            .filter(|n| !g.members.contains(n))
            .collect();
        if g.members.len() + strangers.len() > MAX_UPDATES {
            return Err(refuse_err("too many members"));
        }
        g.members.extend(strangers);
        for u in updates {
            self.merge_one(g, *u)?;
        }
        Ok(())
    }

    fn view_locked(&self, g: &Inner) -> Vec<Update> {
        g.members
            .iter()
            .map(|&n| Update::of(n, g.table.get(n)))
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
        let mut g = self.inner.lock().expect("node lock");
        if !g.members.contains(&node) {
            return Err(refuse_err("not a member"));
        }
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

/// What the node does when a peer calls.
///
/// The sender is an argument, taken from the message, and these take no `Context`
/// and do no I/O, so they need no transport to be driven or tested. The
/// [`Membership`] service below is these, behind the generated protocol.
impl Node {
    /// SWIM's ping from `from`, with the dissemination piggybacked: merge
    /// `updates`, and answer with this node's records for every member they
    /// mentioned, plus its own.
    ///
    /// `from` is a member from now on, if it was not: calling is how a node joins.
    /// A request refused for being over the bound admits nobody.
    pub fn ping(&self, from: Id, updates: &[Update]) -> Result<Vec<Update>> {
        let mut g = self.inner.lock().expect("node lock");
        self.apply_locked(&mut g, updates, Some(from))?;
        Ok(self.ack(&g, updates))
    }

    /// Push/pull from `from`: merge `updates`, and answer with the whole table.
    ///
    /// Admits `from` as [`Node::ping`] does, and the reply is how a newcomer
    /// learns who else is there.
    pub fn sync(&self, from: Id, updates: &[Update]) -> Result<Vec<Update>> {
        let mut g = self.inner.lock().expect("node lock");
        self.apply_locked(&mut g, updates, Some(from))?;
        Ok(self.view_locked(&g))
    }
}

/// The node, served. The sender is the one the message names; the `Context` is
/// not read.
///
/// (`Node::ping` and `Node::sync` above take precedence in a method call; the
/// service's own, with a `Context`, are reached through the generated channel or
/// as `Membership::ping(&node, ctx, from, updates)`.)
impl Membership for Node {
    async fn ping(&self, _ctx: Context, from: Id, updates: Vec<Update>) -> Result<Vec<Update>> {
        Node::ping(self, from, &updates)
    }

    async fn sync(&self, _ctx: Context, from: Id, updates: Vec<Update>) -> Result<Vec<Update>> {
        Node::sync(self, from, &updates)
    }
}
