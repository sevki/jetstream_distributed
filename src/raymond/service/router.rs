//! The router: the whole routing record of a cluster, behind one lock.

use std::collections::{HashMap, HashSet, VecDeque};
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use super::refusal::{refuse, refuse_err, refuse_no};
use super::{Routing, Standing};
use crate::raymond::exec::RayTable;
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// What the router did, for an audit and for tests that check the *path* a
/// privilege took rather than only where it ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    Requested {
        node: u64,
    },
    Forwarded {
        from: u64,
        to: u64,
    },
    Received {
        at: u64,
        from: u64,
    },
    Passed {
        from: u64,
        to: u64,
    },
    Entered {
        node: u64,
    },
    Exited {
        node: u64,
    },
    /// The privilege was seized by the composed coordinator.
    Seized {
        to: u64,
    },
    /// A stale holder learned the truth.
    Reconciled {
        node: u64,
    },
}

struct Inner {
    /// The routing record of the whole cluster: every node's holder pointer,
    /// queue and flags, the requests sent (never shrinking, and delivery does not
    /// consume — the model's `requests`, for the model's reason), and where the
    /// privilege **actually** is, which is not derived from any holder pointer.
    /// Verified code: each method on it is a model step.
    table: RayTable,
    log: Vec<Event>,
}

/// The routing record of a whole cluster, behind one lock.
#[derive(Clone)]
pub struct Router {
    inner: Arc<Mutex<Inner>>,
    /// Connection address to node number. The stated assumption; see the module
    /// docs.
    roster: Arc<HashMap<IpAddr, u64>>,
}

impl Router {
    /// A router whose privilege starts at `root`, with `parent[n]` the next hop
    /// from every other node `n` towards it.
    ///
    /// The shape is checked, because `ray_init` is: every non-root node must
    /// point somewhere other than itself, at a node on the roster, and following
    /// the pointers from any node must reach `root` — a pointer cycle off to
    /// one side of the root satisfies "exactly one root" and is not a Raymond
    /// state (`ray_acyclic`).
    pub fn new(
        roster: HashMap<IpAddr, u64>,
        root: u64,
        parent: HashMap<u64, u64>,
    ) -> io::Result<Self> {
        let nodes: HashSet<u64> = roster.values().copied().collect();
        let bad = |why: String| Err(io::Error::new(io::ErrorKind::InvalidInput, why));
        if !nodes.contains(&root) {
            return bad(format!("root {root} is not on the roster"));
        }
        let mut holder = HashMap::new();
        for &n in &nodes {
            if n == root {
                holder.insert(n, n);
                continue;
            }
            match parent.get(&n) {
                None => return bad(format!("node {n} has no parent")),
                Some(&p) if p == n => return bad(format!("node {n} is its own parent")),
                Some(&p) if !nodes.contains(&p) => {
                    return bad(format!("node {n}'s parent {p} is not on the roster"))
                }
                Some(&p) => {
                    holder.insert(n, p);
                }
            }
        }
        for &n in &nodes {
            let mut at = n;
            for _ in 0..=nodes.len() {
                if at == root {
                    break;
                }
                at = holder[&at];
            }
            if at != root {
                return bad(format!("node {n} does not reach the root"));
            }
        }
        let mut table = RayTable::new(root);
        for (&n, &h) in &holder {
            if n != root {
                table.add_node(n, h);
            }
        }
        Ok(Router {
            inner: Arc::new(Mutex::new(Inner {
                table,
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
        })
    }

    /// Every node points straight at `root`.
    pub fn star(roster: HashMap<IpAddr, u64>, root: u64) -> io::Result<Self> {
        let parent = roster
            .values()
            .filter(|&&n| n != root)
            .map(|&n| (n, root))
            .collect();
        Router::new(roster, root, parent)
    }

    /// Where the privilege actually is.
    pub fn privilege(&self) -> u64 {
        self.inner.lock().expect("router lock").table.privilege
    }

    /// What has happened, oldest first.
    pub fn log(&self) -> Vec<Event> {
        self.inner.lock().expect("router lock").log.clone()
    }

    /// A node's queue, front first.
    pub fn queue_of(&self, node: u64) -> Option<Vec<u64>> {
        let g = self.inner.lock().expect("router lock");
        let i = g.table.find(node)?;
        Some(g.table.entries[i].queue.iter().copied().collect())
    }

    /// A node's own entries, or `None` for a non-node.
    pub fn standing_of(&self, node: u64) -> Option<Standing> {
        let g = self.inner.lock().expect("router lock");
        Self::standing_locked(&g, node)
    }

    /// **The routing layer's invariant, checked on the live table** — the
    /// executable shadow of `ray_inv`, for tests and for a deployment that wants
    /// to assert it.
    ///
    /// The node holding the privilege believes it does
    /// (`ray_authority_believes`), every node inside its critical section
    /// believes it holds the privilege (`ray_using_implies_belief`), and
    /// following holder pointers from anywhere reaches a node that points at
    /// itself (`ray_acyclic`).
    ///
    /// **Not** "reaches the privilege". `ray_acyclic` permits several roots, and
    /// it has to: after a seizure the old holder still believes, so there are
    /// two, and [`Router::stale_holders`] names the one that is wrong. A check
    /// that insisted on one root would call the composed machine's own reachable
    /// states malformed.
    pub fn well_formed(&self) -> bool {
        let g = self.inner.lock().expect("router lock");
        let holder: HashMap<u64, u64> = g.table.entries.iter().map(|e| (e.id, e.holder)).collect();
        let n = holder.len();
        holder.get(&g.table.privilege) == Some(&g.table.privilege)
            && g.table
                .entries
                .iter()
                .all(|e| !e.using || holder[&e.id] == e.id)
            && holder.keys().all(|&start| {
                let mut at = start;
                for _ in 0..=n {
                    if holder[&at] == at {
                        return true;
                    }
                    at = holder[&at];
                }
                false
            })
    }

    /// The nodes that believe they hold the privilege and do not
    /// (`is_stale_holder`). Empty unless the privilege has been seized.
    pub fn stale_holders(&self) -> Vec<u64> {
        let g = self.inner.lock().expect("router lock");
        let mut stale: Vec<u64> = g
            .table
            .entries
            .iter()
            .filter(|e| e.holder == e.id && e.id != g.table.privilege)
            .map(|e| e.id)
            .collect();
        stale.sort_unstable();
        stale
    }

    /// Run `f` on the verified routing record and the audit log, under the lock.
    ///
    /// For the composed coordinator, which takes the registry's lock and then
    /// this one, behind its own gate, and runs a step across both layers
    /// (`crate::composed::exec`) — `ray_seize` and `ray_reconcile` among them,
    /// which no node may ask for.
    pub(crate) fn with_state<R>(&self, f: impl FnOnce(&mut RayTable, &mut Vec<Event>) -> R) -> R {
        let mut g = self.inner.lock().expect("router lock");
        let Inner { table, log } = &mut *g;
        f(table, log)
    }

    fn standing_locked(g: &Inner, node: u64) -> Option<Standing> {
        let e = &g.table.entries[g.table.find(node)?];
        Some(Standing {
            holder: e.holder,
            asked: e.asked,
            using: e.using,
            queued: e.queue.len() as u64,
            privileged: g.table.privilege == node,
        })
    }

    fn caller(&self, ctx: &Context) -> Result<u64> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) => self
                .roster
                .get(addr)
                .copied()
                .ok_or_else(|| refuse_no("unknown caller")),
            _ => Err(refuse_no("unknown caller")),
        }
    }

}

impl Routing for Router {
    async fn standing(&self, ctx: Context) -> Result<Standing> {
        let me = self.caller(&ctx)?;
        let g = self.inner.lock().expect("router lock");
        Ok(Self::standing_locked(&g, me).expect("a rostered caller has entries"))
    }

    async fn request_cs(&self, ctx: Context) -> Result<()> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        g.table.request_cs(me).map_err(refuse)?;
        g.log.push(Event::Requested { node: me });
        Ok(())
    }

    async fn make_request(&self, ctx: Context) -> Result<u64> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        let dest = g.table.make_request(me).map_err(refuse)?;
        g.log.push(Event::Forwarded { from: me, to: dest });
        Ok(dest)
    }

    async fn receive_request(&self, ctx: Context, from: u64) -> Result<()> {
        let at = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        g.table.receive_request(at, from).map_err(refuse)?;
        g.log.push(Event::Received { at, from });
        Ok(())
    }

    async fn assign_privilege(&self, ctx: Context) -> Result<u64> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        // Both nodes act, as in the model: the holder rewrites its own pointer
        // and the recipient learns it holds the privilege, in one step.
        let head = g.table.assign_privilege(me).map_err(refuse)?;
        g.log.push(Event::Passed { from: me, to: head });
        Ok(head)
    }

    async fn enter_cs(&self, ctx: Context) -> Result<()> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        g.table.enter_cs(me).map_err(refuse)?;
        g.log.push(Event::Entered { node: me });
        Ok(())
    }

    async fn exit_cs(&self, ctx: Context) -> Result<()> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        g.table.exit_cs(me).map_err(refuse)?;
        g.log.push(Event::Exited { node: me });
        Ok(())
    }
}
