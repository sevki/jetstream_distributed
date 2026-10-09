//! The router: the whole routing record of a cluster, behind one lock.

use std::collections::{HashMap, HashSet, VecDeque};
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use super::refusal::{refuse, refuse_err, refuse_no};
use super::{Routing, Standing};
use crate::raymond::steps::{
    assign_step, enter_cs_step, exit_cs_step, make_request_step, receive_request_step,
};
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
    holder: HashMap<u64, u64>,
    queue: HashMap<u64, VecDeque<u64>>,
    asked: HashMap<u64, bool>,
    using: HashMap<u64, bool>,
    /// Every request ever sent, as `(originator, destination)`. Never shrinks,
    /// and delivery does not consume — the model's `requests`, for the model's
    /// reason.
    requests: HashSet<(u64, u64)>,
    /// Where the privilege **actually** is. Not derived from `holder`.
    privilege: u64,
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
        Ok(Router {
            inner: Arc::new(Mutex::new(Inner {
                queue: nodes.iter().map(|&n| (n, VecDeque::new())).collect(),
                asked: nodes.iter().map(|&n| (n, false)).collect(),
                using: nodes.iter().map(|&n| (n, false)).collect(),
                holder,
                requests: HashSet::new(),
                privilege: root,
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
        self.inner.lock().expect("router lock").privilege
    }

    /// What has happened, oldest first.
    pub fn log(&self) -> Vec<Event> {
        self.inner.lock().expect("router lock").log.clone()
    }

    /// A node's queue, front first.
    pub fn queue_of(&self, node: u64) -> Option<Vec<u64>> {
        let g = self.inner.lock().expect("router lock");
        g.queue.get(&node).map(|q| q.iter().copied().collect())
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
        let n = g.holder.len();
        g.holder.get(&g.privilege) == Some(&g.privilege)
            && g.using
                .iter()
                .all(|(node, &u)| !u || g.holder[node] == *node)
            && g.holder.keys().all(|&start| {
                let mut at = start;
                for _ in 0..=n {
                    if g.holder[&at] == at {
                        return true;
                    }
                    at = g.holder[&at];
                }
                false
            })
    }

    /// The nodes that believe they hold the privilege and do not
    /// (`is_stale_holder`). Empty unless the privilege has been seized.
    pub fn stale_holders(&self) -> Vec<u64> {
        let g = self.inner.lock().expect("router lock");
        let mut stale: Vec<u64> = g
            .holder
            .iter()
            .filter(|&(&n, &h)| h == n && n != g.privilege)
            .map(|(&n, _)| n)
            .collect();
        stale.sort_unstable();
        stale
    }

    /// Is `node` a node of this cluster?
    pub(crate) fn is_node(&self, node: u64) -> bool {
        self.inner
            .lock()
            .expect("router lock")
            .holder
            .contains_key(&node)
    }

    /// Does `node` believe it holds the privilege? (`believes_holds`.)
    pub(crate) fn believes_holds(&self, node: u64) -> bool {
        self.inner.lock().expect("router lock").holder.get(&node) == Some(&node)
    }

    /// `ray_seize`: re-establish the privilege at `to`. **Only `to` acts** —
    /// nothing belonging to the old holder is touched, because it is memory at a
    /// node that may be unreachable. The guards are the composed coordinator's,
    /// which is the only caller.
    pub(crate) fn seize_to(&self, to: u64) {
        let mut g = self.inner.lock().expect("router lock");
        g.holder.insert(to, to);
        g.privilege = to;
        g.log.push(Event::Seized { to });
    }

    /// `ray_reconcile`: a stale holder learns its privilege was taken.
    pub(crate) fn reconcile_node(&self, node: u64) {
        let mut g = self.inner.lock().expect("router lock");
        let privilege = g.privilege;
        g.holder.insert(node, privilege);
        g.using.insert(node, false);
        g.asked.insert(node, false);
        g.log.push(Event::Reconciled { node });
    }

    fn standing_locked(g: &Inner, node: u64) -> Option<Standing> {
        Some(Standing {
            holder: *g.holder.get(&node)?,
            asked: g.asked[&node],
            using: g.using[&node],
            queued: g.queue[&node].len() as u64,
            privileged: g.privilege == node,
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

    fn head_of(g: &Inner, node: u64) -> (u64, u64) {
        let q = &g.queue[&node];
        (q.len() as u64, q.front().copied().unwrap_or(0))
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
        g.queue.get_mut(&me).expect("rostered").push_back(me);
        g.log.push(Event::Requested { node: me });
        Ok(())
    }

    async fn make_request(&self, ctx: Context) -> Result<u64> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        let (queue_len, _) = Self::head_of(&g, me);
        let dest = make_request_step(me, g.holder[&me], queue_len, g.asked[&me]).map_err(refuse)?;
        g.asked.insert(me, true);
        g.requests.insert((me, dest));
        g.log.push(Event::Forwarded { from: me, to: dest });
        Ok(dest)
    }

    async fn receive_request(&self, ctx: Context, from: u64) -> Result<()> {
        let at = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        if !g.holder.contains_key(&from) {
            return Err(refuse_err("not a node"));
        }
        receive_request_step(g.requests.contains(&(from, at))).map_err(refuse)?;
        g.queue.get_mut(&at).expect("rostered").push_back(from);
        g.log.push(Event::Received { at, from });
        Ok(())
    }

    async fn assign_privilege(&self, ctx: Context) -> Result<u64> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        let (queue_len, head) = Self::head_of(&g, me);
        let head_is_node = g.holder.contains_key(&head);
        let head = assign_step(
            me,
            g.privilege,
            g.holder[&me],
            g.using[&me],
            queue_len,
            head,
            head_is_node,
        )
        .map_err(refuse)?;
        // Both nodes act, as in the model: the holder rewrites its own pointer
        // and the recipient learns it holds the privilege, in one step.
        g.holder.insert(me, head);
        g.holder.insert(head, head);
        g.privilege = head;
        g.queue.get_mut(&me).expect("rostered").pop_front();
        g.asked.insert(me, false);
        g.log.push(Event::Passed { from: me, to: head });
        Ok(head)
    }

    async fn enter_cs(&self, ctx: Context) -> Result<()> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        let (queue_len, head) = Self::head_of(&g, me);
        enter_cs_step(me, g.holder[&me], g.using[&me], queue_len, head).map_err(refuse)?;
        g.using.insert(me, true);
        g.queue.get_mut(&me).expect("rostered").pop_front();
        g.log.push(Event::Entered { node: me });
        Ok(())
    }

    async fn exit_cs(&self, ctx: Context) -> Result<()> {
        let me = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("router lock");
        exit_cs_step(g.using[&me]).map_err(refuse)?;
        g.using.insert(me, false);
        g.log.push(Event::Exited { node: me });
        Ok(())
    }
}
