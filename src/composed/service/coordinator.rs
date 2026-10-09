//! The coordinator: the two layers, and the coupling between them.

use std::collections::{HashMap, HashSet};
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use super::refusal::{refuse, refuse_no};
use super::Composed;
use crate::composed::steps::{
    acquire_under_token_step, pass_token_step, reconcile_step, seize_step,
};
use crate::ownership::service::{EpochFloor, Event as OwnershipEvent, Offer, Ownership, Registry};
use crate::raymond::service::{Event as RoutingEvent, Router, Routing, Standing};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// What the coordinator did on its own account. The layers keep their own logs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// The privilege was taken from `from` and re-established at `to`.
    Seized { from: u64, to: u64 },
    /// `node` reconciled.
    Reconciled { node: u64 },
}

struct Debts {
    /// Nodes whose privilege was seized and whose belief has not been repaired:
    /// the nodes that **owe a reconciliation**. `composed_inv` ties this set to
    /// the routing layer — every stale holder is in it.
    seized: HashSet<u64>,
    log: Vec<Event>,
}

/// The two layers and the coupling between them.
///
/// Neither layer is reachable from outside: they are built inside
/// [`Coordinator::new`] and only read-only views are exposed, because every
/// method of the layers' service traits takes `&self` and would bypass the gate
/// and the coupling.
#[derive(Clone)]
pub struct Coordinator {
    registry: Registry,
    router: Router,
    /// Serialises every method, so a decision that reads both layers acts on
    /// what it read. Held across the layers' own (immediate) `await`s, hence an
    /// async mutex.
    gate: Arc<tokio::sync::Mutex<()>>,
    debts: Arc<Mutex<Debts>>,
    roster: Arc<HashMap<IpAddr, u64>>,
}

impl Coordinator {
    /// Build both layers from **one** roster and compose them.
    ///
    /// The ownership actor starts offered to `first_owner`, and the privilege
    /// starts at `root` with `parent[n]` the next hop from every other node
    /// towards it (see [`Router::new`] for what is checked about that shape).
    ///
    /// The layers are built here rather than handed in, for two reasons that are
    /// the same reason. The coupling reads both layers in one decision, so it is
    /// only sound if nothing else can touch either: a caller holding the
    /// `Registry` or `Router` could route a waiter and pass the privilege while
    /// authority sat at the old owner, bypassing the gate and `pass_token_step`
    /// both. And three rosters supplied separately can disagree about which
    /// address is which node, so the coordinator would check one node's
    /// privilege and then grant authority to another with the same `Context`.
    /// One roster, owned here, closes both.
    pub fn new(
        roster: HashMap<IpAddr, u64>,
        first_owner: u64,
        floor: Arc<dyn EpochFloor>,
        root: u64,
        parent: HashMap<u64, u64>,
    ) -> io::Result<Self> {
        let registry = Registry::new(roster.clone(), first_owner, floor)?;
        let router = Router::new(roster.clone(), root, parent)?;
        Ok(Coordinator {
            registry,
            router,
            gate: Arc::new(tokio::sync::Mutex::new(())),
            debts: Arc::new(Mutex::new(Debts {
                seized: HashSet::new(),
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
        })
    }

    /// As [`Coordinator::new`], with every other node pointing straight at
    /// `root`.
    pub fn star(
        roster: HashMap<IpAddr, u64>,
        first_owner: u64,
        floor: Arc<dyn EpochFloor>,
        root: u64,
    ) -> io::Result<Self> {
        let parent = roster
            .values()
            .filter(|&&n| n != root)
            .map(|&n| (n, root))
            .collect();
        Coordinator::new(roster, first_owner, floor, root, parent)
    }

    /// Where the privilege actually is.
    pub fn privilege(&self) -> u64 {
        self.router.privilege()
    }

    /// The routing layer's invariant, checked on the live table. See
    /// [`Router::well_formed`].
    pub fn well_formed(&self) -> bool {
        self.router.well_formed()
    }

    /// The nodes that believe they hold the privilege and do not. See
    /// [`Router::stale_holders`].
    pub fn stale_holders(&self) -> Vec<u64> {
        self.router.stale_holders()
    }

    /// A node's own routing entries, or `None` for a non-node.
    pub fn standing_of(&self, node: u64) -> Option<Standing> {
        self.router.standing_of(node)
    }

    /// The routing layer's log, oldest first.
    pub fn routing_log(&self) -> Vec<RoutingEvent> {
        self.router.log()
    }

    /// The ownership layer's audit log, oldest first.
    pub fn ownership_log(&self) -> Vec<OwnershipEvent> {
        self.registry.log()
    }

    /// What the coordinator itself has done, oldest first.
    pub fn log(&self) -> Vec<Event> {
        self.debts.lock().expect("debts lock").log.clone()
    }

    /// The nodes that owe a reconciliation, in order.
    pub fn seized(&self) -> Vec<u64> {
        let mut v: Vec<u64> = self
            .debts
            .lock()
            .expect("debts lock")
            .seized
            .iter()
            .copied()
            .collect();
        v.sort_unstable();
        v
    }

    /// `SeizeToken`: take the privilege from whoever holds it and re-establish
    /// it at `to`, **without the holder acting**. Returns the node it was taken
    /// from.
    ///
    /// Inherent rather than on the trait: no node may cause this. The guard is
    /// the same `Unowned` as [`Composed::assign_privilege`]'s, for the same
    /// reason — with nobody holding authority, moving the privilege cannot
    /// strand any. Seizure is safe for exactly the reason a revocation is: the
    /// epoch was burned first.
    ///
    /// Nothing belonging to the old holder is touched. It is left a stale
    /// holder — it believes it holds the privilege, it does not — and owes a
    /// reconciliation.
    pub async fn seize_token(&self, to: u64) -> Result<u64> {
        let _gate = self.gate.lock().await;
        let from = self.router.privilege();
        seize_step(
            self.registry.actor_is_unowned(),
            from,
            self.router.privilege(),
            to,
            self.router.is_node(to),
        )
        .map_err(refuse)?;
        self.router.seize_to(to);
        let mut d = self.debts.lock().expect("debts lock");
        d.seized.insert(from);
        d.seized.remove(&to);
        d.log.push(Event::Seized { from, to });
        Ok(from)
    }

    /// The coordinator forcing progress on the ownership layer: revoke, reassign
    /// or abort. See [`Registry::force`]. Carried by `cs_own`.
    pub async fn force(&self, next: u64) -> Result<u64> {
        let _gate = self.gate.lock().await;
        self.registry.force(next)
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

impl Composed for Coordinator {
    async fn poll(&self, ctx: Context) -> Result<Offer> {
        let _gate = self.gate.lock().await;
        self.registry.poll(ctx).await
    }

    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()> {
        let _gate = self.gate.lock().await;
        let node = self.caller(&ctx)?;
        acquire_under_token_step(self.router.privilege(), node).map_err(refuse)?;
        self.registry.acquire(ctx, epoch).await
    }

    async fn write(&self, ctx: Context, epoch: u64) -> Result<u64> {
        let _gate = self.gate.lock().await;
        self.registry.write(ctx, epoch).await
    }

    async fn begin_transfer(&self, ctx: Context, to: u64) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.registry.begin_transfer(ctx, to).await
    }

    async fn release(&self, ctx: Context, epoch: u64) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.registry.release(ctx, epoch).await
    }

    async fn standing(&self, ctx: Context) -> Result<Standing> {
        let _gate = self.gate.lock().await;
        self.router.standing(ctx).await
    }

    async fn request_cs(&self, ctx: Context) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.router.request_cs(ctx).await
    }

    async fn make_request(&self, ctx: Context) -> Result<u64> {
        let _gate = self.gate.lock().await;
        self.router.make_request(ctx).await
    }

    async fn receive_request(&self, ctx: Context, from: u64) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.router.receive_request(ctx, from).await
    }

    async fn enter_cs(&self, ctx: Context) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.router.enter_cs(ctx).await
    }

    async fn exit_cs(&self, ctx: Context) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.router.exit_cs(ctx).await
    }

    async fn assign_privilege(&self, ctx: Context) -> Result<u64> {
        let _gate = self.gate.lock().await;
        // The coupling first, so that a refusal names it rather than whichever
        // routing guard happens to fail too.
        pass_token_step(self.registry.actor_is_unowned()).map_err(refuse)?;
        let head = self.router.assign_privilege(ctx).await?;
        // Receiving the privilege *is* the node learning the truth, so any
        // reconciliation it owed is settled by the handover itself.
        self.debts.lock().expect("debts lock").seized.remove(&head);
        Ok(head)
    }

    async fn reconcile(&self, ctx: Context) -> Result<()> {
        let _gate = self.gate.lock().await;
        let node = self.caller(&ctx)?;
        let owes = self
            .debts
            .lock()
            .expect("debts lock")
            .seized
            .contains(&node);
        reconcile_step(
            owes,
            self.router.believes_holds(node),
            self.router.privilege() == node,
        )
        .map_err(refuse)?;
        self.router.reconcile_node(node);
        let mut d = self.debts.lock().expect("debts lock");
        d.seized.remove(&node);
        d.log.push(Event::Reconciled { node });
        Ok(())
    }
}
