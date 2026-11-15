//! The coordinator: the two layers, and the coupling between them.

use std::collections::HashMap;
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use super::command::{apply, Command, Reply};
use super::refusal::{refuse, refuse_no};
use super::Composed;
use crate::composed::exec::ComposedError;
use crate::ownership::service::{EpochFloor, Event as OwnershipEvent, Offer, Ownership, Registry};
use crate::raymond::service::{Event as RoutingEvent, Router, Routing, Standing};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use crate::id::{Id, IdSet};
use jetstream::prelude::*;

/// What the coordinator did on its own account. The layers keep their own logs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// The privilege was taken from `from` and re-established at `to`.
    Seized { from: Id, to: Id },
    /// `node` reconciled.
    Reconciled { node: Id },
}

struct Debts {
    /// Nodes whose privilege was seized and whose belief has not been repaired:
    /// the nodes that **owe a reconciliation**. `composed_inv` ties this set to
    /// the routing layer — every stale holder is in it.
    seized: IdSet,
    log: Vec<Event>,
}

/// A composed step's refusal in the line protocol's alphabet: the coupling's,
/// or one of the layers' own.
fn refuse_composed(why: ComposedError) -> Error {
    match why {
        ComposedError::Coupled(why) => refuse(why),
        ComposedError::Ray(why) => crate::raymond::service::refusal::refuse(why),
        ComposedError::Own(why) => crate::ownership::service::refuse(why),
    }
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
    roster: Arc<HashMap<IpAddr, Id>>,
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
        roster: HashMap<IpAddr, Id>,
        first_owner: Id,
        floor: Arc<dyn EpochFloor>,
        root: Id,
        parent: HashMap<Id, Id>,
    ) -> io::Result<Self> {
        let registry = Registry::new(roster.clone(), first_owner, floor)?;
        let router = Router::new(roster.clone(), root, parent)?;
        Ok(Coordinator {
            registry,
            router,
            gate: Arc::new(tokio::sync::Mutex::new(())),
            debts: Arc::new(Mutex::new(Debts {
                seized: IdSet::new(),
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
        })
    }

    /// As [`Coordinator::new`], with every other node pointing straight at
    /// `root`.
    pub fn star(
        roster: HashMap<IpAddr, Id>,
        first_owner: Id,
        floor: Arc<dyn EpochFloor>,
        root: Id,
    ) -> io::Result<Self> {
        let parent = roster
            .values()
            .filter(|&&n| n != root)
            .map(|&n| (n, root))
            .collect();
        Coordinator::new(roster, first_owner, floor, root, parent)
    }

    /// Where the privilege actually is.
    pub fn privilege(&self) -> Id {
        self.router.privilege()
    }

    /// The routing layer's invariant, checked on the live table. See
    /// [`Router::well_formed`].
    pub fn well_formed(&self) -> bool {
        self.router.well_formed()
    }

    /// The nodes that believe they hold the privilege and do not. See
    /// [`Router::stale_holders`].
    pub fn stale_holders(&self) -> Vec<Id> {
        self.router.stale_holders()
    }

    /// A node's own routing entries, or `None` for a non-node.
    pub fn standing_of(&self, node: Id) -> Option<Standing> {
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
    pub fn seized(&self) -> Vec<Id> {
        let mut v: Vec<Id> = self.debts.lock().expect("debts lock").seized.iter().collect();
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
    pub async fn seize_token(&self, to: Id) -> Result<Id> {
        let _gate = self.gate.lock().await;
        match self.run(Command::Seize { to })? {
            Reply::Seized { from } => Ok(from),
            other => unreachable!("Seize answered {other:?}"),
        }
    }

    /// The coordinator forcing progress on the ownership layer: revoke, reassign
    /// or abort. See [`Registry::force`]. Carried by `cs_own`.
    pub async fn force(&self, next: Id) -> Result<Id> {
        let _gate = self.gate.lock().await;
        self.registry.force(next)
    }

    /// Run one coupling step on the two layers and the debts, and record it in the
    /// logs it belongs to. The caller holds the gate.
    ///
    /// The step is [`apply`], which is the verified function of the command's name;
    /// what is left here is taking the locks, in the order the coordinator always
    /// has (registry, router, debts), and the audit trail.
    fn run(&self, command: Command) -> Result<Reply> {
        self.registry.with_state(|own, own_log| {
            self.router.with_state(|ray, ray_log| {
                let mut d = self.debts.lock().expect("debts lock");
                let reply = apply(own, ray, &mut d.seized, command).map_err(refuse_composed)?;
                match (command, reply) {
                    (Command::Seize { to }, Reply::Seized { from }) => {
                        ray_log.push(RoutingEvent::Seized { to });
                        d.log.push(Event::Seized { from, to });
                    }
                    (Command::Pass { me }, Reply::Passed { head }) => {
                        ray_log.push(RoutingEvent::Passed { from: me, to: head });
                    }
                    (Command::Acquire { node, epoch }, Reply::Acquired) => {
                        own_log.push(OwnershipEvent::Acquired { node, epoch });
                    }
                    (Command::Reconcile { node }, Reply::Reconciled) => {
                        ray_log.push(RoutingEvent::Reconciled { node });
                        d.log.push(Event::Reconciled { node });
                    }
                    (command, reply) => unreachable!("{command:?} answered {reply:?}"),
                }
                Ok(reply)
            })
        })
    }

    fn caller(&self, ctx: &Context) -> Result<Id> {
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
        // `cs_acquire_under_token`: the ownership layer's acquire, for the node
        // holding the privilege.
        self.run(Command::Acquire { node, epoch }).map(|_| ())
    }

    async fn write(&self, ctx: Context, epoch: u64) -> Result<u64> {
        let _gate = self.gate.lock().await;
        self.registry.write(ctx, epoch).await
    }

    async fn begin_transfer(&self, ctx: Context, to: Id) -> Result<()> {
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

    async fn make_request(&self, ctx: Context) -> Result<Id> {
        let _gate = self.gate.lock().await;
        self.router.make_request(ctx).await
    }

    async fn receive_request(&self, ctx: Context, from: Id) -> Result<()> {
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

    async fn assign_privilege(&self, ctx: Context) -> Result<Id> {
        let _gate = self.gate.lock().await;
        let me = self.caller(&ctx)?;
        // `cs_pass_token`: the coupling first, so that a refusal names it rather
        // than whichever routing guard happens to fail too; and receiving the
        // privilege *is* the node learning the truth, so any reconciliation it
        // owed is settled by the handover itself.
        match self.run(Command::Pass { me })? {
            Reply::Passed { head } => Ok(head),
            other => unreachable!("Pass answered {other:?}"),
        }
    }

    async fn reconcile(&self, ctx: Context) -> Result<()> {
        let _gate = self.gate.lock().await;
        let node = self.caller(&ctx)?;
        // `cs_reconcile`: a node that owes one and really is stale.
        self.run(Command::Reconcile { node }).map(|_| ())
    }
}
