//! Ownership and Raymond, behind one coordinator, over Jetstream RPC.
//!
//! The composition is not an algorithm of its own — it is two, with the coupling
//! between them made a **guard**. So this service is the two existing ones
//! ([`Registry`] and [`Router`]) and the guards that tie them together, and
//! almost all of it is delegation. What it adds is small and is the whole point:
//!
//! * **the privilege moves only once the actor has been released.**
//!   [`Composed::assign_privilege`] refuses while the actor is `Owned` or
//!   `Transferring`, however willing the routing layer is
//!   (`cs_pass_token`, [`crate::composed::steps::pass_token_step`]);
//! * **authority is taken only by the node holding the privilege.**
//!   [`Composed::acquire`] refuses a node the routing layer has not elected
//!   (`cs_acquire_under_token`);
//! * **the privilege can be taken from a holder that does not cooperate**
//!   ([`Coordinator::seize_token`], `cs_seize_token`), and the node it was taken
//!   from owes a reconciliation ([`Composed::reconcile`], `cs_reconcile`).
//!
//! Everything else is carried: a routing step is the Raymond layer's own
//! (`cs_ray`) and an ownership step is the ownership layer's own (`cs_own`), and
//! `crate::composed::proofs::refinement` proves that carrying a step the layers
//! have already proved correct needs no second proof.
//!
//! # Why one coordinator, and why a gate
//!
//! The coupling reads **both** layers' state in one decision: `assign_privilege`
//! asks the registry whether the actor is `Unowned` and then moves the
//! privilege. Two locks, taken one after the other, would leave a gap between
//! the question and the move — and the gap is exactly the race the guard
//! exists to close. Say the registry answers "unowned", an `acquire` slips in
//! (the caller still holds the privilege, so the coupling lets it), and then the
//! privilege moves: authority stranded at a node that no longer holds the
//! privilege. So every method takes one **gate** first, and the two layers
//! underneath it are never shared with anything else. The registry and router a
//! [`Coordinator`] is built from must not be used directly afterwards, which is
//! why construction takes them by value.
//!
//! # Liveness, stated
//!
//! The composed *model* guards some steps on `own.live`, which is ground truth.
//! This service has no `Crash` or `Recover`: it refines the composed machine's
//! executions in which no node crashes. See [`crate::composed::steps`] for the
//! argument, and for why that still covers the case the machine exists for —
//! taking the privilege from a holder that is merely unreachable.
//!
//! # The assumption this rests on, stated
//!
//! The same one the other services state: a caller is identified by
//! [`Context::remote`] against a roster fixed at construction, and an address is
//! not a credential.

use std::collections::{HashMap, HashSet};
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use crate::composed::steps::{
    acquire_under_token_step, pass_token_step, reconcile_step, seize_step, CoupledRefusal,
};
use crate::ownership::service::{Offer, Ownership, Registry};
use crate::raymond::service::{Router, Routing, Standing};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// The node-facing protocol: the ownership layer's five calls, the routing
/// layer's six, and the one step that belongs to neither.
///
/// None takes the acting node's number. Seizing the privilege is **not** here:
/// it is the coordinator's own step, and a node-facing service that offered it
/// would let any node take the privilege from the one that holds it.
#[service(uses(super::{Offer, Standing}))]
pub trait Composed {
    // --- ownership, carried ---------------------------------------------

    /// What is on offer for the caller?
    async fn poll(&self, ctx: Context) -> Result<Offer>;

    /// `AcquireUnderToken`: take an offered grant — **only if the caller holds
    /// the privilege.**
    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()>;

    /// Write as the current owner, returning the sequence number.
    async fn write(&self, ctx: Context, epoch: u64) -> Result<u64>;

    /// The owner agrees to hand the actor to `to`.
    async fn begin_transfer(&self, ctx: Context, to: u64) -> Result<()>;

    /// The outgoing owner acknowledges the revocation.
    async fn release(&self, ctx: Context, epoch: u64) -> Result<()>;

    // --- routing, carried -----------------------------------------------

    /// What do my own routing entries say?
    async fn standing(&self, ctx: Context) -> Result<Standing>;

    /// I want the privilege.
    async fn request_cs(&self, ctx: Context) -> Result<()>;

    /// Forward my request one hop towards the privilege.
    async fn make_request(&self, ctx: Context) -> Result<u64>;

    /// A request `from` sent to me arrives.
    async fn receive_request(&self, ctx: Context, from: u64) -> Result<()>;

    /// I enter my critical section.
    async fn enter_cs(&self, ctx: Context) -> Result<()>;

    /// I leave it.
    async fn exit_cs(&self, ctx: Context) -> Result<()>;

    // --- the coupling ---------------------------------------------------

    /// `PassToken`: hand the privilege to the head of my queue — **only once
    /// the actor has been released.** Returns who got it.
    async fn assign_privilege(&self, ctx: Context) -> Result<u64>;

    /// `Reconcile`: the privilege was taken from me. I drop the belief that I
    /// hold it and leave the critical section I thought I was in.
    async fn reconcile(&self, ctx: Context) -> Result<()>;
}

fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

fn refuse(why: CoupledRefusal) -> Error {
    match why {
        CoupledRefusal::ActorNotReleased => {
            refuse_no("the actor has not been released; the privilege may not move")
        }
        CoupledRefusal::NotPrivileged => {
            refuse_no("only the node holding the privilege may acquire")
        }
        CoupledRefusal::NothingToSeize => {
            refuse_no("nothing to seize: the target already holds it")
        }
        CoupledRefusal::NotANode => refuse_err("not a node"),
        CoupledRefusal::NotSeized => refuse_no("this node owes no reconciliation"),
        CoupledRefusal::NotStale => refuse_no("this node's belief is not stale"),
    }
}

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
    /// Compose a registry and a router built over the same roster.
    ///
    /// By value, because the coupling is only sound if nothing else touches
    /// either: see the module docs.
    pub fn new(registry: Registry, router: Router, roster: HashMap<IpAddr, u64>) -> Self {
        Coordinator {
            registry,
            router,
            gate: Arc::new(tokio::sync::Mutex::new(())),
            debts: Arc::new(Mutex::new(Debts {
                seized: HashSet::new(),
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
        }
    }

    /// The ownership layer, for reading its audit log. Not for calling.
    pub fn registry(&self) -> &Registry {
        &self.registry
    }

    /// The routing layer, for reading its table. Not for calling.
    pub fn router(&self) -> &Router {
        &self.router
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
