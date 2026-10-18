//! The host: a journal, a mailbox, and the registry that fences them.

use std::collections::HashMap;
use std::io;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use super::refusal::{refuse, refuse_err, refuse_no};
use super::{Actor, Receipt, Record, Snapshot, MAX_READ};
use crate::actor::steps::{accept_step, apply_step, send_step};
use crate::ownership::service::{EpochFloor, Event as OwnershipEvent, Offer, Ownership, Registry};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// What the host accepted, in the order it accepted it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    Sent {
        sender: u64,
        seq: u64,
    },
    Accepted {
        host: u64,
        epoch: u64,
        sender: u64,
        seq: u64,
        index: u64,
    },
}

struct Inner {
    /// Every message ever sent, by `(sender, seq)`. Never shrinks, and accepting
    /// does not consume — the model's `sent`, for the model's reason.
    sent: HashMap<(u64, u64), u64>,
    /// Each sender's next sequence number.
    next_seq: HashMap<u64, u64>,
    /// The journal.
    journal: Vec<Record>,
    /// How many messages the journal holds from each sender: the count
    /// `accept_step` is handed. Kept beside the journal so an append is constant
    /// time, and checked against it by `accepted_from`.
    accepted: HashMap<u64, u64>,
    /// The state the journal folds to.
    state: u64,
    log: Vec<Event>,
}

/// One distributed actor.
#[derive(Clone)]
pub struct Host {
    registry: Registry,
    /// Serialises every method, so a decision that reads the registry and then
    /// writes the journal acts on what it read. Held across the registry's own
    /// (immediate) `await`s, hence an async mutex.
    gate: Arc<tokio::sync::Mutex<()>>,
    inner: Arc<Mutex<Inner>>,
    /// Connection address to node number. The stated assumption; see the module
    /// docs.
    roster: Arc<HashMap<IpAddr, u64>>,
}

impl Host {
    /// An actor offered to `first_owner`, over the nodes on `roster`.
    ///
    /// The ownership registry is built here, from the one roster and the given
    /// epoch floor, and nothing outside can hold it: every method of the
    /// `Ownership` trait takes `&self`, so a handle to the registry would be a
    /// handle to `write`, bypassing the gate. See the module docs.
    pub fn new(
        roster: HashMap<IpAddr, u64>,
        first_owner: u64,
        floor: Arc<dyn EpochFloor>,
    ) -> io::Result<Self> {
        let registry = Registry::new(roster.clone(), first_owner, floor)?;
        Ok(Host {
            registry,
            gate: Arc::new(tokio::sync::Mutex::new(())),
            inner: Arc::new(Mutex::new(Inner {
                sent: HashMap::new(),
                next_seq: HashMap::new(),
                journal: Vec::new(),
                accepted: HashMap::new(),
                state: 0,
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
        })
    }

    /// The actor, as of the journal's end.
    pub fn snapshot(&self) -> Snapshot {
        let g = self.inner.lock().expect("host lock");
        Snapshot {
            len: g.journal.len() as u64,
            state: g.state,
        }
    }

    /// The whole journal.
    pub fn records(&self) -> Vec<Record> {
        self.inner.lock().expect("host lock").journal.clone()
    }

    /// What the host has done, oldest first.
    pub fn log(&self) -> Vec<Event> {
        self.inner.lock().expect("host lock").log.clone()
    }

    /// The ownership layer's audit log, oldest first.
    pub fn ownership_log(&self) -> Vec<OwnershipEvent> {
        self.registry.log()
    }

    /// The coordinator forcing progress on the ownership layer: revoke,
    /// reassign or abort. See `Registry::force`.
    ///
    /// Inherent, not on the trait: no node may cause it.
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

impl Actor for Host {
    async fn poll(&self, ctx: Context) -> Result<Offer> {
        let _gate = self.gate.lock().await;
        self.registry.poll(ctx).await
    }

    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.registry.acquire(ctx, epoch).await
    }

    async fn begin_transfer(&self, ctx: Context, to: u64) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.registry.begin_transfer(ctx, to).await
    }

    async fn release(&self, ctx: Context, epoch: u64) -> Result<()> {
        let _gate = self.gate.lock().await;
        self.registry.release(ctx, epoch).await
    }

    async fn send(&self, ctx: Context, body: u64) -> Result<u64> {
        let _gate = self.gate.lock().await;
        let sender = self.caller(&ctx)?;
        let mut g = self.inner.lock().expect("host lock");
        let next = g.next_seq.get(&sender).copied().unwrap_or(0);
        let seq = send_step(next).map_err(refuse)?;
        g.sent.insert((sender, seq), body);
        g.next_seq.insert(sender, seq + 1);
        g.log.push(Event::Sent { sender, seq });
        Ok(seq)
    }

    async fn accept(&self, ctx: Context, epoch: u64, sender: u64, seq: u64) -> Result<Receipt> {
        let _gate = self.gate.lock().await;
        let host = self.caller(&ctx)?;
        let (body, index, state) = {
            let g = self.inner.lock().expect("host lock");
            let sent = g.sent.get(&(sender, seq)).copied();
            let accepted = g.accepted.get(&sender).copied().unwrap_or(0);
            // The fence is asked first and about the registry's own record, so a
            // host that is not the owner learns nothing about the journal.
            accept_step(
                self.registry.may_write(host, epoch),
                sent.is_some(),
                seq,
                accepted,
            )
            .map_err(refuse)?;
            let body = sent.expect("accept_step checked the message was sent");
            (body, g.journal.len() as u64, apply_step(g.state, body))
        };
        // The effect the fence guards. It makes the same check under the
        // registry's lock, which cannot disagree with the one above: nothing else
        // can reach the registry while the gate is held.
        self.registry.write(ctx, epoch).await?;
        let mut g = self.inner.lock().expect("host lock");
        g.journal.push(Record {
            sender,
            seq,
            body,
            host,
            epoch,
        });
        *g.accepted.entry(sender).or_insert(0) += 1;
        g.state = state;
        g.log.push(Event::Accepted {
            host,
            epoch,
            sender,
            seq,
            index,
        });
        Ok(Receipt { index, body, state })
    }

    async fn state(&self, ctx: Context) -> Result<Snapshot> {
        self.caller(&ctx)?;
        Ok(self.snapshot())
    }

    async fn journal(&self, ctx: Context, from: u64, limit: u64) -> Result<Vec<Record>> {
        self.caller(&ctx)?;
        if limit > MAX_READ {
            return Err(refuse_err("too many records in one read"));
        }
        let g = self.inner.lock().expect("host lock");
        Ok(g.journal
            .iter()
            .skip(from as usize)
            .take(limit as usize)
            .copied()
            .collect())
    }
}
