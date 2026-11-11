//! The recorder: a register per slot, behind a lock, answering proposers.

use std::collections::{BTreeMap, HashMap};
use std::net::IpAddr;
use std::sync::{Arc, Mutex};

use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

use super::{Recorder, Reply, refuse_err, refuse_no};
use crate::quepaxa::isr::Isr;

/// How many slots a recorder will keep a register for. A slot is a few integers, but
/// they are never forgotten, and a caller can name any slot.
pub const MAX_SLOTS: usize = 1 << 20;

struct Inner {
    /// One register per slot ever recorded in.
    registers: HashMap<u64, Isr>,
    /// What this recorder has been told was decided.
    learned: BTreeMap<u64, u64>,
}

/// One recorder.
#[derive(Clone)]
pub struct RecorderNode {
    inner: Arc<Mutex<Inner>>,
    /// Who may call, by connection address. The stated assumption; see the module docs
    /// of [`super`].
    roster: Arc<HashMap<IpAddr, u32>>,
}

impl RecorderNode {
    /// A recorder that answers the members in `roster` (address to proposer index).
    pub fn new(roster: HashMap<IpAddr, u32>) -> Self {
        RecorderNode {
            inner: Arc::new(Mutex::new(Inner {
                registers: HashMap::new(),
                learned: BTreeMap::new(),
            })),
            roster: Arc::new(roster),
        }
    }

    /// What this recorder was told was decided at `slot`.
    pub fn decided(&self, slot: u64) -> Option<u64> {
        self.inner
            .lock()
            .expect("recorder lock")
            .learned
            .get(&slot)
            .copied()
    }

    /// How many slots from 0 this recorder was told were decided, with no gap.
    pub fn committed(&self) -> u64 {
        let g = self.inner.lock().expect("recorder lock");
        let mut n = 0;
        while g.learned.contains_key(&n) {
            n += 1;
        }
        n
    }

    /// Record that `value` was decided at `slot`, here and now. `false` if a different
    /// value was already learned there, which the protocol says cannot happen.
    pub fn learn_local(&self, slot: u64, value: u64) -> bool {
        let mut g = self.inner.lock().expect("recorder lock");
        *g.learned.entry(slot).or_insert(value) == value
    }

    /// Every slot this recorder has learned, in order.
    pub fn learned(&self) -> Vec<(u64, u64)> {
        let g = self.inner.lock().expect("recorder lock");
        g.learned.iter().map(|(&s, &v)| (s, v)).collect()
    }

    fn check_caller(&self, ctx: &Context) -> Result<()> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) if self.roster.contains_key(addr) => Ok(()),
            _ => Err(refuse_no("unknown caller")),
        }
    }
}

impl Recorder for RecorderNode {
    async fn record(&self, ctx: Context, slot: u64, step: u64, value: u128) -> Result<Reply> {
        self.check_caller(&ctx)?;
        if value == 0 {
            return Err(refuse_err("0 is not a proposal"));
        }
        let mut g = self.inner.lock().expect("recorder lock");
        if !g.registers.contains_key(&slot) && g.registers.len() >= MAX_SLOTS {
            return Err(refuse_no("too many slots"));
        }
        // The register is the verified one: it answers what the paper's specification
        // answers. This is the plain Rust around it.
        let (step, first, prior) = g
            .registers
            .entry(slot)
            .or_insert_with(Isr::new)
            .record_now(step, value);
        Ok(Reply { step, first, prior })
    }

    async fn learn(&self, ctx: Context, slot: u64, value: u64) -> Result<()> {
        self.check_caller(&ctx)?;
        let mut g = self.inner.lock().expect("recorder lock");
        match g.learned.get(&slot) {
            Some(&known) if known != value => {
                Err(refuse_err("a different value was decided there"))
            }
            Some(_) => Ok(()),
            None => {
                g.learned.insert(slot, value);
                Ok(())
            }
        }
    }
}
