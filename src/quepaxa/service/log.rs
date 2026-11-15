//! A replicated log from QuePaxa: consensus on slot after slot.

use jetstream::prelude::async_trait;

use super::{Proposer, Recorder, RecorderNode};
use crate::consensus::{Decision, ProposeError, ReplicatedLog};

/// One replica's view of the log: its own recorder (which holds what it has learned),
/// and a proposer to every recorder (itself included).
pub struct QuePaxaLog<R> {
    local: RecorderNode,
    proposer: Proposer<R>,
}

impl<R: Recorder + Send + Sync> QuePaxaLog<R> {
    /// `local` is this replica's own recorder; `proposer` reaches all of them, `local`
    /// among them.
    pub fn new(local: RecorderNode, proposer: Proposer<R>) -> Self {
        QuePaxaLog { local, proposer }
    }
}

#[async_trait]
impl<R: Recorder + Send + Sync> ReplicatedLog for QuePaxaLog<R> {
    async fn propose(&self, value: u64) -> Result<Decision, ProposeError> {
        // The first slot this replica does not know is decided. Another proposer may
        // have taken it without this replica hearing, in which case running consensus
        // there finds that out: the recorders are past it and say what was decided.
        let mut slot = self.local.committed();
        loop {
            if let Some(known) = self.local.decided(slot) {
                if known == value {
                    return Ok(Decision { slot, value });
                }
                slot += 1;
                continue;
            }
            let decided = self.proposer.propose(slot, value).await?;
            // Tell everyone, and make sure this replica knows even if telling itself
            // over the wire failed.
            self.proposer.announce(slot, decided).await;
            if !self.local.learn_local(slot, decided) {
                return Err(ProposeError::Unavailable(format!(
                    "slot {slot} was already decided differently here: a safety violation"
                )));
            }
            if decided == value {
                return Ok(Decision { slot, value });
            }
            slot += 1;
        }
    }

    async fn decided(&self, slot: u64) -> Option<u64> {
        self.local.decided(slot)
    }

    async fn committed(&self) -> u64 {
        self.local.committed()
    }
}
