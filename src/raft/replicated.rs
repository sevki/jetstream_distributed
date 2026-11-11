//! **Raft as a [`ReplicatedLog`]**: the driver that the rest of this module leaves to its
//! caller, and the interface every consensus protocol in this crate shares.
//!
//! [`Peer`] is one server's state and the decisions it makes. Everything that *moves*
//! (asking for votes, sending an entry, backing off when a follower refuses, telling
//! followers what is committed) was deliberately the caller's, and the tests drive it by
//! hand. [`RaftLog`] is that caller, written once: it holds a `Peer` and a handle to each
//! other server, and turns `propose` into "append at the leader, replicate until a
//! majority holds it, return the slot once it is committed".
//!
//! # What it is, and is not
//!
//! * **Plain Rust over the verified pieces.** Every decision (a vote, a term, an
//!   acknowledgement, the commit point) is `Peer`'s, which calls the verified step
//!   functions. What is added is the order they are called in, and none of that is
//!   proved. The tests are `tests/consensus_contract.rs`, the same ones QuePaxa runs.
//! * **Timeouts are here, and QuePaxa has none.** A call to a server that does not answer
//!   is given up on after [`RaftLog::with_rpc_timeout`], and the follower is tried again
//!   next round. That is the timing Raft's liveness rests on; nothing about it is proved.
//! * **No election timer.** Raft elects a leader when a follower's election timeout
//!   fires. [`RaftLog::elect`] is what a timeout would call, and nothing calls it on its
//!   own: a cluster has a leader because someone elected one.
//! * **Only the leader proposes.** `propose` on a server that does not lead returns
//!   [`ProposeError::NotPlaced`], and a caller tries another. This is Raft's own shape
//!   and the contract allows it.
//! * **Entries are replicated one at a time**, as [`Consensus::append_entries`] defines
//!   it, with the leader backing off one entry on each refusal. Slow, and exactly the
//!   protocol's.
//! * **Crash-stop.** A [`Peer`] recovers its term and vote from its [`Durable`](super::service::Durable)
//!   store; a log store that loses entries is outside the model.

use std::collections::HashMap;
use std::sync::Mutex;
use std::time::Duration;

use jetstream::prelude::futures::future::join_all;
use jetstream::prelude::*;

use super::service::{Appended, Consensus, LogEntry, Peer};
use crate::consensus::{Decision, ProposeError, ReplicatedLog};
use crate::id::Id;

/// How many rounds of replication a `propose` makes before it gives up on a majority.
const ROUNDS: usize = 64;

/// One Raft server, with the means to reach every other.
pub struct RaftLog<C> {
    peer: Peer,
    /// The other servers, as the wire protocol's trait: a network channel, or a
    /// [`Peer`] in the same process.
    others: Vec<(Id, C)>,
    /// How long a call to another server may take before it is given up on.
    rpc_timeout: Duration,
    /// One replication at a time. Appending entries is concurrent; sending them is not.
    replicating: tokio::sync::Mutex<()>,
    /// For each follower, the length of its log the leader last believed (`nextIndex`).
    next: Mutex<HashMap<Id, u64>>,
}

impl<C: Consensus + Send + Sync> RaftLog<C> {
    /// `peer` is this server; `others` reaches every other server.
    pub fn new(peer: Peer, others: Vec<(Id, C)>) -> Self {
        RaftLog {
            peer,
            others,
            rpc_timeout: Duration::from_millis(100),
            replicating: tokio::sync::Mutex::new(()),
            next: Mutex::new(HashMap::new()),
        }
    }

    /// How long a call to another server may take before it counts as unreachable.
    pub fn with_rpc_timeout(mut self, timeout: Duration) -> Self {
        self.rpc_timeout = timeout;
        self
    }

    /// This server's state, for a caller that wants to read it.
    pub fn peer(&self) -> &Peer {
        &self.peer
    }

    /// Whether this server believes it leads. A belief: see [`super::service::Standing`].
    pub fn leads(&self) -> bool {
        self.peer.standing_now().leading
    }

    /// **Stand for election**, ask every other server for its vote, and say whether this
    /// one now leads. What an election timeout would do; nothing here calls it.
    pub async fn elect(&self) -> Result<bool> {
        let term = self.peer.stand_for_election()?;
        let (last_term, len) = self.peer.summary()?;
        let ballots = join_all(self.others.iter().map(|(id, server)| async move {
            let ask = server.request_vote(Context::default(), term, last_term, len);
            (*id, tokio::time::timeout(self.rpc_timeout, ask).await)
        }))
        .await;
        for (id, ballot) in ballots {
            // A server that did not answer has not voted. The ones that did, have.
            if let Ok(Ok(ballot)) = ballot {
                self.peer.count_ballot(id, term, ballot)?;
            }
        }
        Ok(self.leads())
    }

    /// Bring every reachable follower up to this leader's log, and tell them what is
    /// committed. Stops early if a reply shows this server is no longer the leader.
    async fn replicate(&self) -> std::result::Result<(), ProposeError> {
        let _one = self.replicating.lock().await;
        let standing = self.peer.standing_now();
        if !standing.leading {
            return Err(ProposeError::NotPlaced("not the leader".into()));
        }
        let term = standing.term;
        let results = join_all(
            self.others
                .iter()
                .map(|(id, server)| self.catch_up(*id, server, term)),
        )
        .await;
        for result in results {
            result?;
        }
        // Tell the followers what is now committed, so they apply it.
        let beats = join_all(self.others.iter().map(|(_, server)| {
            tokio::time::timeout(
                self.rpc_timeout,
                server.heartbeat(Context::default(), term, self.peer.commit()),
            )
        }))
        .await;
        for beat in beats {
            if let Ok(Ok(standing)) = beat {
                self.peer.observe_standing(standing).map_err(down)?;
            }
        }
        Ok(())
    }

    /// Send one follower the entries it lacks, backing off when it refuses.
    async fn catch_up(
        &self,
        id: Id,
        server: &C,
        term: u64,
    ) -> std::result::Result<(), ProposeError> {
        let mut prefix = {
            let len = self.len()?;
            *self
                .next
                .lock()
                .expect("next")
                .get(&id)
                .unwrap_or(&len.saturating_sub(1))
        };
        loop {
            let len = self.len()?;
            if prefix >= len {
                break;
            }
            let entry = self.entry(prefix)?;
            let prev_term = if prefix == 0 {
                0
            } else {
                self.entry(prefix - 1)?.term
            };
            let call = server.append_entries(
                Context::default(),
                term,
                prefix,
                prev_term,
                entry,
                self.peer.commit(),
            );
            let Ok(Ok(reply)) = tokio::time::timeout(self.rpc_timeout, call).await else {
                // Unreachable for now. It is brought up to date on a later round.
                break;
            };
            match reply {
                Appended::Accepted(ack) => {
                    self.peer.observe_appended(id, reply).map_err(down)?;
                    prefix = ack.len;
                }
                Appended::Rejected(_) => {
                    self.peer.observe_appended(id, reply).map_err(down)?;
                    if !self.leads() {
                        return Err(ProposeError::NotPlaced("deposed".into()));
                    }
                    // The consistency check failed: back off one entry and retry.
                    if prefix == 0 {
                        break;
                    }
                    prefix -= 1;
                }
            }
        }
        self.next.lock().expect("next").insert(id, prefix);
        Ok(())
    }

    fn len(&self) -> std::result::Result<u64, ProposeError> {
        self.peer
            .log_store()
            .len()
            .map_err(|e| ProposeError::Unavailable(format!("log: {e}")))
    }

    fn entry(&self, index: u64) -> std::result::Result<LogEntry, ProposeError> {
        self.peer
            .log_store()
            .entry_at(index)
            .map_err(|e| ProposeError::Unavailable(format!("log: {e}")))?
            .ok_or_else(|| ProposeError::Unavailable(format!("no entry at {index}")))
    }
}

fn down(e: Error) -> ProposeError {
    ProposeError::Unavailable(e.to_string())
}

#[async_trait]
impl<C: Consensus + Send + Sync> ReplicatedLog for RaftLog<C> {
    async fn propose(&self, value: u64) -> std::result::Result<Decision, ProposeError> {
        if !self.leads() {
            return Err(ProposeError::NotPlaced("not the leader".into()));
        }
        let slot = match self.peer.append_command(value) {
            Ok(index) => index,
            Err(e) if e.code() == Some("NO") => {
                return Err(ProposeError::NotPlaced("not the leader".into()));
            }
            Err(e) => return Err(down(e)),
        };
        for _ in 0..ROUNDS {
            self.replicate().await?;
            if self.peer.commit() > slot {
                // Committed. If a new leader overwrote the slot first, it is not ours.
                return if self.entry(slot)?.value == value {
                    Ok(Decision { slot, value })
                } else {
                    Err(ProposeError::Unavailable("the slot was overwritten".into()))
                };
            }
            if !self.leads() {
                return Err(ProposeError::Unavailable(
                    "deposed before the entry committed".into(),
                ));
            }
            tokio::task::yield_now().await;
        }
        Err(ProposeError::Unavailable(
            "no majority acknowledged the entry".into(),
        ))
    }

    async fn decided(&self, slot: u64) -> Option<u64> {
        if slot >= self.peer.commit() {
            return None;
        }
        self.peer
            .log_store()
            .entry_at(slot)
            .ok()
            .flatten()
            .map(|e| e.value)
    }

    async fn committed(&self) -> u64 {
        self.peer.commit()
    }
}
