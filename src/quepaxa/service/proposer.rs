//! **The proposer** (the paper's Algorithm 4), for one slot.
//!
//! A proposer drives the recorders through steps `s = 4, 5, 6, ...`, four to a round:
//!
//! ```text
//! phase 0 (s mod 4 = 0)  propose: send a random-priority copy of my proposal to each
//!                        recorder; a recorder answers with the FIRST value it saw this
//!                        step. If every first value is the leader's, decide it.
//!                        Otherwise my proposal becomes the best first value.
//! phase 1                spread it: record my proposal; nothing to decide.
//! phase 2                gather: each recorder answers with the best proposal recorded
//!                        in phase 1. If mine is the best of them, decide it.
//! phase 3                my proposal becomes the best phase-2 aggregate, for next round.
//! ```
//!
//! and, whenever a recorder answers from a later step, jump to that step and adopt the
//! first value it recorded there ("catch up").
//!
//! [`absorb`] is that logic, a pure function of the proposer's state and the replies
//! from a quorum, so it can be tested line by line against the paper. [`Proposer`] is the
//! I/O around it. **Neither is verified**: that this provides the broadcast the abstract
//! algorithm assumes is the paper's Appendix B argument, and is not proved here.

use std::collections::HashMap;
use std::sync::Mutex;
use std::time::Duration;

use jetstream::prelude::futures::stream::{FuturesUnordered, StreamExt};
use jetstream::prelude::*;
use rand::RngExt as _;
use rand::SeedableRng as _;

use super::{Recorder, Reply};
use crate::consensus::ProposeError;
use crate::quepaxa::proposal::{LEADER, Proposal, pack, unpack};

/// How many times in a row a call to one recorder may fail before it is taken to be down.
const ATTEMPTS: u32 = 30;

/// Make `call` until it succeeds, backing off a little between failures, and give up
/// after [`ATTEMPTS`] in a row: the recorder is taken to be down.
async fn with_retries<T, F>(mut call: impl FnMut() -> F) -> Option<T>
where
    F: std::future::Future<Output = Result<T>>,
{
    for attempt in 0..ATTEMPTS {
        if let Ok(value) = call().await {
            return Some(value);
        }
        if attempt + 1 < ATTEMPTS {
            tokio::time::sleep(Duration::from_millis(u64::from(attempt.min(10)))).await;
        }
    }
    None
}

/// How a proposer behaves.
#[derive(Debug, Clone, Copy)]
pub struct Config {
    /// This proposer's index. Breaks a tie in priority, so it must differ between
    /// proposers.
    pub index: u32,
    /// Whether this proposer is the slot's designated leader: in the first round its
    /// proposals carry the highest priority, so if a quorum sees them first it can
    /// decide in one round trip.
    pub leader: bool,
    /// How long to wait before starting. **Hedging**: the leader waits nothing, and
    /// later proposers wait longer, so under normal conditions only the first acts.
    pub hedge: Duration,
    /// Seeds the priorities. `None` is entropy; a test passes a seed.
    pub seed: Option<u64>,
}

/// What a proposer holds between replies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct State {
    /// The current step, `4 * round + phase`, starting at 4 (round 1, phase 0).
    pub step: u64,
    /// The proposal this proposer is carrying: a packed `(priority, proposer, value)`.
    pub proposal: u128,
    /// This proposer's index.
    pub index: u32,
    /// Whether it is the designated leader.
    pub leader: bool,
}

impl State {
    /// A proposer about to start, proposing `value`.
    pub fn start(index: u32, leader: bool, value: u64) -> State {
        State {
            step: 4,
            // The template carries the leader's priority; a non-leader replaces it at
            // phase 0 of its first round.
            proposal: pack(Proposal {
                priority: LEADER,
                proposer: index,
                value,
            }),
            index,
            leader,
        }
    }
}

/// What a quorum's replies do to a proposer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// Consensus: this value is decided.
    Decided(u64),
    /// Go round again, at the state's new step.
    Continue,
}

/// The packed proposal to send to each of `recorders` at the current step.
///
/// At phase 0, each recorder gets its own random priority, except the designated
/// leader's first round, which keeps the highest. At every other phase every recorder
/// is sent the proposal as it is.
pub fn outgoing(state: &State, recorders: usize, rng: &mut impl rand::Rng) -> Vec<u128> {
    (0..recorders)
        .map(|_| {
            if state.step % 4 == 0 && (state.step > 4 || !state.leader) {
                let mut p = unpack(state.proposal);
                p.priority = rng.random_range(1..LEADER);
                pack(p)
            } else {
                state.proposal
            }
        })
        .collect()
}

/// Take the replies of a quorum (never empty), and decide, advance or catch up.
pub fn absorb(state: &mut State, replies: &[Reply]) -> Outcome {
    assert!(!replies.is_empty(), "a quorum is not empty");
    let s = state.step;
    if replies.iter().all(|r| r.step == s) {
        match s % 4 {
            0 => {
                // The fast path: every recorder's first value is the designated
                // leader's, so a quorum already holds it.
                if replies.iter().all(|r| unpack(r.first).priority == LEADER) {
                    return Outcome::Decided(unpack(replies[0].first).value);
                }
                state.proposal = replies.iter().map(|r| r.first).max().expect("non-empty");
            }
            1 => {}
            2 => {
                let best = replies.iter().map(|r| r.prior).max().expect("non-empty");
                if state.proposal == best {
                    return Outcome::Decided(unpack(state.proposal).value);
                }
            }
            _ => {
                state.proposal = replies.iter().map(|r| r.prior).max().expect("non-empty");
            }
        }
        state.step += 1;
    } else {
        // Some recorder is ahead. Jump to the furthest step heard of and carry the
        // first value that recorder recorded there.
        let ahead = replies.iter().max_by_key(|r| r.step).expect("non-empty");
        debug_assert!(ahead.step > s);
        state.step = ahead.step;
        state.proposal = ahead.first;
    }
    Outcome::Continue
}

/// A proposer for single slots, talking to a set of recorders.
///
/// `R` is any [`Recorder`]: a network channel, or a recorder in the same process.
pub struct Proposer<R> {
    config: Config,
    recorders: Vec<R>,
    rng: Mutex<rand::rngs::StdRng>,
    /// Held for the whole of a `propose`: this proposer runs one slot at a time.
    running: tokio::sync::Mutex<()>,
    /// The value this proposer first proposed at each slot it has run.
    attempted: Mutex<HashMap<u64, u64>>,
}

impl<R: Recorder + Send + Sync> Proposer<R> {
    /// A proposer over `recorders`, a majority of which must answer.
    pub fn new(config: Config, recorders: Vec<R>) -> Self {
        let rng = match config.seed {
            Some(seed) => rand::rngs::StdRng::seed_from_u64(seed),
            None => rand::make_rng(),
        };
        Proposer {
            config,
            recorders,
            rng: Mutex::new(rng),
            running: tokio::sync::Mutex::new(()),
            attempted: Mutex::new(HashMap::new()),
        }
    }

    fn quorum(&self) -> usize {
        self.recorders.len() / 2 + 1
    }

    /// Run consensus on `slot`, proposing `value`, and return what is decided there. It
    /// is `value` unless another proposer's got there first.
    ///
    /// **A proposer proposes one value per slot.** The protocol's argument has one
    /// proposal per proposer per round, and the designated leader's proposals all carry
    /// the same priority, so a proposer that put two different values into one slot (a
    /// retry of a different value after a failed attempt, or two calls at once) would be
    /// two proposers with one id. This enforces it: calls run one at a time, and once a
    /// value has been tried at a slot, later calls for that slot carry *that* value and
    /// return what is decided, so a caller whose value lost must move to another slot.
    ///
    /// Waits for a quorum at each step and never times out. A recorder that is down
    /// fails or never answers and is not waited for; if so many fail that no quorum
    /// can answer, this gives up with [`ProposeError::Unavailable`].
    pub async fn propose(&self, slot: u64, value: u64) -> std::result::Result<u64, ProposeError> {
        let _one_at_a_time = self.running.lock().await;
        let value = *self
            .attempted
            .lock()
            .expect("attempted")
            .entry(slot)
            .or_insert(value);
        if !self.config.hedge.is_zero() {
            tokio::time::sleep(self.config.hedge).await;
        }
        let mut state = State::start(self.config.index, self.config.leader, value);
        loop {
            let sent = {
                let mut rng = self.rng.lock().expect("proposer rng");
                outgoing(&state, self.recorders.len(), &mut *rng)
            };
            let replies = self.quorum_of_replies(slot, state.step, sent).await?;
            if let Outcome::Decided(v) = absorb(&mut state, &replies) {
                return Ok(v);
            }
        }
    }

    /// Tell every recorder `value` was decided at `slot`, and return once a majority has
    /// acknowledged (or no majority can). Best effort: a recorder that is down is not
    /// waited for, and one that was not reached finds out by running consensus on the
    /// slot itself, which says what was decided.
    pub async fn announce(&self, slot: u64, value: u64) {
        let quorum = self.quorum();
        let mut calls: FuturesUnordered<_> = self
            .recorders
            .iter()
            .map(|r| with_retries(move || r.learn(Context::default(), slot, value)))
            .collect();
        let mut acknowledged = 0;
        while let Some(answer) = calls.next().await {
            if answer.is_some() {
                acknowledged += 1;
                if acknowledged >= quorum {
                    return;
                }
            }
        }
    }

    /// Send each recorder its own copy and wait for the first quorum of answers.
    async fn quorum_of_replies(
        &self,
        slot: u64,
        step: u64,
        sent: Vec<u128>,
    ) -> std::result::Result<Vec<Reply>, ProposeError> {
        let n = self.recorders.len();
        let quorum = self.quorum();
        // Each call is retried until it answers or has failed `ATTEMPTS` times in a
        // row, because the protocol assumes a message between correct nodes is
        // eventually delivered, and a failed call (a dropped connection) is not that
        // message arriving. `record` is idempotent, so a retry of a call that did get
        // through changes nothing.
        let mut calls: FuturesUnordered<_> = self
            .recorders
            .iter()
            .zip(sent)
            .map(|(r, value)| with_retries(move || r.record(Context::default(), slot, step, value)))
            .collect();
        let mut replies = Vec::with_capacity(quorum);
        let mut down = 0;
        while let Some(answer) = calls.next().await {
            match answer {
                Some(reply) => {
                    replies.push(reply);
                    if replies.len() >= quorum {
                        return Ok(replies);
                    }
                }
                None => {
                    down += 1;
                    if n - down < quorum {
                        return Err(ProposeError::Unavailable(format!(
                            "{down} of {n} recorders are down, so no quorum can answer"
                        )));
                    }
                }
            }
        }
        Err(ProposeError::Unavailable("no quorum answered".into()))
    }
}
