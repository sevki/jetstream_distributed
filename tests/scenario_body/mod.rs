//! Randomised ownership scenarios over a simulated network.
//!
//! `src/proofs` establishes that the *model* is safe: no reachable state of
//! the state machine has two owners, a burned epoch fences the outgoing one,
//! and a stale token confers nothing. That is a claim about a transition
//! relation. It says nothing about whether an implementation follows it, and
//! `README.md` has always listed the gap as future work.
//!
//! This closes part of that gap by simulation rather than by proof. It runs an
//! *executable* ownership protocol — a coordinator holding the registry, nodes
//! acquiring and writing over real sockets — on turmoil's deterministic
//! network, and checks the model's own theorems as runtime oracles while the
//! network partitions, delays and reorders underneath it.
//!
//! **What this is evidence of.** A divergence here is one of two things: an
//! implementation that does not follow the protocol, or a protocol whose proof
//! rests on something the network does not give you. Both are findings. What it
//! is *not* is a check on the proofs — those are static, and a simulation
//! cannot contradict them.
//!
//! **Where the executable code lives, and why.** Entirely in `tests/`. `src/`
//! is specification and proof plus the one verified `FenceGuard`, and CI greps
//! it for `verifier::external`; unverified protocol code there would need that
//! attribute and would fail the build by design. The one piece of `src/` this
//! does use is `FenceGuard`, because it is the node-local check a real node
//! performs, and exercising it against an authoritative fence is precisely the
//! asymmetry `src/exec.rs` documents.
//!
//! Everything here is deterministic: turmoil's network is seeded, its clock is
//! simulated, and nothing reads a wall clock or an RNG. A failing seed
//! reproduces exactly.

// Mounted by more than one target, and each uses a different part: only the
// seed walk builds scenarios from seeds, only the named stories call the
// protocol pieces directly. Warning about the unused half in each is noise
// about a shared module doing its job.
#![allow(dead_code)]

use std::{
    collections::{HashMap, VecDeque},
    io,
    net::{IpAddr, Ipv4Addr},
    sync::{Arc, Mutex},
    time::Duration,
};

use distributed_ownership::exec::FenceGuard;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use turmoil::{
    net::{TcpListener, TcpStream},
    Builder,
};

/// The one actor every scenario contends over.
///
/// One is enough: exclusivity is a per-actor property, and the model's
/// `theorem_actor_domain_constant` says actors never interact. A second actor
/// would double the runtime and test the same thing twice.
const ACTOR: u64 = 7;

/// How many nodes contend.
///
/// Three, so that a handover has somewhere to go that is not the node being
/// revoked, and so a partition can isolate one while two remain reachable.
const NODES: u64 = 3;

const PORT: u16 = 9_440;

/// The epoch the registry starts at.
///
/// Named rather than written twice, because the oracles need it: a
/// monotonicity check that starts from "whatever the first event said" cannot
/// see a first event that is already wrong.
pub const INITIAL_EPOCH: u64 = 41;

/// The node the actor is offered to before anyone has taken it.
///
/// Named for the same reason as the epoch: an oracle that checks who may
/// acquire needs somewhere to start, and taking that from the first event in
/// the log it is auditing would make the first acquire unconditionally valid.
pub const INITIAL_OWNER: u64 = 0;

/// How long the driver waits after queueing an action.
///
/// Comfortably more than a round trip, so that consecutive actions read as
/// consecutive steps rather than as a pile-up. It is simulated time.
const SETTLE: Duration = Duration::from_millis(75);

fn node_host(n: u64) -> String {
    format!("node-{n}")
}

// ---------------------------------------------------------------------------
// The audit log: what the coordinator did, in order
// ---------------------------------------------------------------------------

/// One thing the coordinator accepted or refused.
///
/// The oracles are predicates over a `Vec<Event>`, which is deliberate: the
/// proofs are predicates over `Seq<System>`, and keeping the same shape means a
/// runtime check can be read against the theorem it comes from. The coordinator
/// is the only writer, because it is the only place that knows the
/// authoritative state — which is the same reason the model puts `actors` in
/// one map and assumes it is updated atomically.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// A node took ownership at this epoch.
    Acquired { node: u64, epoch: u64 },
    /// A write was accepted: at this instant the registry said
    /// `Owned(node, epoch)`.
    Wrote { node: u64, epoch: u64, seq: u64 },
    /// A write was refused because the registry said otherwise. The stale
    /// owner's request arriving after a takeover lands here.
    Fenced { node: u64, epoch: u64 },
    /// The coordinator burned an epoch, with or without the owner's agreement.
    EpochBurned { from_epoch: u64, to_epoch: u64, next: u64, forced: bool },
    /// A revoked owner acknowledged.
    Released { node: u64, new_epoch: u64 },
}

/// The registry, plus the log of what it did.
///
/// `state` is the executable counterpart of the model's
/// `actors: Map<ActorId, OwnershipState>`, narrowed to one actor and to `u64`.
pub struct Coord {
    state: Owned,
    log: Vec<Event>,
    /// Writes accepted so far, used to give each one a sequence number.
    writes: u64,
    /// When false the coordinator skips its fence check. Used only by the
    /// self-test that proves these oracles can fail — see
    /// [`run_scenario_unfenced`].
    fencing: bool,
    /// Delay the next reply past the caller's deadline, once.
    ///
    /// The network can delay a *request*; only the coordinator can accept one
    /// and then answer too late. The two are different failures and the second
    /// is the one a node's doc comment claims not to over-read: a timeout says
    /// no answer arrived, never that the write was not applied.
    slow_next_reply: bool,
}

/// The actor's ownership state. The three-case enum of `model::OwnershipState`,
/// with the epochs as `u64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Owned {
    Unowned { epoch: u64, intended: u64 },
    Transferring { from: u64, to: u64, old_epoch: u64, new_epoch: u64 },
    Owned { owner: u64, epoch: u64 },
}

impl Owned {
    fn epoch(&self) -> u64 {
        match *self {
            Owned::Unowned { epoch, .. } => epoch,
            Owned::Transferring { new_epoch, .. } => new_epoch,
            Owned::Owned { epoch, .. } => epoch,
        }
    }
}

impl Coord {
    pub fn new(fencing: bool) -> Self {
        Coord {
            // The same start state the scenarios in `src/proofs` use: offered
            // to node 0 at the initial epoch, held by nobody.
            state: Owned::Unowned { epoch: INITIAL_EPOCH, intended: INITIAL_OWNER },
            log: Vec::new(),
            writes: 0,
            fencing,
            slow_next_reply: false,
        }
    }

    /// Make the next reply arrive after the caller has given up on it.
    fn arm_slow_reply(&mut self) {
        self.slow_next_reply = true;
    }

    /// Consume that arming, if it is set.
    fn take_slow_reply(&mut self) -> bool {
        core::mem::take(&mut self.slow_next_reply)
    }

    /// Handle one request line, returning the reply line.
    ///
    /// Every branch is one of the model's transitions, and the comments name
    /// which. Keeping them in step is the whole point: a transition the
    /// implementation has that the model does not is exactly the kind of thing
    /// this suite exists to find.
    pub fn handle(&mut self, line: &str) -> String {
        let mut parts = line.split_whitespace();
        let verb = parts.next().unwrap_or("");
        let args: Vec<u64> = parts.filter_map(|p| p.parse().ok()).collect();

        match (verb, args.as_slice()) {
            // What does this node currently have on offer? A node with no
            // grant has nothing to acquire with.
            ("POLL", [node]) => match self.state {
                Owned::Unowned { epoch, intended } if intended == *node => {
                    format!("GRANT {epoch}")
                }
                Owned::Transferring { from, new_epoch, .. } if from == *node => {
                    // `tr_handle_revoke`: the outgoing owner is told to stop.
                    format!("REVOKE {new_epoch}")
                }
                _ => "NONE".to_string(),
            },

            // `tr_acquire`. Only from `Unowned`, only by the intended owner,
            // only at exactly that epoch.
            ("ACQUIRE", [node, epoch]) => match self.state {
                Owned::Unowned { epoch: e, intended } if intended == *node && e == *epoch => {
                    self.state = Owned::Owned { owner: *node, epoch: e };
                    self.log.push(Event::Acquired { node: *node, epoch: e });
                    "OK".to_string()
                }
                _ => "NO".to_string(),
            },

            // The fence, at the point where the effect lands. This is
            // `can_mutate(sys, actor, node, epoch)` made executable, and it is
            // the check `src/exec.rs` says a node cannot perform for itself.
            ("WRITE", [node, epoch]) => {
                let permitted = matches!(
                    self.state,
                    Owned::Owned { owner, epoch: e } if owner == *node && e == *epoch
                );
                if permitted || !self.fencing {
                    self.writes += 1;
                    let seq = self.writes;
                    self.log.push(Event::Wrote { node: *node, epoch: *epoch, seq });
                    format!("OK {seq}")
                } else {
                    self.log.push(Event::Fenced { node: *node, epoch: *epoch });
                    "FENCED".to_string()
                }
            }

            // `tr_begin_transfer`: the owner agrees to hand over. The epoch is
            // burned immediately, which fences the outgoing owner from here on.
            //
            // The request names its own sender, and the registry checks it, so
            // that only the owner can agree on the owner's behalf. The model
            // additionally requires `pre.live.contains(from)` — "agrees to hand
            // over" is an action *by* `from` — and the simulation's counterpart
            // of that guard is that the request has to arrive: an isolated
            // owner's `BEGIN` is swallowed by the partition and the transfer
            // never starts. That only works because the request originates at
            // the owner's host; issued from anywhere else it would let a node
            // nobody can reach volunteer, which is exactly the hole the
            // liveness guard on `tr_begin_transfer` was added to close.
            //
            // `*to < NODES` is `pre.nodes.contains(to)`. The driver happens to
            // take its successor modulo `NODES`, so nothing in this suite sends
            // an unknown one — which is exactly why the check belongs here
            // rather than there. A precondition enforced by the caller is a
            // precondition the registry does not have.
            ("BEGIN", [from, to]) if *to >= NODES => {
                let _ = from;
                "NO".to_string()
            }
            ("BEGIN", [from, to]) => match self.state {
                Owned::Owned { owner, epoch } if owner == *from && owner != *to => {
                    self.state = Owned::Transferring {
                        from: owner,
                        to: *to,
                        // (`owner == *from` here, checked by the guard above.)
                        old_epoch: epoch,
                        new_epoch: epoch + 1,
                    };
                    self.log.push(Event::EpochBurned {
                        from_epoch: epoch,
                        to_epoch: epoch + 1,
                        next: *to,
                        forced: false,
                    });
                    "OK".to_string()
                }
                _ => "NO".to_string(),
            },

            // `tr_handle_revoke` then `tr_complete_release`, folded: the
            // outgoing owner acknowledges and the actor becomes `Unowned` at
            // the new epoch. Folding them is a simplification of the model,
            // and it is the one place this implementation is deliberately
            // coarser than what was proved — noted in README.
            // The epoch is part of the acknowledgement, not inferred from
            // where the registry happens to be. `tr_complete_release` requires
            // `Message::Released { from, new_epoch }` to name the transfer's
            // *current* `new_epoch`, and without carrying it a release from an
            // earlier handover — delayed on the wire, or replayed — would
            // complete a later one by the same node. The line protocol is where
            // that has to be checked, because by the time the handler sees it
            // the only thing distinguishing the two is the epoch.
            ("RELEASE", [node, epoch]) => match self.state {
                Owned::Transferring { from, to, new_epoch, .. }
                    if from == *node && new_epoch == *epoch =>
                {
                    self.state = Owned::Unowned { epoch: new_epoch, intended: to };
                    self.log.push(Event::Released { node: *node, new_epoch });
                    "OK".to_string()
                }
                _ => "NO".to_string(),
            },

            // The coordinator forcing progress on its own. Which transition
            // that is depends on the state, and the three are not
            // interchangeable — in particular the model gives the coordinator
            // *no* way to redirect an interrupted transfer to a node of its
            // choosing, and an implementation that offered one would be
            // exercising histories the proofs say nothing about.
            ("FORCE", [next]) if *next >= NODES => "NO".to_string(),
            ("FORCE", [next]) => match self.state {
                // `tr_revoke_owner`: burn the epoch without the owner's
                // cooperation and offer the actor to `next`. Fires against a
                // healthy owner on purpose — unreliable failure detection is
                // modelled, not assumed away.
                Owned::Owned { epoch, .. } => {
                    self.state = Owned::Unowned { epoch: epoch + 1, intended: *next };
                    self.log.push(Event::EpochBurned {
                        from_epoch: epoch,
                        to_epoch: epoch + 1,
                        next: *next,
                        forced: true,
                    });
                    "OK".to_string()
                }
                // `tr_reassign_unowned`: the intended owner never picked the
                // actor up. Burn and offer it to somebody else.
                Owned::Unowned { epoch, .. } => {
                    self.state = Owned::Unowned { epoch: epoch + 1, intended: *next };
                    self.log.push(Event::EpochBurned {
                        from_epoch: epoch,
                        to_epoch: epoch + 1,
                        next: *next,
                        forced: true,
                    });
                    "OK".to_string()
                }
                // `tr_abort_transfer`: a transfer was interrupted. Burn
                // *another* epoch, so a `Grant` for `new_epoch` still in flight
                // is stale on arrival, and offer the actor back to the node it
                // was being taken from.
                //
                // `next` is deliberately ignored here. `tr_revoke_owner` only
                // matches `Owned`, and the model's one recovery from
                // `Transferring` returns the actor to `from` — so a coordinator
                // that sent it anywhere else would be taking a step outside the
                // transition relation, and every oracle it then satisfied would
                // be evidence about nothing.
                Owned::Transferring { from, new_epoch, .. } => {
                    self.state = Owned::Unowned { epoch: new_epoch + 1, intended: from };
                    self.log.push(Event::EpochBurned {
                        from_epoch: new_epoch,
                        to_epoch: new_epoch + 1,
                        next: from,
                        forced: true,
                    });
                    "OK".to_string()
                }
            },

            _ => "ERR".to_string(),
        }
    }
}

// ---------------------------------------------------------------------------
// The node agent
// ---------------------------------------------------------------------------

/// One thing a node can be told to do.
///
/// Each is a round trip to the coordinator, so each is something a partition
/// can swallow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NodeCmd {
    /// Ask for the current offer, and remember it as a `FenceGuard`.
    Poll,
    /// Find out what is on offer, and take it if it is this node's to take.
    Acquire,
    /// Attempt a write using the guard this node holds — stale or not.
    Write,
    /// Acknowledge a revoke this node has seen.
    Release,
    /// Agree to hand the actor to another node. Sent by the node itself,
    /// because in the model agreeing is an action *by* the owner.
    Handover { to: u64 },
}

/// A node's local state: the last generation it observed.
///
/// `FenceGuard` is the verified `u64` check from `src/exec.rs`. It is what the
/// node consults before bothering to send a write, and it is deliberately not
/// authoritative: a partitioned node's guard goes on saying yes long after the
/// system has moved on, which is the asymmetry `src/exec.rs` is at pains to
/// document. The sim exercises both halves — the node asks its guard, the
/// coordinator asks the registry, and the oracles watch what the registry did.
#[derive(Default)]
struct NodeState {
    /// What this node tried to do, counted here rather than at the
    /// coordinator. The coordinator's log cannot distinguish a request that a
    /// partition swallowed from one that was never sent — not seeing a request
    /// is exactly what being cut off from one looks like — so a story that
    /// wants to claim the first has to observe the node.
    attempts: Attempts,
    /// The epoch this node believes is current, if it has ever been offered
    /// one. Survives a "crash", which is what makes a returning owner
    /// dangerous — `tr_recover` says a node comes back still holding what it
    /// had.
    guard: Option<(u64, u64)>,
    /// A revoke this node has been told about and not yet acknowledged.
    pending_revoke: Option<u64>,
}

impl NodeState {
    /// The node-local verdict, through the verified guard.
    fn would_write(&self, node: u64) -> Option<(u64, u64)> {
        let (owner, epoch) = self.guard?;
        let guard = FenceGuard::new(owner, epoch);
        // `accepts` is `may_mutate(self.view(), ..)` — the node's own belief,
        // which is all a node has. Whether it is *right* is the coordinator's
        // business, and the whole point of the exercise.
        if guard.accepts(node, epoch) {
            Some((owner, epoch))
        } else {
            None
        }
    }
}

/// How long a node waits for the coordinator before giving up.
///
/// This was added on a guess that turned out to be wrong, and it is worth
/// recording which part. The guess was that a partition leaves a request
/// hanging, so that without a deadline the first isolation would park a node
/// for the rest of the run. turmoil does not behave that way when the partition
/// is already in place: it knows there is no route and fails the connect at
/// once — `an_isolated_owner_is_met_with_silence_not_refusal` measures exactly
/// that, and it is a place where the simulator is kinder to the sender than a
/// network, which drops the SYN and says nothing.
///
/// What the deadline still covers is the other shape: a partition that arrives
/// after the connection is up, where the reply is dropped and there is nothing
/// to fail. Whether the seed walk ever reaches that shape is not assumed — it
/// is printed, per run, as the node-side totals in `turmoil_scenarios.rs`.
///
/// A real node needs the deadline under both shapes. The clock is simulated, so
/// the wait costs ordering and nothing else.
const RPC_TIMEOUT: Duration = Duration::from_millis(250);

/// What a node put on the wire, and what came back.
///
/// Deliberately not derived from the audit log: everything here is invisible
/// to the coordinator by construction, which is the whole reason it is
/// counted.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Attempts {
    /// Writes this node sent, whatever became of them.
    pub writes_sent: u64,
    /// Writes that spent the whole deadline without an answer — which is what
    /// a partition looks like from inside a node.
    pub writes_timed_out: u64,
    /// Writes that failed some other way: refused, reset, cut off mid-reply.
    ///
    /// Kept apart from the count above rather than lumped in with it, because
    /// the two mean opposite things. A refusal is the network answering; a
    /// deadline is the network saying nothing at all, and only the second is
    /// what a story about silence is entitled to claim. Counting them together
    /// would let "the request was swallowed" be satisfied by a connection that
    /// failed instantly and locally.
    pub writes_failed: u64,
}

/// One request/response round trip. A fresh connection per request, which is
/// slower than a long-lived lane and much easier to reason about: a partition
/// stops the next request rather than half-killing an established one.
///
/// A timeout is reported as an error, which is the honest answer: the node does
/// not know whether the coordinator saw the request. Nothing here retries, and
/// nothing here treats a timeout as a refusal — a node that assumed "no reply"
/// meant "not applied" would be the bug this whole model is about.
async fn rpc(req: String) -> io::Result<String> {
    match tokio::time::timeout(RPC_TIMEOUT, rpc_inner(req)).await {
        Ok(result) => result,
        Err(_) => Err(io::Error::new(io::ErrorKind::TimedOut, "coordinator unreachable")),
    }
}

async fn rpc_inner(req: String) -> io::Result<String> {
    let mut stream = TcpStream::connect(("coord", PORT)).await?;
    stream.write_all(req.as_bytes()).await?;
    stream.write_all(b"\n").await?;
    stream.flush().await?;
    let mut reply = String::new();
    BufReader::new(&mut stream).read_line(&mut reply).await?;
    Ok(reply.trim().to_string())
}

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/// One step a scenario can take.
///
/// Every variant is something a caller, a coordinator or a network can
/// actually do, so any sequence of them is a run the implementation has to
/// survive. They line up with the model's `Step` deliberately: a scenario is
/// an execution of the modelled state machine, run for real.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    /// A node asks what it is currently offered.
    Poll { node: u8 },
    /// A node asks what is on offer and takes it if it is its own.
    Acquire { node: u8 },
    /// A node attempts a fenced write with whatever guard it holds.
    Write { node: u8 },
    /// A revoked node acknowledges.
    Release { node: u8 },
    /// A node agrees to hand the actor over. `tr_begin_transfer`.
    ///
    /// `from` is who sends it, because the model makes agreeing an action by
    /// the owner — and because a request routed around the sender would arrive
    /// even while that sender is partitioned away.
    Handover { from: u8, to: u8 },
    /// The coordinator burns the epoch without asking. `tr_revoke_owner`.
    Force { next: u8 },
    /// Cut a node off — indistinguishable, from outside, from a crash.
    Isolate { node: u8 },
    /// Let it back in. The node returns still holding its old guard, which is
    /// the headline scenario.
    Rejoin { node: u8 },
    /// Hold this node's messages instead of dropping them: the network accepts
    /// them for delivery and delivers nothing.
    ///
    /// Distinct from `Isolate`, and the distinction is the whole reason this
    /// exists. A partition in turmoil is reported to the sender at once, so it
    /// never produces a request that was taken and left unanswered — the shape
    /// a node's deadline is for. A hold does. The model's claim that
    /// arbitrarily delayed requests are safe is about this case, not the other
    /// one.
    Stall { node: u8 },
    /// Deliver everything that was held, all at once.
    Resume { node: u8 },
    /// Let time pass, so in-flight requests land.
    Sleep { millis: u8 },
    /// Make the coordinator answer its next request after the caller's
    /// deadline, having already applied it.
    ///
    /// The one action the generator never produces, because it is not something
    /// a network does: `Stall` delays a request, which turmoil can do, and this
    /// delays a *reply the registry has already acted on*, which needs the
    /// coordinator's cooperation to arrange deterministically. It is here so
    /// that "a timeout is not evidence the write did not happen" is a checked
    /// assertion rather than a sentence in a doc comment.
    SlowReply,
}

impl Action {
    /// One action from two numbers: which one, and its parameter.
    ///
    /// Both generators go through here so that a seed and a byte string
    /// explore the same space. If they diverged, a seed filed by one would not
    /// reproduce under the other.
    ///
    /// The weighting is deliberate. `Write` is commonest because the fence is
    /// what the invariants are about; `Isolate` and `Rejoin` are rarer because
    /// a scenario that spends its length cutting the network tests turmoil
    /// rather than this protocol.
    fn from_pair(choice: u64, param: u64) -> Self {
        let node = (param % NODES) as u8;
        match choice % 14 {
            0..=1 => Action::Poll { node },
            2..=3 => Action::Acquire { node },
            4..=6 => Action::Write { node },
            7 => Action::Release { node },
            8 => {
                // `to` is offset from `from` so the two always differ, which
                // `tr_begin_transfer` requires. With three nodes the offset is
                // 1 or 2 and either lands somewhere else.
                let from = param % NODES;
                let to = (from + 1 + (param / NODES) % (NODES - 1)) % NODES;
                Action::Handover { from: from as u8, to: to as u8 }
            }
            9 => Action::Force { next: node },
            10 => {
                if param % 2 == 0 {
                    Action::Isolate { node }
                } else {
                    Action::Rejoin { node }
                }
            }
            11 => {
                if param % 2 == 0 {
                    Action::Stall { node }
                } else {
                    Action::Resume { node }
                }
            }
            _ => Action::Sleep { millis: (param % 60) as u8 },
        }
    }
}

#[derive(Debug, Clone)]
pub struct Scenario {
    pub seed: u64,
    pub actions: Vec<Action>,
}

impl Scenario {
    /// Build one from a seed. The same seed yields the same actions *and* the
    /// same network schedule, so a failure reported as a seed is a failure
    /// anyone can re-run.
    pub fn from_seed(seed: u64) -> Self {
        let mut rng = Lcg::new(seed);
        let len = 8 + (rng.next() % 28) as usize;
        let actions = (0..len).map(|_| Action::from_pair(rng.next(), rng.next())).collect();
        Scenario { seed, actions }
    }

    /// Build one from an arbitrary byte string, so the scenarios are fuzzable.
    ///
    /// `from_seed` derives everything from one number, which is what lets a
    /// finding be reported as one — but it also means the only way to explore
    /// is to count upwards, blind to whether the next seed reaches anything the
    /// last did not. Bytes let a coverage-guided fuzzer steer.
    ///
    /// Nothing in this repository calls it yet: it is the entry point a fuzz
    /// target would use, kept here so that the fuzzer and the seed walk would
    /// share one runner and one oracle rather than growing two.
    ///
    /// The first eight bytes are turmoil's network seed. The rest are actions,
    /// two bytes each.
    pub fn from_bytes(data: &[u8]) -> Option<Self> {
        let (head, tail) = data.split_at_checked(8)?;
        let seed = u64::from_le_bytes(head.try_into().ok()?);
        let actions: Vec<Action> = tail
            .chunks_exact(2)
            .take(MAX_ACTIONS)
            .map(|pair| Action::from_pair(pair[0] as u64, pair[1] as u64))
            .collect();
        if actions.is_empty() {
            return None;
        }
        Some(Scenario { seed, actions })
    }
}

/// How long a fuzzed scenario may get. Length alone is never interesting and
/// nothing penalises it, so it is capped.
const MAX_ACTIONS: usize = 64;

/// A tiny deterministic generator, so the scenario shape needs no dependency
/// and no global state. Numerical Recipes' constants.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed.wrapping_mul(6364136223846793005).wrapping_add(1))
    }

    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
}

// ---------------------------------------------------------------------------
// The oracles
// ---------------------------------------------------------------------------

/// Check the model's theorems against what the coordinator actually did.
///
/// Each one names the claim it comes from. A failure here means the
/// implementation and the proof disagree, and the interesting question is
/// always which of them is wrong.
pub fn check_invariants(log: &[Event]) -> Result<(), String> {
    // Claim 1 — exclusive mutable ownership. Two accepted writes at the same
    // epoch must come from the same node. This is the whole point: it is
    // `theorem_exclusive_mutable_ownership` observed rather than proved.
    let mut writer_at: HashMap<u64, u64> = HashMap::new();
    for ev in log {
        if let Event::Wrote { node, epoch, seq } = ev {
            match writer_at.get(epoch) {
                Some(prev) if prev != node => {
                    return Err(format!(
                        "claim 1 (exclusivity): epoch {epoch} accepted writes from \
                         both node {prev} and node {node} (at seq {seq})"
                    ));
                }
                _ => {
                    writer_at.insert(*epoch, *node);
                }
            }
        }
    }

    // Claim 5 — epoch monotonicity. The registry's epoch moves only by a burn,
    // and a burn strictly increases it.
    //
    // Stated as exact accounting rather than as "never goes backwards", which
    // is what it said first and which sees only half of the failure. A
    // monotonic reading catches `Acquired(0, 41), EpochBurned(41, 42),
    // Acquired(0, 41)` — the registry sitting back down below an epoch it
    // burned — but says nothing about `Acquired(0, 41), Acquired(1, 42)`, where
    // it jumps forward with no burn recorded at all. Both are a registry whose
    // epoch moved by something other than a burn, and in the model there is no
    // such step: every transition that changes the epoch burns it.
    //
    // Two kinds of event are deliberately not read as saying where the registry
    // was.
    //
    // `Fenced` names the *request's* epoch. A stale request is by definition
    // one below where the registry has got to, so reading it here would reject
    // precisely the thing being refused.
    //
    // `Wrote` names the registry's epoch only if the fence works, and the fence
    // working is the thing under test — `run_scenario_unfenced` exists to
    // produce logs where it does not. Reading an accepted write as authoritative
    // would let this oracle pre-empt the two that are supposed to catch that,
    // and an oracle that fires first on someone else's failure is worse than
    // one that stays silent: the message would name the wrong claim.
    // Seeded with where the registry actually starts, rather than with the
    // first event that happens to name an epoch. Left as "whatever the first
    // event said", `EpochBurned(42, 43)` followed by `Acquired(0, 43)` is
    // self-consistent and passes — but `Coord::new` starts at 41 and no
    // transition burns from 42, so the corruption is simply invisible before
    // the first event. An oracle that takes its baseline from the thing it is
    // auditing has no baseline.
    let mut epoch = INITIAL_EPOCH;
    for ev in log {
        match ev {
            Event::EpochBurned { from_epoch, to_epoch, .. } => {
                if to_epoch <= from_epoch {
                    return Err(format!(
                        "claim 5 (monotonicity): epoch went {from_epoch} -> {to_epoch}"
                    ));
                }
                if *from_epoch != epoch {
                    return Err(format!(
                        "claim 5 (monotonicity): a burn from epoch {from_epoch} \
                         while the registry was at {epoch} ({ev:?})"
                    ));
                }
                epoch = *to_epoch;
            }
            // Both of these say the registry was `Unowned` or `Owned` at this
            // exact epoch when the event was recorded.
            Event::Acquired { epoch: at, .. } | Event::Released { new_epoch: at, .. } => {
                if *at != epoch {
                    return Err(format!(
                        "claim 5 (monotonicity): the registry was at epoch \
                         {epoch} and is now at {at}, with no burn between \
                         ({ev:?})"
                    ));
                }
            }
            Event::Wrote { .. } | Event::Fenced { .. } => {}
        }
    }

    // P5 / P6 — an epoch determines its owner, and ownership at an epoch is
    // final. Two acquires of the same epoch must name the same node.
    //
    // This is the direct reading of those two theorems, and the version of this
    // function that shipped first did not have it: it read only write epochs,
    // which is a *consequence* of P5/P6 rather than the thing itself. So
    // `Acquired(0, 41), Acquired(1, 41), Wrote(1, 41)` — an epoch changing
    // hands with no burn between, which is exactly what those theorems forbid —
    // passed the entire suite. One writer per epoch satisfied claim 1, no burn
    // satisfied claim 5 and the fencing check, and node 1 really had acquired,
    // so P8 was happy too.
    //
    // The coordinator cannot produce that log, because `ACQUIRE` requires the
    // registry to be `Unowned` at exactly that epoch. But an oracle that is
    // sound only because the thing it audits is correct is not an oracle, so
    // `oracles_reject_an_epoch_that_changes_owner` feeds it in by hand — and
    // that witness is now the only thing keeping this check honest, which is
    // as it should be. A check should be live because something exercises it,
    // not because of where it sits in this function.
    let mut owner_at: HashMap<u64, u64> = HashMap::new();
    for ev in log {
        if let Event::Acquired { node, epoch } = ev {
            match owner_at.get(epoch) {
                Some(prev) if prev != node => {
                    return Err(format!(
                        "P5/P6: epoch {epoch} was acquired by node {prev} and then \
                         by node {node}, with no burn in between — an epoch does \
                         not determine its owner"
                    ));
                }
                _ => {
                    owner_at.insert(*epoch, *node);
                }
            }
        }
    }

    // There is no second half. "Accepted writes never regress to an epoch a
    // later write already used" was one, and it was a misdiagnosis wearing a
    // theorem's name.
    //
    // Every log it rejected is rejected by the fencing oracle below, and the
    // fencing oracle is the one that is *right* about them: the registry's
    // ownership never changed hands at either epoch, so nothing about P5/P6
    // was violated. What happened is that a write below the burned epoch was
    // accepted. The comment here used to say that running it first "keeps it a
    // live check rather than unreachable prose", which is exactly backwards —
    // it was live only because it pre-empted the correct diagnosis, and
    // `oracles_catch_an_unfenced_coordinator` was pinning the wrong claim in
    // place.
    //
    // This is the same mistake as reading `Wrote` into claim 5, two commits
    // apart, and worth leaving written down: an oracle kept alive by its
    // position in the list is not a check, it is a label.

    // P8, at the grant — a node acquires only what it was offered.
    //
    // `tr_acquire` requires two things of the acquiring node: that it is the
    // `intended_owner`, and that a matching `Grant` is in flight. The grant is
    // the capability, so this is the same principle as the write-side check
    // below, one step earlier in the protocol.
    //
    // Until this existed, nothing correlated who acquired with who was offered.
    // `Acquired(0,41), EpochBurned(41→42, next=1), Acquired(2,42), Wrote(2,42)`
    // passed every oracle: one writer per epoch, a well-formed burn from where
    // the registry was, distinct epochs per owner, no write below the burn, and
    // node 2 really had acquired. Deleting the coordinator's `intended == node`
    // guard would have left the whole suite green, which is the plainest
    // possible statement that the suite was not checking it.
    //
    // The intended owner is read off the burns. Every path that leaves the
    // actor `Unowned` records the node it is offered to as that burn's `next`:
    // a forced revoke and a reassignment name their successor, an aborted
    // transfer names the node it came from, and a cooperative handover names
    // its target, which is still the intended owner once the release lands.
    let mut intended = INITIAL_OWNER;
    for ev in log {
        match ev {
            Event::EpochBurned { next, .. } => intended = *next,
            Event::Acquired { node, epoch } if *node != intended => {
                return Err(format!(
                    "P8 (grant): node {node} acquired epoch {epoch}, which was \
                     offered to node {intended}"
                ));
            }
            _ => {}
        }
    }

    // Claims 2 and 3 — stale-owner fencing. Once the registry has burned
    // forward to an epoch, no write below it may ever be accepted again.
    //
    // This is the oracle the headline scenario is about, and the first version
    // of this function did not have it. It had only the write-against-write
    // check above, which sees a stale write only when the *replacement* owner
    // happens to write first: `Acquire(0)@41, Force->42, Write(0)@41` has one
    // writer per epoch, a strictly increasing burn and an acquire behind every
    // write, so every check passed while the exact failure this model exists
    // to rule out went by unremarked. A burn is the event that makes an epoch
    // stale, so a burn is what the high-water mark has to follow.
    let mut burned_to = 0u64;
    for ev in log {
        match ev {
            Event::EpochBurned { to_epoch, .. } => {
                // `max` rather than assignment, so this oracle stands on its
                // own: if burns ever did go backwards, the monotonicity check
                // above is what should say so, not a confused reading here.
                burned_to = burned_to.max(*to_epoch);
            }
            Event::Wrote { node, epoch, seq } if *epoch < burned_to => {
                return Err(format!(
                    "claims 2/3 (fencing): node {node} wrote at epoch {epoch} \
                     (seq {seq}) after the registry had already burned forward \
                     to {burned_to}"
                ));
            }
            _ => {}
        }
    }

    // P8 — no authority without a capability. Every accepted write is backed
    // by an `Acquired` for exactly that (node, epoch), earlier in the log.
    let mut acquired: Vec<(u64, u64)> = Vec::new();
    for ev in log {
        match ev {
            Event::Acquired { node, epoch } => acquired.push((*node, *epoch)),
            Event::Wrote { node, epoch, seq } => {
                if !acquired.contains(&(*node, *epoch)) {
                    return Err(format!(
                        "P8 (token): node {node} wrote at epoch {epoch} (seq {seq}) \
                         without ever having acquired it"
                    ));
                }
            }
            _ => {}
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The runner
// ---------------------------------------------------------------------------

/// Run one scenario with the fence in place, asserting the invariants that
/// must hold whatever the ordering was.
///
/// Returns the number of *accepted* writes, so a caller can tell a scenario
/// that exercised something from one that did not.
pub fn run_scenario(scenario: Scenario) -> turmoil::Result<usize> {
    run_inner(scenario, true)
}

/// The same run, handing back the coordinator's audit log.
///
/// `run_scenario` answers "did anything break?", which is what a blind seed
/// walk wants — it has no idea what its scenario was supposed to do. A named
/// story does know, and checking only that nothing broke would let it pass
/// while doing nothing at all. The invariants are still checked here, so a
/// story gets both: the general claim and its own.
pub fn run_scenario_logged(scenario: Scenario) -> turmoil::Result<Vec<Event>> {
    Ok(run_scenario_probed(scenario)?.0)
}

/// The same run again, handing back what each node *tried* to do alongside
/// what the coordinator accepted.
///
/// The two are different observations and the difference is load-bearing. The
/// audit log is what the registry decided; it is silent about a request that
/// never arrived, and silent in exactly the same way about one that was never
/// sent. A story claiming a partition swallowed something has to look at the
/// node to tell those apart.
pub fn run_scenario_probed(
    scenario: Scenario,
) -> turmoil::Result<(Vec<Event>, Vec<Attempts>)> {
    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = log.clone();
    let attempts = run_with_log(scenario, true, captured)?;
    let out = log.lock().unwrap().clone();
    check_invariants(&out)?;
    Ok((out, attempts))
}

/// The same scenario with the coordinator's fence check disabled.
///
/// This exists to answer the question every oracle has to answer about itself:
/// would it notice? A suite that cannot fail is indistinguishable from one
/// that passes, and since this code cannot be run on the machine that wrote
/// it, a green CI run proving only that the assertions *did not fire* would be
/// very weak evidence. Removing the fence should break claim 1 or P8 — see
/// `oracles_catch_an_unfenced_coordinator`.
pub fn run_scenario_unfenced(scenario: Scenario) -> turmoil::Result<Vec<Event>> {
    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = log.clone();
    let _ = run_with_log(scenario, false, captured)?;
    let out = log.lock().unwrap().clone();
    Ok(out)
}

fn run_inner(scenario: Scenario, fencing: bool) -> turmoil::Result<usize> {
    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = log.clone();
    let _ = run_with_log(scenario, fencing, captured)?;
    let log = log.lock().unwrap();
    // `?` converts the `String` through `From`, which both of the boxed error
    // types turmoil's `Result` alias could be built on implement. Naming the
    // box here instead would pin this file to one of them.
    check_invariants(&log)?;
    Ok(log.iter().filter(|e| matches!(e, Event::Wrote { .. })).count())
}

/// Run the simulation, leaving the coordinator's log in `out` and returning
/// each node's own tally of what it attempted.
fn run_with_log(
    scenario: Scenario,
    fencing: bool,
    out: Arc<Mutex<Vec<Event>>>,
) -> turmoil::Result<Vec<Attempts>> {
    let mut sim = Builder::new()
        .rng_seed(scenario.seed)
        // Latency is bounded well below the settle window below, on purpose.
        // turmoil's default upper bound is a tenth of a second, which is longer
        // than a scenario step: with it, almost every request would still be in
        // flight when the next action was queued and the run would be dominated
        // by its own backlog rather than by the protocol. Reordering across
        // nodes survives — two hosts acting at once still race — and the
        // partitions, which are what this suite is actually about, are
        // unaffected either way.
        .min_message_latency(Duration::from_millis(1))
        .max_message_latency(Duration::from_millis(10))
        .simulation_duration(Duration::from_secs(120))
        .build();

    // The coordinator. One host, one registry, updated under a lock — which is
    // the executable form of the model's load-bearing assumption that ownership
    // records are updated atomically. A deployment buys that from consensus or
    // a compare-and-swap store; here it is a `Mutex`, and saying so is the
    // point: the assumption is visible rather than smuggled in.
    let coord = Arc::new(Mutex::new(Coord::new(fencing)));
    let coord_for_host = coord.clone();
    sim.host("coord", move || {
        let coord = coord_for_host.clone();
        async move {
            let listener =
                TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let coord = coord.clone();
                tokio::spawn(async move {
                    let mut reader = BufReader::new(stream);
                    let mut line = String::new();
                    if reader.read_line(&mut line).await.is_err() {
                        return;
                    }
                    // The verdict and the decision to answer late are taken
                    // together, under the one lock, and the wait happens after
                    // it is released — both because holding a `std` mutex
                    // across an await is a deadlock waiting to happen, and
                    // because the registry really has moved by then. That is
                    // the whole point: the effect has landed and the caller
                    // does not know it.
                    let (reply, answer_late) = {
                        let mut guard = coord.lock().unwrap();
                        let reply = guard.handle(line.trim());
                        (reply, guard.take_slow_reply())
                    };
                    if answer_late {
                        tokio::time::sleep(RPC_TIMEOUT * 2).await;
                    }
                    let mut stream = reader.into_inner();
                    let _ = stream.write_all(reply.as_bytes()).await;
                    let _ = stream.write_all(b"\n").await;
                    let _ = stream.flush().await;
                });
            }
            // A host runs until the simulation does, so the loop above has no
            // exit. Writing the tail out anyway means the future's type is
            // stated rather than inferred from a diverging block.
            #[allow(unreachable_code)]
            Ok(())
        }
    });

    // Each node is its own host, so a partition can isolate one of them while
    // the others keep going. The queue is test scaffolding rather than
    // protocol: turmoil hosts are tasks in one process, so the driver hands
    // work to a node the same way a local caller would.
    let queues: Vec<Arc<Mutex<VecDeque<NodeCmd>>>> =
        (0..NODES).map(|_| Arc::new(Mutex::new(VecDeque::new()))).collect();

    // A mirror of each node's own counters, kept outside the simulation so a
    // caller can read them once it has finished.
    let stats: Vec<Arc<Mutex<Attempts>>> =
        (0..NODES).map(|_| Arc::new(Mutex::new(Attempts::default()))).collect();

    for n in 0..NODES {
        let queue = queues[n as usize].clone();
        let stat = stats[n as usize].clone();
        sim.host(node_host(n), move || {
            let queue = queue.clone();
            let stat = stat.clone();
            async move {
                // Local state survives isolation, which is what `tr_recover`
                // says: a node comes back still holding what it had.
                let mut state = NodeState::default();
                loop {
                    let cmd = queue.lock().unwrap().pop_front();
                    match cmd {
                        None => {
                            tokio::time::sleep(Duration::from_millis(5)).await;
                        }
                        Some(cmd) => {
                            // A request that a partition swallows simply never
                            // answers. That is the network's doing, not a
                            // protocol violation, so it is never an assertion
                            // failure here — the oracles run over what the
                            // coordinator accepted, and a lost request is one
                            // it never saw.
                            let _ = run_cmd(n, cmd, &mut state).await;
                            *stat.lock().unwrap() = state.attempts;
                        }
                    }
                }
                #[allow(unreachable_code)]
                Ok(())
            }
        });
    }

    let coord_for_client = coord.clone();
    let queues_for_client = queues.clone();
    sim.client("driver", async move {
        for action in scenario.actions {
            match action {
                Action::Poll { node } => push(&queues_for_client, node, NodeCmd::Poll),
                Action::Acquire { node } => push(&queues_for_client, node, NodeCmd::Acquire),
                Action::Write { node } => push(&queues_for_client, node, NodeCmd::Write),
                Action::Release { node } => push(&queues_for_client, node, NodeCmd::Release),
                Action::Handover { from, to } => push(
                    &queues_for_client,
                    from,
                    NodeCmd::Handover { to: to as u64 % NODES },
                ),
                Action::Force { next } => {
                    let _ = rpc(format!("FORCE {}", next as u64 % NODES)).await;
                }
                Action::Isolate { node } => {
                    turmoil::partition(node_host(node as u64 % NODES), "coord");
                }
                Action::Rejoin { node } => {
                    turmoil::repair(node_host(node as u64 % NODES), "coord");
                }
                Action::Stall { node } => {
                    turmoil::hold(node_host(node as u64 % NODES), "coord");
                }
                Action::Resume { node } => {
                    turmoil::release(node_host(node as u64 % NODES), "coord");
                }
                Action::Sleep { millis } => {
                    tokio::time::sleep(Duration::from_millis(millis as u64 + 1)).await;
                }
                Action::SlowReply => coord_for_client.lock().unwrap().arm_slow_reply(),
            }
            // Give whatever was just queued a chance to reach the wire and be
            // answered. Without this the driver would run to the end before any
            // node had acted, and every scenario would collapse to the same
            // empty run. It is longer than a round trip at the latency set
            // above, so a step ordinarily completes before the next is queued;
            // that is what makes a named story readable as a story.
            tokio::time::sleep(SETTLE).await;
        }

        // Let the last requests land, and put the network back together so
        // anything still queued can finish. A scenario that ends mid-partition
        // would otherwise report fewer writes than it actually caused, and a
        // fixed final sleep would do the same to any scenario whose last
        // actions queued behind a timed-out request.
        //
        // So the drain waits for the queues to empty rather than for a clock.
        // The bound is there because a queue emptying is not guaranteed — it
        // only takes one host whose current request is mid-timeout — and a
        // drain that could not end would turn a scenario that misbehaved into
        // a hang instead of a failure.
        for n in 0..NODES {
            turmoil::repair(node_host(n), "coord");
            // A held link is not a repaired one: `repair` restores the route,
            // `release` delivers what was held on it. A drain that did only the
            // first would wait out its bound on a node whose request is still
            // sitting in the network.
            turmoil::release(node_host(n), "coord");
        }
        for _ in 0..200 {
            let outstanding: usize =
                queues_for_client.iter().map(|q| q.lock().unwrap().len()).sum();
            if outstanding == 0 {
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        // The last command is off the queue but still in flight.
        tokio::time::sleep(Duration::from_millis(500)).await;

        *out.lock().unwrap() = coord_for_client.lock().unwrap().log.clone();
        Ok(())
    });

    sim.run()?;
    Ok(stats.iter().map(|s| *s.lock().unwrap()).collect())
}

fn push(queues: &[Arc<Mutex<VecDeque<NodeCmd>>>], node: u8, cmd: NodeCmd) {
    let idx = (node as u64 % NODES) as usize;
    queues[idx].lock().unwrap().push_back(cmd);
}

/// Ask the coordinator what this node is currently offered, and record it.
///
/// The only branch that touches the guard is `GRANT`: a `NONE` reply leaves a
/// stale guard exactly as stale as it was, which is deliberate. A node that has
/// been superseded is not told so by a poll — it is simply no longer the
/// intended owner — and if polling quietly cleared the guard, the scenario this
/// whole suite is about could never arise.
async fn poll(node: u64, state: &mut NodeState) -> io::Result<()> {
    let reply = rpc(format!("POLL {node}")).await?;
    let mut parts = reply.split_whitespace();
    match (parts.next(), parts.next().and_then(|e| e.parse::<u64>().ok())) {
        (Some("GRANT"), Some(epoch)) => {
            // A fresh generation observed. `FenceGuard` has no setter, so
            // observing one means constructing a new guard — the model's
            // `Observing a new generation means constructing a new guard` made
            // literal.
            state.guard = Some((node, epoch));
            state.pending_revoke = None;
        }
        (Some("REVOKE"), Some(new_epoch)) => {
            state.pending_revoke = Some(new_epoch);
        }
        _ => {}
    }
    Ok(())
}

/// Execute one node command over the network.
async fn run_cmd(node: u64, cmd: NodeCmd, state: &mut NodeState) -> io::Result<()> {
    match cmd {
        NodeCmd::Poll => poll(node, state).await?,
        NodeCmd::Acquire => {
            // Ask, then take. A node that wants the actor finds out what it is
            // being offered first, because an acquire has to name the exact
            // epoch on offer and a node that never asked cannot know it.
            //
            // This also decides how much of the state space the blind search
            // reaches, and the first version got it wrong. With `Acquire`
            // sending only when the node already happened to hold a grant, an
            // accepted write needed the ordered triple poll-acquire-write at
            // one node, and a walk over the first 256 seeds produced 22 of
            // them: 94% of scenarios never reached the fence at all and passed
            // by doing nothing. Folding the poll in is both more faithful and
            // four times as productive.
            poll(node, state).await?;
            if let Some((_, epoch)) = state.guard {
                let _ = rpc(format!("ACQUIRE {node} {epoch}")).await?;
            }
        }
        NodeCmd::Write => {
            // The node asks its own guard first, exactly as a real one would.
            // A stale guard says yes; the coordinator is what says no. That
            // gap is the point, and it is why the verdict is ignored: whether
            // the write landed is the oracle's business, not the node's.
            //
            // A timeout is counted, not propagated. The node does not know
            // whether the coordinator saw the request, so it carries on — and
            // a node that stopped working because one write went unanswered
            // would be treating silence as a decision.
            if let Some((_, epoch)) = state.would_write(node) {
                state.attempts.writes_sent += 1;
                match rpc(format!("WRITE {node} {epoch}")).await {
                    Ok(_) => {}
                    Err(e) if e.kind() == io::ErrorKind::TimedOut => {
                        state.attempts.writes_timed_out += 1;
                    }
                    Err(_) => state.attempts.writes_failed += 1,
                }
            }
        }
        NodeCmd::Handover { to } => {
            // Sent unconditionally, without consulting what this node believes
            // it owns: the registry is what decides whether this node is in a
            // position to agree, and a `BEGIN` from a node that is not the
            // owner is a request worth seeing refused.
            let _ = rpc(format!("BEGIN {node} {to}")).await?;
        }
        NodeCmd::Release => {
            if let Some(new_epoch) = state.pending_revoke {
                let _ = rpc(format!("RELEASE {node} {new_epoch}")).await?;
                state.pending_revoke = None;
                // The node has given the actor up; its guard is no longer a
                // claim to anything. Dropping it here is the honest thing: the
                // node knows it released.
                state.guard = None;
            }
        }
    }
    Ok(())
}
