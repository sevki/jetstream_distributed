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
struct Coord {
    state: Owned,
    log: Vec<Event>,
    /// Writes accepted so far, used to give each one a sequence number.
    writes: u64,
    /// When false the coordinator skips its fence check. Used only by the
    /// self-test that proves these oracles can fail — see
    /// [`run_scenario_unfenced`].
    fencing: bool,
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
    fn new(fencing: bool) -> Self {
        Coord {
            // The same start state the scenarios in `src/proofs` use: offered
            // to node 0 at epoch 41, held by nobody.
            state: Owned::Unowned { epoch: 41, intended: 0 },
            log: Vec::new(),
            writes: 0,
            fencing,
        }
    }

    /// Handle one request line, returning the reply line.
    ///
    /// Every branch is one of the model's transitions, and the comments name
    /// which. Keeping them in step is the whole point: a transition the
    /// implementation has that the model does not is exactly the kind of thing
    /// this suite exists to find.
    fn handle(&mut self, line: &str) -> String {
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
            ("BEGIN", [to]) => match self.state {
                Owned::Owned { owner, epoch } if owner != *to => {
                    self.state = Owned::Transferring {
                        from: owner,
                        to: *to,
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
            ("RELEASE", [node]) => match self.state {
                Owned::Transferring { from, to, new_epoch, .. } if from == *node => {
                    self.state = Owned::Unowned { epoch: new_epoch, intended: to };
                    self.log.push(Event::Released { node: *node, new_epoch });
                    "OK".to_string()
                }
                _ => "NO".to_string(),
            },

            // `tr_revoke_owner`: the coordinator burns the epoch *without* the
            // owner's cooperation. Fires against a healthy owner on purpose —
            // unreliable failure detection is modelled, not assumed away.
            ("FORCE", [next]) => match self.state {
                Owned::Owned { epoch, .. } | Owned::Unowned { epoch, .. } => {
                    self.state = Owned::Unowned { epoch: epoch + 1, intended: *next };
                    self.log.push(Event::EpochBurned {
                        from_epoch: epoch,
                        to_epoch: epoch + 1,
                        next: *next,
                        forced: true,
                    });
                    "OK".to_string()
                }
                Owned::Transferring { new_epoch, .. } => {
                    self.state = Owned::Unowned { epoch: new_epoch + 1, intended: *next };
                    self.log.push(Event::EpochBurned {
                        from_epoch: new_epoch,
                        to_epoch: new_epoch + 1,
                        next: *next,
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
/// A partition in turmoil *drops* messages rather than refusing them, so a
/// request sent across one is never answered and never fails either. Without a
/// deadline the first isolation would park that node for the rest of the run —
/// it would never deadlock the simulation, because the driver is what ends it,
/// but every later action aimed at that node would be silently discarded and
/// the scenario would be shorter than it looked. A real node has exactly this
/// problem and exactly this answer. The clock is simulated, so the wait costs
/// ordering and nothing else.
const RPC_TIMEOUT: Duration = Duration::from_millis(250);

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
    /// The owner agrees to hand over. `tr_begin_transfer`.
    Handover { to: u8 },
    /// The coordinator burns the epoch without asking. `tr_revoke_owner`.
    Force { next: u8 },
    /// Cut a node off — indistinguishable, from outside, from a crash.
    Isolate { node: u8 },
    /// Let it back in. The node returns still holding its old guard, which is
    /// the headline scenario.
    Rejoin { node: u8 },
    /// Let time pass, so in-flight requests land.
    Sleep { millis: u8 },
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
        match choice % 12 {
            0..=1 => Action::Poll { node },
            2..=3 => Action::Acquire { node },
            4..=6 => Action::Write { node },
            7 => Action::Release { node },
            8 => Action::Handover { to: node },
            9 => Action::Force { next: node },
            10 => {
                if param % 2 == 0 {
                    Action::Isolate { node }
                } else {
                    Action::Rejoin { node }
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

    // Claim 5 — epoch monotonicity. The registry's epoch never goes backwards.
    let mut epoch = 0u64;
    for ev in log {
        if let Event::EpochBurned { from_epoch, to_epoch, .. } = ev {
            if *to_epoch <= *from_epoch {
                return Err(format!(
                    "claim 5 (monotonicity): epoch went {from_epoch} -> {to_epoch}"
                ));
            }
            if *from_epoch < epoch {
                return Err(format!(
                    "claim 5 (monotonicity): epoch {from_epoch} is below the high \
                     water mark {epoch}"
                ));
            }
            epoch = *to_epoch;
        }
    }

    // P5 / P6 — ownership at an epoch is final, and an epoch determines its
    // owner. Accepted writes never regress to an epoch that has already been
    // superseded by a later accepted write.
    let mut high = 0u64;
    for ev in log {
        if let Event::Wrote { epoch, node, seq } = ev {
            if *epoch < high {
                return Err(format!(
                    "P5/P6: node {node} wrote at epoch {epoch} (seq {seq}) after a \
                     write at epoch {high} had already been accepted"
                ));
            }
            high = *epoch;
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
                        "P8: node {node} wrote at epoch {epoch} (seq {seq}) without \
                         ever having acquired it"
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
    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = log.clone();
    run_with_log(scenario, true, captured)?;
    let out = log.lock().unwrap().clone();
    check_invariants(&out)?;
    Ok(out)
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
    run_with_log(scenario, false, captured)?;
    let out = log.lock().unwrap().clone();
    Ok(out)
}

fn run_inner(scenario: Scenario, fencing: bool) -> turmoil::Result<usize> {
    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = log.clone();
    run_with_log(scenario, fencing, captured)?;
    let log = log.lock().unwrap();
    // `?` converts the `String` through `From`, which both of the boxed error
    // types turmoil's `Result` alias could be built on implement. Naming the
    // box here instead would pin this file to one of them.
    check_invariants(&log)?;
    Ok(log.iter().filter(|e| matches!(e, Event::Wrote { .. })).count())
}

fn run_with_log(
    scenario: Scenario,
    fencing: bool,
    out: Arc<Mutex<Vec<Event>>>,
) -> turmoil::Result<()> {
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
                    let reply = {
                        let mut guard = coord.lock().unwrap();
                        guard.handle(line.trim())
                    };
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

    for n in 0..NODES {
        let queue = queues[n as usize].clone();
        sim.host(node_host(n), move || {
            let queue = queue.clone();
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
                Action::Handover { to } => {
                    let _ = rpc(format!("BEGIN {}", to as u64 % NODES)).await;
                }
                Action::Force { next } => {
                    let _ = rpc(format!("FORCE {}", next as u64 % NODES)).await;
                }
                Action::Isolate { node } => {
                    turmoil::partition(node_host(node as u64 % NODES), "coord");
                }
                Action::Rejoin { node } => {
                    turmoil::repair(node_host(node as u64 % NODES), "coord");
                }
                Action::Sleep { millis } => {
                    tokio::time::sleep(Duration::from_millis(millis as u64 + 1)).await;
                }
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

    sim.run()
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
            // gap is the point, and it is why the reply is ignored: whether
            // the write landed is the oracle's business, not the node's.
            if let Some((_, epoch)) = state.would_write(node) {
                let _ = rpc(format!("WRITE {node} {epoch}")).await?;
            }
        }
        NodeCmd::Release => {
            if state.pending_revoke.is_some() {
                let _ = rpc(format!("RELEASE {node}")).await?;
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
