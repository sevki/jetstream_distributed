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

/// The host the driver runs on, which stands in for the registry's own control
/// path — the failure detector that decides to revoke an owner.
const CONTROL_HOST: &str = "driver";

/// Who a connection is, as far as the registry can tell.
///
/// The addresses are turmoil's, assigned per host, so this is the simulation's
/// stand-in for an authenticated peer identity. A real deployment would get it
/// from mTLS or a signed token; what matters is that it comes from the
/// connection rather than from the request body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Peer {
    /// One of the nodes.
    Node(u64),
    /// The registry's own control path.
    Control,
    /// Somebody else.
    ///
    /// This variant exists because the first version of this check had no
    /// place for it: it asked `peer.is_none()` and treated that as "the
    /// control path", which is authorisation by exclusion. `None` meant
    /// *unknown*, so any host that was not one of the three nodes could burn
    /// an epoch — which is most of them.
    Unknown,
}

fn peer_of(ip: IpAddr) -> Peer {
    if let Some(n) = (0..NODES).find(|n| turmoil::lookup(node_host(*n)) == ip) {
        return Peer::Node(n);
    }
    if turmoil::lookup(CONTROL_HOST) == ip {
        return Peer::Control;
    }
    Peer::Unknown
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
    /// The registry offered the actor to this node at this epoch.
    ///
    /// `Message::Grant`. Logged because `tr_acquire` requires one to be in
    /// flight, and an acquire cannot be checked against a grant nobody wrote
    /// down — the audit log had no record of what was ever offered.
    Granted { node: u64, epoch: u64 },
    /// The registry told this node to stop, ahead of the new epoch.
    ///
    /// `Message::Revoke`, whose `target` the model binds to the transfer's
    /// outgoing owner. Logged for the same reason as `Granted`: `POLL` guards
    /// who may be told, and a guard nothing records is a guard nothing checks.
    Revoked { node: u64, new_epoch: u64 },
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
    /// How the coordinator's `WRITE` arm decides. Anything but
    /// [`Fence::Checked`] is a deliberately broken registry, used only by the
    /// self-tests that prove these oracles can fail.
    fence: Fence,
    /// The grants this registry has issued, as `(node, epoch)`.
    ///
    /// `tr_acquire` wants `pre.network.contains(Message::Grant { to: n, epoch })`,
    /// so an acquire needs an offer that was actually made. The oracle was
    /// taught to check this and the registry was not, which meant a fresh
    /// `ACQUIRE 0 41` succeeded with no `POLL` before it — outside the model,
    /// and invisible because the generated `Acquire` action polls first.
    issued: Vec<(u64, u64)>,
    /// Delay the next reply past the caller's deadline, once.
    ///
    /// The network can delay a *request*; only the coordinator can accept one
    /// and then answer too late. The two are different failures and the second
    /// is the one a node's doc comment claims not to over-read: a timeout says
    /// no answer arrived, never that the write was not applied.
    slow_next_reply: bool,
}

/// What the coordinator does with a `WRITE`.
///
/// A bool would do for two of these, and did until there were three. The
/// third exists because the oracles are not symmetric on their own: seven of
/// them bound what was *accepted*, so a registry that refused everything
/// satisfied all seven. Disabling the fence and jamming it on are the two
/// ways to be wrong about the same check, and each has an oracle that should
/// catch it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fence {
    /// The fence as specified: accept exactly when the actor is `Owned` by
    /// this node at this epoch. Every real run uses this.
    Checked,
    /// Accept everything. Breaks claims 2/3 — see `run_scenario_unfenced`.
    Never,
    /// Refuse everything, including the current owner writing at its own
    /// epoch. Breaks nothing among the first seven oracles, which is the
    /// point — see `run_scenario_overfenced`.
    Always,
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
    pub fn new(fence: Fence) -> Self {
        Coord {
            // The same start state the scenarios in `src/proofs` use: offered
            // to node 0 at the initial epoch, held by nobody.
            state: Owned::Unowned { epoch: INITIAL_EPOCH, intended: INITIAL_OWNER },
            log: Vec::new(),
            writes: 0,
            fence,
            issued: Vec::new(),
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
    /// The audit log so far.
    ///
    /// Exposed for the protocol search, which drives this registry directly
    /// rather than over a socket and so has nowhere else to read the log from.
    pub fn log(&self) -> &[Event] {
        &self.log
    }

    pub fn handle(&mut self, line: &str, peer: Peer) -> String {
        let mut parts = line.split_whitespace();
        let verb = parts.next().unwrap_or("");
        // Every field parses or the line is malformed. `filter_map` quietly
        // *dropped* what it could not parse, which turns a bad request into a
        // shorter good one: `POLL junk 0` became `POLL 0`, and after a grant
        // `ACQUIRE 0 junk 41` became `ACQUIRE 0 41`. The raw-line boundary
        // exists precisely to accept what the generator cannot express, and it
        // was sanitising it on the way in.
        let Some(args) = parts.map(|p| p.parse::<u64>().ok()).collect::<Option<Vec<u64>>>()
        else {
            return "ERR".to_string();
        };

        // Who a request claims to be from is a field in the line. Who it is
        // actually from is the connection it arrived on, and the registry has
        // to believe the second.
        //
        // The model binds every node-authored transition to a node that is
        // `live`, and the simulation's counterpart of `live` is `reachable`.
        // That only means something if a partition can stop the request — and
        // it cannot stop one somebody else sends. Routing the generated
        // commands through the owner's host, which is how an earlier round
        // closed this, protects the *driver*; it does nothing at the line
        // protocol, where any reachable client could send `BEGIN 0 2` while
        // node 0 was partitioned away and the partition would protect nothing.
        //
        // `FORCE` is the one verb no node may send, and the reasoning that
        // first exempted it was half right. `tr_revoke_owner` makes no node
        // act — so there is nobody to authenticate *as* — but that means the
        // registry's own control path may initiate it, not that anything
        // reachable may. Left open, a node could sit in a loop revoking
        // whoever legitimately held the actor. The driver stands in for the
        // registry here, so `FORCE` requires the control connection —
        // named, not merely "not a node's". That distinction is the whole
        // fix: the first version asked for anything that was not a node, so
        // every host nobody had heard of qualified.
        if verb == "FORCE" && peer != Peer::Control {
            return "NO".to_string();
        }

        let claimed = match (verb, args.as_slice()) {
            ("POLL", [node])
            | ("ACQUIRE", [node, _])
            | ("WRITE", [node, _])
            | ("BEGIN", [node, _])
            | ("RELEASE", [node, _]) => Some(*node),
            _ => None,
        };
        if let Some(node) = claimed {
            if peer != Peer::Node(node) {
                return "NO".to_string();
            }
        }

        match (verb, args.as_slice()) {
            // What does this node currently have on offer? A node with no
            // grant has nothing to acquire with.
            ("POLL", [node]) => match self.state {
                Owned::Unowned { epoch, intended } if intended == *node => {
                    self.issued.push((*node, epoch));
                    self.log.push(Event::Granted { node: *node, epoch });
                    format!("GRANT {epoch}")
                }
                Owned::Transferring { from, new_epoch, .. } if from == *node => {
                    // `tr_handle_revoke`: the outgoing owner is told to stop.
                    self.log.push(Event::Revoked { node: *node, new_epoch });
                    format!("REVOKE {new_epoch}")
                }
                _ => "NONE".to_string(),
            },

            // `tr_acquire`. Only from `Unowned`, only by the intended owner,
            // only at exactly that epoch.
            //
            // The grant has to have been issued, not merely be due. This is the
            // second conjunct of `tr_acquire`, and it was missing here for the
            // same reason it was missing from the oracle: the generated
            // `Acquire` action polls first, so nothing in the suite ever tried
            // to acquire without asking.
            ("ACQUIRE", [node, epoch]) if !self.issued.contains(&(*node, *epoch)) => {
                "NO".to_string()
            }
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
                let accepted = match self.fence {
                    Fence::Checked => permitted,
                    Fence::Never => true,
                    Fence::Always => false,
                };
                if accepted {
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
    /// Writes that were never sent, because the connection was never made.
    ///
    /// `RpcFailure::NoRoute` and nothing else. This is the only counter here
    /// whose entries are writes the node may soundly conclude did not happen,
    /// which is why it has to mean exactly one thing.
    ///
    /// It said "refused, reset, cut off mid-reply" and counted every
    /// non-timeout error, while the seed walk printed it as "with no route".
    /// So a request that went out in full and lost only its reply was reported
    /// as one the network never carried — the resiliency diagnostics claiming
    /// the strongest of the three readings for the weakest evidence.
    ///
    /// Kept apart from the deadline count rather than lumped in with it,
    /// because those two mean opposite things. No route is the network
    /// answering; a deadline is the network saying nothing at all, and only
    /// the second is what a story about silence is entitled to claim.
    pub writes_failed: u64,
    /// Writes that went out, wholly or partly, and got no reply back.
    ///
    /// `RpcFailure::Disconnected` and `RpcFailure::Cut` together: the
    /// connection ended before a reply, or the send itself failed partway. The
    /// two are one counter because they leave the node in the same position —
    /// the coordinator may have the request, and there is no way to find out.
    /// That is the same standing as a timeout, and it is separate from the
    /// timeout count only because the events differ: a run full of these would
    /// mean the simulated network is severing established connections rather
    /// than exercising the protocol.
    pub writes_disconnected: u64,
}

/// Why a round trip produced no reply.
///
/// Classified by *where in the exchange* it stopped, rather than by the
/// `io::ErrorKind` that came back, because where it stopped is the only thing
/// the node genuinely knows and the kind is the simulator's opinion. Reading
/// the kind is what produced two earlier mistakes here: the claim that a
/// partitioned connect hangs, and the counting of every non-timeout error as
/// a no-route failure.
///
/// The distinction that matters is not how the failure looked but whether the
/// request can have been applied. `NoRoute` is the only variant that answers
/// no.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RpcFailure {
    /// The connection was never established, so nothing was sent and nothing
    /// can have landed. This is how turmoil reports a partition to a sender,
    /// and it is the one case where a node could soundly conclude its write
    /// did not happen.
    NoRoute,
    /// Established, then failed while the request was still going out. The
    /// coordinator may have read part of a line or all of it, so this says
    /// nothing about whether the write landed — which is why it is not
    /// `NoRoute`, though it used to be counted as one.
    Cut,
    /// The request went out and the connection ended before any reply.
    Disconnected,
    /// The request went out and nothing came back before the deadline.
    TimedOut,
}

/// One request/response round trip. A fresh connection per request, which is
/// slower than a long-lived lane and much easier to reason about: a partition
/// stops the next request rather than half-killing an established one.
///
/// A failure is reported as an error, which is the honest answer: except for
/// `NoRoute`, the node does not know whether the coordinator saw the request.
/// Nothing here retries, and nothing here treats a timeout as a refusal — a
/// node that assumed "no reply" meant "not applied" would be the bug this
/// whole model is about.
async fn rpc(req: String) -> Result<String, RpcFailure> {
    match tokio::time::timeout(RPC_TIMEOUT, rpc_inner(req)).await {
        Ok(result) => result,
        Err(_) => Err(RpcFailure::TimedOut),
    }
}

async fn rpc_inner(req: String) -> Result<String, RpcFailure> {
    // Each `?` below is tagged with the phase it is in, so the caller never
    // has to infer the phase from the error. Only this first one means the
    // request was never sent.
    let mut stream = TcpStream::connect(("coord", PORT))
        .await
        .map_err(|_| RpcFailure::NoRoute)?;
    stream.write_all(req.as_bytes()).await.map_err(|_| RpcFailure::Cut)?;
    stream.write_all(b"\n").await.map_err(|_| RpcFailure::Cut)?;
    stream.flush().await.map_err(|_| RpcFailure::Cut)?;
    let mut reply = String::new();
    let n = BufReader::new(&mut stream)
        .read_line(&mut reply)
        .await
        .map_err(|_| RpcFailure::Disconnected)?;
    // `read_line` reports a clean EOF as `Ok(0)`, and a line that ended
    // without a newline as `Ok(n)` with no `\n` in the buffer. Neither is a
    // reply, and returning `Ok("")` for the first made the caller count the
    // request as answered: `run_cmd` matches `Ok(_) => {}`, so a write whose
    // connection ended before the coordinator said anything was neither
    // timed out nor failed. A story asserting the request was answered before
    // the deadline would have been satisfied by silence.
    if n == 0 || !reply.ends_with('\n') {
        return Err(RpcFailure::Disconnected);
    }
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

/// The guards this function cannot witness, and where they are checked
/// instead.
///
/// There are two reasons an oracle here misses a guard, and they are
/// different problems with the same remedy.
///
/// **The log does not record the difference.** An oracle reads the audit log,
/// so it can only see a guard whose violation changes what gets written. Two
/// do not.
///
/// `ACQUIRE` requires the epoch a node quotes to match the registry's, and the
/// handler logs the epoch it *acquired* — so a request naming any epoch at all
/// produces the same, entirely valid-looking, `Acquired`.
///
/// `POLL` decides who is told to stand down, and the `Revoked` it writes sits
/// *inside* that guarded arm: delete the guard and the logging moves with it.
/// An audit event cannot witness a guard it is nested in. `Granted` has the
/// same shape for the same reason — it is written inside `POLL`'s
/// `intended == node` arm — so it witnesses what an offer looks like, not the
/// decision to make one.
///
/// All three are witnessed by driving `Coord` with raw lines instead — see
/// `the_registry_refuses_an_acquire_quoting_the_wrong_epoch`,
/// `the_registry_does_not_tell_a_bystander_to_stand_down` and
/// `the_registry_does_not_offer_the_actor_to_a_bystander`. The log is the wrong
/// instrument for a guard about the request rather than the result; the
/// protocol boundary is the right one.
///
/// **Nothing ever sends the request.** The larger category, and the one that
/// has produced the most findings. The oracle would see the violation, but no
/// scenario can produce it: `Action::from_pair` generates only well-formed
/// requests, and a named story drives the same node agent, which sends what a
/// correct node would send. A guard against a request the alphabet cannot
/// express is unreachable however many seeds the walk counts through — a
/// handover to the sender itself, a write against somebody else's live epoch,
/// a release from the node receiving the actor rather than the one giving it
/// up, a successor that is not a node, a `FORCE` from a node, a line that does
/// not parse. Every one of those had to be reached by hand.
///
/// The general lesson is that a search is bounded by its generator and says
/// nothing whatever about what the generator cannot say. Both categories are
/// covered the same way: construct the request at the protocol boundary and
/// assert the refusal, rather than hoping a scenario wanders into it.
///
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
            // All three say the registry was at this exact epoch when the event
            // was recorded: an offer publishes the epoch the registry is at,
            // an acquire takes it, and a release lands on it.
            //
            // `Granted` was left out of this loop at first, while the grant
            // oracle's own comment claimed the epoch had to match — the same
            // half-implemented conjunct as `tr_acquire`, for the third time. A
            // bare `Granted(0, 42)` at the start passed everything: the grant
            // oracle checked only the node, and this loop was not looking.
            Event::Acquired { epoch: at, .. }
            | Event::Released { new_epoch: at, .. }
            | Event::Granted { epoch: at, .. } => {
                if *at != epoch {
                    return Err(format!(
                        "claim 5 (monotonicity): the registry was at epoch \
                         {epoch} and is now at {at}, with no burn between \
                         ({ev:?})"
                    ));
                }
            }
            // `Revoked` also names the registry's current epoch exactly — a
            // stand-down order is written while the actor is `Transferring`,
            // and that phase begins with the burn to `new_epoch`. It is left
            // out because claim 4 already pins it harder than this loop could:
            // a revoke must name the transfer in flight, and that transfer's
            // epoch came from an `EpochBurned` this loop has already checked.
            // Adding it here would be redundant rather than wrong, and a
            // redundant check reads like a second opinion when it is an echo.
            Event::Wrote { .. } | Event::Fenced { .. } | Event::Revoked { .. } => {}
        }
    }

    // P5 / P6 — an epoch determines its owner, and ownership at an epoch is
    // final. An epoch is acquired once, full stop.
    //
    // This heading said "two acquires of the same epoch must name the same
    // node" for one commit after the code stopped meaning it, which is the
    // recurring mismatch of this file running the other way: usually the
    // comment promises more than the code does, here it promised less. A reader
    // trusting it would have thought a same-node repeat was allowed. Found by
    // sweeping every check in this function against its own heading, which is
    // the audit that mismatch earned.
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
    // Any second acquire of an epoch, not just one by a different node.
    // Rejecting only a different node was a mistake, and one I compounded by
    // claiming in review that a same-node repeat would be caught here: it was
    // not, and `tr_acquire` cannot fire the second time either way, because the
    // actor is already `Owned`. Ownership at an epoch being *final* means the
    // acquire happens once.
    let mut owner_at: HashMap<u64, u64> = HashMap::new();
    for ev in log {
        if let Event::Acquired { node, epoch } = ev {
            if let Some(prev) = owner_at.get(epoch) {
                return Err(format!(
                    "P5/P6: epoch {epoch} was acquired by node {prev} and then \
                     again by node {node} — ownership at an epoch is not final \
                     if it can be taken twice"
                ));
            }
            owner_at.insert(*epoch, *node);
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
    let mut granted: Vec<(u64, u64)> = Vec::new();
    for ev in log {
        match ev {
            Event::EpochBurned { next, .. } => intended = *next,
            // An offer goes to the node the registry is holding the actor for.
            // The other half — that it names the epoch the registry is at — is
            // the monotonicity loop above, which reads every event that exposes
            // the registry's epoch and a grant is one of them. Checking it
            // twice would be two trackers to keep in step; checking it nowhere
            // is what happened first.
            Event::Granted { node, epoch } => {
                if *node != intended {
                    return Err(format!(
                        "P8 (grant): the registry offered epoch {epoch} to node \
                         {node}, but the actor is held for node {intended}"
                    ));
                }
                granted.push((*node, *epoch));
            }
            Event::Acquired { node, epoch } => {
                if *node != intended {
                    return Err(format!(
                        "P8 (grant): node {node} acquired epoch {epoch}, which \
                         was offered to node {intended}"
                    ));
                }
                // The second conjunct of `tr_acquire`, and the one this suite
                // was missing: `pre.network.contains(Message::Grant { to: n,
                // epoch })`. Being the intended owner is not enough — the model
                // wants the offer to have been made, and nothing here could
                // check that until grants were written down.
                if !granted.contains(&(*node, *epoch)) {
                    return Err(format!(
                        "P8 (grant): node {node} acquired epoch {epoch} without \
                         ever having been offered it"
                    ));
                }
            }
            _ => {}
        }
    }

    // Claim 4 — transfer safety. A handover goes to somebody else, and the
    // release that completes it comes from the node it is taking the actor
    // from, naming the transfer actually in flight.
    //
    // The last two items of the audit that followed @codex's acquire findings,
    // and the same shape as the rest: `tr_begin_transfer` requires
    // `from != to`, `tr_complete_release` binds `from` and `new_epoch` from the
    // current `Transferring`, and nothing here correlated either. A node could
    // hand the actor to itself, and a release could be credited to a node that
    // was never part of the transfer, without any oracle objecting.
    //
    // The outgoing owner is not in the log directly; it is the node that
    // acquired the epoch being burned, which is the same thing. A cooperative
    // burn from an epoch nobody acquired is itself a violation — `BEGIN`
    // requires `Owned` — so it is reported rather than skipped.
    //
    // A forced burn clears the pending transfer, because `tr_abort_transfer`
    // and `tr_revoke_owner` supersede it: a release arriving afterwards is
    // acknowledging something that no longer exists.
    // While a transfer is in flight the actor is `Transferring`, and in that
    // phase the registry offers nothing, nobody acquires, and no second
    // handover can be agreed — `IssueGrant` and `tr_acquire` want `Unowned`,
    // `tr_begin_transfer` wants `Owned`.
    //
    // Reading the outgoing owner out of `Acquired` alone, without that phase,
    // was the load-bearing inference in this check and it was wrong:
    // `Acquired(1,42)` logged while the first handover was still in flight
    // counted node 1 as a real owner, and a second cooperative burn then
    // overwrote the pending transfer. The whole sequence passed.
    let mut owner_at: HashMap<u64, u64> = HashMap::new();
    let mut pending: Option<(u64, u64)> = None;
    let mut owned = false;
    for ev in log {
        match ev {
            // `tr_issue_grant` applies to `Unowned` only, and the phase gate
            // covered `Transferring` and not `Owned` — so a second offer after
            // the actor had been taken passed, and `POLL`'s `Owned::Unowned`
            // arm could have been weakened with the suite still green. Half a
            // phase is the same mistake as half a conjunct.
            Event::Granted { epoch, .. } if owned => {
                return Err(format!(
                    "claim 4 (transfer): the registry offered epoch {epoch} \
                     while the actor was already held"
                ));
            }
            Event::Granted { epoch, .. } if pending.is_some() => {
                return Err(format!(
                    "claim 4 (transfer): the registry offered epoch {epoch} while \
                     the transfer {pending:?} was still in flight"
                ));
            }
            Event::Acquired { node, epoch } => {
                owned = true;
                if pending.is_some() {
                    return Err(format!(
                        "claim 4 (transfer): node {node} acquired epoch {epoch} \
                         while the transfer {pending:?} was still in flight"
                    ));
                }
                owner_at.insert(*epoch, *node);
            }
            Event::EpochBurned { from_epoch, to_epoch, next, forced: false } => {
                if pending.is_some() {
                    return Err(format!(
                        "claim 4 (transfer): a handover was agreed at epoch \
                         {from_epoch} while {pending:?} was still in flight"
                    ));
                }
                let Some(outgoing) = owner_at.get(from_epoch).copied() else {
                    return Err(format!(
                        "claim 4 (transfer): a handover was agreed at epoch \
                         {from_epoch}, which nobody owns"
                    ));
                };
                if *next == outgoing {
                    return Err(format!(
                        "claim 4 (transfer): node {outgoing} agreed to hand the \
                         actor to itself at epoch {from_epoch}"
                    ));
                }
                owned = false;
                pending = Some((outgoing, *to_epoch));
            }
            // A forced burn supersedes a transfer, and `tr_abort_transfer`
            // says where the actor goes: back to `from`. Clearing the pending
            // transfer without checking that was the same shape as everything
            // else here — the named story pins the current handler, but an
            // audited log could abort a handover to a third party and no oracle
            // would object.
            Event::EpochBurned { to_epoch, next, .. } => {
                if let Some((outgoing, _)) = pending {
                    if *next != outgoing {
                        return Err(format!(
                            "claim 4 (transfer): the handover from node \
                             {outgoing} was aborted at epoch {to_epoch}, which \
                             was offered to node {next} rather than back to it"
                        ));
                    }
                }
                owned = false;
                pending = None;
            }
            // A revoke names the node the actor is being taken from, and the
            // epoch it is being taken to. It does not complete anything, so it
            // leaves the transfer in flight.
            Event::Revoked { node, new_epoch } => {
                if pending != Some((*node, *new_epoch)) {
                    return Err(format!(
                        "claim 4 (transfer): node {node} was told to stand down \
                         at epoch {new_epoch}, but the transfer in flight is \
                         {pending:?}"
                    ));
                }
            }
            Event::Released { node, new_epoch } => {
                if pending != Some((*node, *new_epoch)) {
                    return Err(format!(
                        "claim 4 (transfer): node {node} released at epoch \
                         {new_epoch}, but the transfer in flight is {pending:?}"
                    ));
                }
                pending = None;
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

    // `may_mutate`, in the direction nothing above checks: the registry must
    // not refuse a write it was obliged to accept.
    //
    // Every oracle above bounds what was *accepted*. None bounds what was
    // refused, and that asymmetry is a hole with a shape: a coordinator whose
    // `WRITE` arm returned `FENCED` unconditionally satisfies all seven. It
    // accepts no two writers at an epoch, burns nothing out of order, hands
    // the actor over correctly and never lets a stale write through, because
    // it never lets any write through. The write floor in `turmoil_scenarios`
    // catches the *fully* degenerate version of that by counting accepted
    // writes across the window — but a registry that fenced only node 2, or
    // only every third request, would sail past a floor that asks for one
    // write per sixteen seeds.
    //
    // `may_mutate` is a biconditional where the handler is concerned:
    // `WRITE` accepts exactly when the actor is `Owned { owner: node, epoch }`
    // for the pair the request names. So a `Fenced` logged while the log says
    // that node holds that epoch is the registry refusing its own current
    // owner, and there is no state in the model where that is correct.
    //
    // This is the one oracle here that does not come from a theorem, and it
    // should not be dressed up as one. The Verus proofs are all of the form
    // "this cannot happen"; none of them says any write is ever accepted, and
    // none could — liveness is not what they are about. This checks the
    // definition of `may_mutate` rather than a consequence of it, which is
    // weaker provenance than every row above it and is recorded as such in the
    // README.
    //
    // Runs last so it cannot pre-empt an oracle that does come from a theorem.
    // `held` is `Some` only between an acquire and the next burn: a
    // cooperative burn moves the actor to `Transferring` and a forced one to
    // `Unowned`, and neither is a state where a write is permitted.
    let mut held: Option<(u64, u64)> = None;
    for ev in log {
        match ev {
            Event::Acquired { node, epoch } => held = Some((*node, *epoch)),
            Event::EpochBurned { .. } | Event::Released { .. } => held = None,
            Event::Fenced { node, epoch } => {
                if held == Some((*node, *epoch)) {
                    return Err(format!(
                        "may_mutate (refusals): node {node} was fenced at epoch \
                         {epoch} while the registry still held the actor \
                         for it — a refusal the model has no state for"
                    ));
                }
            }
            Event::Wrote { .. } | Event::Granted { .. } | Event::Revoked { .. } => {}
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The protocol boundary, driven by bytes
// ---------------------------------------------------------------------------
//
// Why this exists at all is the largest finding of the review that built this
// file. `Action::from_pair` emits only well-formed requests, and a named story
// drives the same node agent, which sends what a correct node would send. So
// every guard against a request the alphabet cannot express was invisible to
// the seed walk — not "not yet found", but unreachable however long it counts.
// Six of them had to be reached by hand, one test at a time.
//
// Hand-written tests are the right instrument for a guard somebody has already
// thought of. They are no instrument at all for the next one. This generator
// makes the malformed request a thing the search produces rather than a thing
// somebody remembered, and the property it checks is the one those six tests
// each check a single instance of: **no sequence of arbitrary lines from
// arbitrary peers can drive the registry into a state whose audit log the
// oracles reject.**
//
// Note what is *not* fuzzed here. `Scenario::from_bytes` would let a
// coverage-guided fuzzer steer the action alphabet, which explores deeper
// sequences of well-formed requests — a different axis, and not this one. A
// fuzzer over that entry point would not have found any of the six.

/// One thing that arrives at the registry: a connection, and a line on it.
///
/// The peer and the line are related but not determined by each other, and
/// getting that balance right took a measurement. A peer drawn independently
/// of the line is the spoof case — the registry must believe the connection
/// rather than the request body — but if it is *always* independent then a
/// well-formed request matches its sender only about a quarter of the time,
/// the run never advances past the connection check, and the search spends
/// itself proving that the registry refuses strangers.
///
/// So the peer usually matches the node the line claims to be, and
/// deliberately does not in a minority of steps. Both halves are needed: the
/// matching ones get the registry into a state worth attacking, and the
/// mismatched ones are the attack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Step {
    pub peer: Peer,
    pub line: String,
    /// How the line was built.
    ///
    /// Recorded because counting *refusals* does not establish that malformed
    /// input is being generated at all, and the first version of this search
    /// believed otherwise. `NONE`, `NO` and `FENCED` are ordinary answers to
    /// well-formed, authenticated requests — a poll when the actor is held, an
    /// acquire that was never offered, a write at a burned epoch. Deleting
    /// every malformed generation mode left the refusal count *higher* and the
    /// search green.
    ///
    /// So the floors are on how the step was made, not on what came back. A
    /// mode that stops being generated takes its counter to zero and fails.
    ///
    /// The limit of that is worth stating rather than leaving to be
    /// discovered: this is the *label*, so the floors catch a mode being
    /// removed and would not catch one hollowed out while the label stayed.
    pub shape: Shape,
    /// Whether the connection disagrees with the line about who is sending.
    ///
    /// Recorded for the same reason as `shape`, and separately from it,
    /// because the spoof is orthogonal to the syntax: a perfectly well-formed
    /// `WRITE 1 42` arriving on node 2's connection is the case the registry's
    /// believe-the-connection rule exists for. Deriving this from the
    /// registry's *obligations* instead would not hold: `BEGIN 1 99` is owed a
    /// refusal for naming a node that does not exist, on any connection at
    /// all, so a count of owed refusals stays comfortably positive with the
    /// spoof generation deleted outright.
    pub spoofed: bool,
}

/// How a generated line was built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    /// A syntactically valid request. Whether it is *permitted* is another
    /// question — the peer may be wrong and the fields may be nonsense.
    WellFormed,
    /// A valid request then broken: a field dropped, added, replaced with a
    /// non-number, the verb lowercased, the separators mangled, or the line
    /// truncated mid-token.
    Corrupted,
    /// Bytes with no structure at all.
    Junk,
    /// Nothing, which is what a short read looks like.
    Empty,
}

/// A run of arbitrary protocol lines against one registry.
///
/// Held as the words that generate the lines rather than as the lines
/// themselves, because one generation mode quotes the epoch the registry last
/// named and so cannot be resolved until the run reaches it. The run is still
/// entirely determined by the words, which is what keeps a seed replayable.
///
/// That mode is not a convenience. Without it the search measurably could not
/// get anywhere: over 1024 runs it reached 15 acquires, no writes, no releases
/// and no revokes, because reaching a write means quoting an epoch that
/// another step has usually just burned. A node that could not echo what it
/// was told would be a strange node, and a generator that could not was a
/// strange generator.
#[derive(Debug, Clone)]
pub struct ProtocolRun {
    pub seed: u64,
    pub words: Vec<[u64; 3]>,
}

/// What the registry last said, as far as the generator is concerned.
///
/// Not the registry's state — the generator cannot see that, and should not:
/// a generator that knew the state would only ever send requests that succeed,
/// which is the action alphabet again. This is what a *node* would know, which
/// is what it was last told.
#[derive(Debug, Default, Clone, Copy)]
struct Offered {
    node: Option<u64>,
    epoch: Option<u64>,
}

/// Values for a field that names a node.
///
/// Weighted towards real node ids, with `NODES`, 99 and `u64::MAX` present so
/// the off-the-end case is reached. One table for both fields was the first
/// version and it was measurably wrong: a node field drawn from a table
/// containing 40 through 44 is out of range most of the time, so most
/// well-formed requests were refused before they reached the guard under test.
/// The search reported 122 requests served against 17,871 refused, which its
/// own vacuity floor of 64 barely cleared.
const NODE_VALUES: [u64; 8] = [0, 0, 1, 1, 2, NODES, 99, u64::MAX];

/// Values for a field that names an epoch.
///
/// Clustered around `INITIAL_EPOCH`, because an epoch that is off by one is a
/// refusal worth reaching and an epoch of 3 is one the registry can dismiss
/// without consulting anything. The two largest `u64`s are here because an
/// epoch is a field that gets added to.
const EPOCH_VALUES: [u64; 9] =
    [40, 41, 41, 42, 42, 43, 44, u64::MAX - 1, u64::MAX];

/// The verbs the registry has, weighted.
///
/// Repeated entries rather than a uniform choice, and `FORCE` appears once in
/// fourteen for the same reason it does in `Action::from_pair`: it is the only
/// verb that succeeds from *any* state, so a uniform sixth of the steps
/// burning the epoch means no grant ever survives long enough to be acquired
/// and written at. Measured over 1024 runs, uniform choice reached 31 acquires
/// and 4 writes; the protocol's interesting states were all downstream of the
/// ones it was demolishing.
const VERBS: [&str; 14] = [
    "POLL", "POLL", "POLL", "ACQUIRE", "ACQUIRE", "ACQUIRE", "WRITE", "WRITE", "WRITE", "WRITE",
    "BEGIN", "RELEASE", "RELEASE", "FORCE",
];

/// Tokens that are not a `u64`, for the field-corruption case.
///
/// `1O24` is a capital O for a zero, which is the typo that motivated the
/// strict parse in the first place. `41.0` and `-1` parse as numbers in most
/// languages and not in this one. The empty string is what a doubled separator
/// leaves behind.
const NON_NUMBERS: [&str; 6] = ["x", "-1", "41.0", "1O24", "0x29", "١٤"];

impl Step {
    /// One step from three words, in the same spirit as `Action::from_pair`.
    ///
    /// The mode split is deliberate and load-bearing. A generator that emitted
    /// only junk would spend the whole run being refused at the parser and
    /// never reach a guard at all; one that emitted only well-formed lines
    /// would be the action alphabet again. Most steps are well formed so the
    /// registry advances, and a third of them are corrupted so the advance
    /// keeps meeting malformed input from a state that took work to reach.
    /// One step from three words and whatever the registry last offered.
    ///
    /// `offered` is the node the registry last dealt with and the epoch it
    /// last named, if any.
    ///
    /// The epoch comes only from a `GRANT` or a `REVOKE`: an `OK 3` is a
    /// write's sequence number, and quoting it as an epoch would be a
    /// generator that had confused the protocol's two numeric fields with each
    /// other. The node is whoever sent the request that was not refused,
    /// because the node the registry just answered is the node that would
    /// plausibly act next — which is a fact about the protocol, not a script.
    fn from_words(a: u64, b: u64, c: u64, offered: Offered) -> Self {
        let (line, shape) = match b % 16 {
            0..=8 => (well_formed(b / 16, c, offered), Shape::WellFormed),
            9..=13 => (corrupt(&well_formed(b / 16, c, offered), c / 13), Shape::Corrupted),
            14 => (junk(c), Shape::Junk),
            _ => (String::new(), Shape::Empty),
        };
        let peer = peer_for(&line, a);
        let spoofed = misdirected(&line, peer);
        Step { peer, line, shape, spoofed }
    }
}

/// Did this line arrive somewhere a correct node would not have sent it?
///
/// True only when the line names a sender that exists and the connection is
/// somebody else, or when it is a `FORCE` off the control path. A line whose
/// node field is missing or out of range is not counted: nothing correct
/// sends it on any connection, so calling it misdirected would let the
/// mangled shapes stand in for a spoof this search had stopped generating.
fn misdirected(line: &str, peer: Peer) -> bool {
    let mut parts = line.split_whitespace();
    match (parts.next(), parts.next().and_then(|f| f.parse::<u64>().ok())) {
        (Some("FORCE"), _) => peer != Peer::Control,
        (Some(_), Some(node)) if node < NODES => peer != Peer::Node(node),
        _ => false,
    }
}

/// What the registry owes a request, decided from the request and the
/// connection alone.
///
/// Two *independent* reasons, not a sequence. Which one the registry reports
/// when both apply is not a property worth pinning: the first version of this
/// pinned it and was immediately wrong about `FORCE 0 7` from an unknown
/// host, which `Coord::handle` refuses as unauthorised before it ever counts
/// the fields — and refusing unauthorised input before parsing it further is
/// the better order, not a defect. An obligation that encodes the handler's
/// sequence is an obligation fitted to the implementation, which is exactly
/// what this must not be.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Owed {
    /// An unknown verb, the wrong number of fields, or a field that is not a
    /// `u64`. Owed `ERR`.
    pub malformed: bool,
    /// Not something this peer may ask for, or naming a node that does not
    /// exist. Owed `NO`.
    pub not_permitted: bool,
}

impl Owed {
    pub fn owes_anything(self) -> bool {
        self.malformed || self.not_permitted
    }

    /// The exact reply owed, when only one reason applies. `None` when both
    /// do and any refusal will serve.
    pub fn exact(self) -> Option<&'static str> {
        match (self.malformed, self.not_permitted) {
            (true, false) => Some("ERR"),
            (false, true) => Some("NO"),
            _ => None,
        }
    }
}

/// The refusals the registry owes in *every* state.
///
/// This exists because the oracles cannot see the defect it catches. They
/// audit the audit log, and the log records what the registry *did*, never
/// what it was asked. So a request that should have been refused and was
/// accepted instead leaves a perfectly legal log: restore the old
/// `filter_map` parser and `POLL junk 0` executes as `POLL 0`, answering
/// `GRANT 41` and writing `Granted { node: 0, epoch: 41 }` — which satisfies
/// every invariant in `check_invariants`, because it *is* a thing the
/// registry is allowed to do. It was merely allowed to do it for the wrong
/// reason.
///
/// Measured rather than argued: with the parser regressed that way, this
/// search passed 20 000 seeds — over half a million requests — while the
/// single hand-written `the_registry_refuses_a_line_with_an_unparseable_field`
/// caught it immediately. A search strictly weaker than the test it was
/// written to generalise is not much of a search.
///
/// Only *unconditional* refusals belong here. Whether `ACQUIRE 0 41` should
/// succeed depends on the registry's state and is the oracles' business; that
/// `POLL junk 0` must be refused depends on nothing at all.
pub fn owed_for(line: &str, peer: Peer) -> Owed {
    let mut owed = Owed::default();
    let mut parts = line.split_whitespace();
    let verb = parts.next().unwrap_or("");
    let fields: Vec<&str> = parts.collect();

    // Each field on its own terms, rather than all of them or none.
    //
    // This is the third time the same mistake has been caught here, each time
    // one field further out, so it is worth stating as the rule instead of as
    // another case: **a permission check uses its own field's parse result,
    // never the whole line's.** An all-or-nothing parse makes one illegible
    // field hide every authority fact the others carry — `BEGIN junk 99` names
    // a successor that does not exist, and `FORCE 99 junk` does too, and both
    // were recorded as owing `ERR` and nothing else.
    let field = |i: usize| fields.get(i).and_then(|f| f.parse::<u64>().ok());

    let arity = match verb {
        "POLL" | "FORCE" => Some(1),
        "ACQUIRE" | "WRITE" | "BEGIN" | "RELEASE" => Some(2),
        _ => None,
    };

    // Authority first, from whatever is legible, and *before* the line is
    // judged well formed. The two reasons are independent, so every one that
    // can be established has to be — an obligation that drops a reason it
    // could have known demands one exact refusal where two are defensible,
    // and then reports a sound handler as defective for choosing the other.
    //
    // Both halves of this were got wrong once, and found rather than reasoned
    // out. `FORCE 41.0` from a node is unparseable *and* unauthorised, and
    // the first version decided the fields first, so it demanded `ERR` from a
    // registry that quite reasonably refuses strangers before parsing their
    // input. The fix covered `FORCE` and stopped there, one case short of the
    // rule: `WRITE 0 junk` on the control connection is the same shape,
    // because the *sender* field is legible even though the epoch is not, so
    // `NO` is as defensible as `ERR`.
    if verb == "FORCE" {
        // The registry's own verb. No node may send it, whatever the line
        // claims and whatever else is wrong with it — knowable without
        // reading a field at all.
        if peer != Peer::Control {
            owed.not_permitted = true;
        }
        // And the successor it names has to be a node that exists, on any
        // connection, whatever became of the fields after it.
        if field(0).is_some_and(|next| next >= NODES) {
            owed.not_permitted = true;
        }
    } else if arity.is_some() {
        // Every other known verb names its sender in its first field, and the
        // registry believes the connection rather than the field.
        //
        // Only for a verb the protocol *has*: it has no opinion about who may
        // send a request it does not recognise, so an unknown verb is
        // malformed and nothing else.
        if let Some(claimed) = field(0) {
            if peer != Peer::Node(claimed) {
                owed.not_permitted = true;
            }
        }
        // A handover's successor has to exist too, read from its own field.
        if verb == "BEGIN" && field(1).is_some_and(|to| to >= NODES) {
            owed.not_permitted = true;
        }
    }

    // Then whether the line is well formed at all: a verb the protocol has —
    // which the empty line and the wrong case are not — the right number of
    // fields, and every one of them a `u64`. That last is the rule the strict
    // parse replaced `filter_map` to enforce, stated independently of it.
    let Some(n) = arity else {
        owed.malformed = true;
        return owed;
    };
    if fields.len() != n || fields.iter().any(|f| f.parse::<u64>().is_err()) {
        owed.malformed = true;
    }

    owed
}

/// Who the line arrives from.
///
/// Three cases in seven. Most often the connection matches what the line
/// claims, because that is the only way the run gets anywhere; `FORCE` is
/// answered only on the control path, so a plausible `FORCE` comes from there;
/// and the rest is an arbitrary peer, which is where the spoof lives.
fn peer_for(line: &str, choice: u64) -> Peer {
    let arbitrary = match (choice / 7) % 5 {
        0..=2 => Peer::Node((choice / 35) % NODES),
        3 => Peer::Control,
        _ => Peer::Unknown,
    };
    if choice % 7 >= 5 {
        return arbitrary;
    }
    let mut parts = line.split_whitespace();
    match (parts.next(), parts.next().and_then(|f| f.parse::<u64>().ok())) {
        (Some("FORCE"), _) => Peer::Control,
        (Some(_), Some(node)) if node < NODES => Peer::Node(node),
        _ => arbitrary,
    }
}

/// A syntactically valid request. Whether the registry accepts it is its own
/// business — the arguments come from `FIELD_VALUES` and are often wrong.
fn well_formed(choice: u64, fields: u64, offered: Offered) -> String {
    let verb = VERBS[(choice % VERBS.len() as u64) as usize];
    // Mostly whoever the registry last answered. Drawing the node freshly each
    // time was measurably why the transfer path was never reached: a handover
    // is five consecutive steps at *one* node, and an independent draw put the
    // right node there one time in eight.
    let node = match offered.node {
        Some(n) if fields % 4 != 0 => n,
        _ => NODE_VALUES[(fields % NODE_VALUES.len() as u64) as usize],
    };
    match verb {
        // `FORCE`'s one argument is the successor, which is a node.
        "POLL" | "FORCE" => format!("{verb} {node}"),
        // `BEGIN`'s second argument is a node too, not an epoch. It usually
        // differs from the sender, because `tr_begin_transfer` requires that
        // and a handover refused for naming itself teaches the search nothing
        // about the transfer path beyond it. The collision is still reachable
        // — `the_registry_refuses_a_handover_to_the_owner_itself` is a guard,
        // and a guard nothing sends at is a guard nothing checks.
        "BEGIN" => {
            let pick = (fields / 8) % NODE_VALUES.len() as u64;
            let to = if (fields / 8) % 5 == 0 {
                NODE_VALUES[pick as usize]
            } else {
                // `node % NODES` first. Without it this overflowed on the very
                // first run of the search, because `NODE_VALUES` contains
                // `u64::MAX` precisely so that the off-the-end case is
                // reached, and `u64::MAX + 1` is a panic in a debug build. The
                // analogous line in `Action::from_pair` is safe only because
                // its `from` was already reduced.
                (node % NODES + 1 + pick % (NODES - 1)) % NODES
            };
            format!("{verb} {node} {to}")
        }
        _ => {
            // Mostly the epoch the registry last named, because that is what a
            // node would quote and the only way a run reaches a write. The
            // table is still drawn from a third of the time, which is where
            // the stale and impossible epochs come from — and those are half
            // the point, since the fence exists for exactly them.
            let epoch = match offered.epoch {
                Some(e) if (fields / 8) % 3 != 0 => e,
                _ => EPOCH_VALUES[((fields / 8) % EPOCH_VALUES.len() as u64) as usize],
            };
            format!("{verb} {node} {epoch}")
        }
    }
}

/// Break a valid line in one of the ways a real one breaks.
fn corrupt(line: &str, how: u64) -> String {
    let mut parts: Vec<String> = line.split(' ').map(str::to_string).collect();
    match how % 8 {
        // A field short. `filter_map` used to turn this into a shorter valid
        // request rather than an error, which is the defect the strict parse
        // replaced.
        0 => {
            parts.pop();
            parts.join(" ")
        }
        // A field long.
        1 => {
            parts.push("7".to_string());
            parts.join(" ")
        }
        // A field that is not a number. Placed at a varying position, because
        // the first version of the parser dropped what it could not read and
        // so cared very much which field it was.
        2 => {
            if parts.len() > 1 {
                let at = 1 + (how / 8) as usize % (parts.len() - 1);
                parts[at] = NON_NUMBERS[(how / 8) as usize % NON_NUMBERS.len()].to_string();
            }
            parts.join(" ")
        }
        // Wrong case. The verb match is exact, and a reader could reasonably
        // assume otherwise.
        3 => line.to_lowercase(),
        // Padded. `split_whitespace` should absorb this; that it does is worth
        // a search knowing rather than a comment claiming.
        4 => format!("   {line}  "),
        // Tabs and doubled spaces instead of single ones.
        5 => parts.join("\t\t"),
        // A *surplus* non-number, inserted rather than substituted, leaving
        // every real field in place.
        //
        // This is the one shape the old `filter_map` parser turned back into a
        // valid request. It dropped the field it could not read, so `POLL junk
        // 0` arrived as `POLL 0`, with the right arity, and executed. Every
        // other corruption above changes the field *count*, which that parser
        // rejected by accident — so without this mode the strict parse could
        // be reverted and this search would not object. It was not objecting:
        // measured over 20 000 seeds with the parser regressed, the run was
        // green.
        6 => {
            let at = 1 + (how / 8) as usize % parts.len();
            parts.insert(at, NON_NUMBERS[(how / 8) as usize % NON_NUMBERS.len()].to_string());
            parts.join(" ")
        }
        // Truncated mid-token, which is what a short read looks like.
        _ => {
            let keep = line.len().saturating_sub(1 + (how / 8) as usize % 4);
            line.chars().take(keep).collect()
        }
    }
}

/// Bytes with no structure at all.
fn junk(seed: u64) -> String {
    let mut rng = Lcg::new(seed);
    let len = (seed % 12) as usize;
    (0..len)
        .map(|_| char::from_u32((rng.next() % 0x7f) as u32).unwrap_or('?'))
        .collect()
}

impl ProtocolRun {
    /// Build one from a seed, so a finding can be reported as a number.
    pub fn from_seed(seed: u64) -> Self {
        let mut rng = Lcg::new(seed);
        // Longer than a scenario, because these runs cost microseconds rather
        // than simulated seconds and a handover needs several steps to line up.
        let len = 8 + (rng.next() % 40) as usize;
        let words = (0..len).map(|_| [rng.next(), rng.next(), rng.next()]).collect();
        ProtocolRun { seed, words }
    }

    /// Build one from an arbitrary byte string, for a coverage-guided fuzzer.
    ///
    /// Three bytes a step, and no header: unlike `Scenario::from_bytes` there
    /// is no network schedule to seed, because nothing here is simulated. The
    /// registry is driven directly, which is also why this half of the search
    /// runs in milliseconds where the scenario walk takes half a minute.
    pub fn from_bytes(data: &[u8]) -> Option<Self> {
        let words: Vec<[u64; 3]> = data
            .chunks_exact(3)
            .take(MAX_STEPS)
            .map(|w| [w[0] as u64, w[1] as u64, w[2] as u64])
            .collect();
        if words.is_empty() {
            return None;
        }
        Some(ProtocolRun { seed: 0, words })
    }
}

/// How long a generated run may get.
const MAX_STEPS: usize = 64;

/// What the registry did with a run of lines.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Served {
    /// Requests the registry acted on rather than refused.
    ///
    /// The vacuity measure for this search, and it needs one badly: a
    /// generator that produced nothing but garbage would be refused at the
    /// parser every time, satisfy every oracle trivially and reach no guard at
    /// all. Counting refusals would not notice. Counting what got through
    /// does.
    pub accepted: usize,
    /// Requests refused — `NO`, `ERR` or `FENCED`.
    pub refused: usize,
    /// Writes the registry accepted.
    ///
    /// Counted separately from `accepted` because the two can move in
    /// opposite directions, and the difference is where this search earns its
    /// keep. A regression that made every `ACQUIRE` fail would leave
    /// `accepted` almost unchanged — polls still succeed — while the run
    /// stopped reaching the fence, the capability check and everything else
    /// downstream of holding the actor. A write is the deepest state a run can
    /// reach, so it is the one worth a floor.
    pub writes: usize,
    /// Steps generated as each shape, and steps whose connection did not
    /// match what the line claimed.
    ///
    /// Floors go on these rather than on refusals, because a refusal does not
    /// mean the request was malformed. See `Step::shape` and `Step::spoofed`.
    pub corrupted: usize,
    pub junk: usize,
    pub empty: usize,
    pub spoofed: usize,
    /// Requests the registry was obliged to refuse in any state, and did.
    ///
    /// Reported so a reader can see the obligation check is doing work rather
    /// than being vacuously satisfied by a search that never generates an
    /// unconditionally-refusable request.
    pub owed_refusals: usize,
    /// Handovers the registry completed.
    ///
    /// Reported and deliberately **not** asserted on. Measured over the
    /// default window it lands at 5 runs in 1024: reaching it needs
    /// `POLL → ACQUIRE → BEGIN → POLL → RELEASE` to line up at one node with
    /// nothing burning the epoch in between, and a random walk finds that
    /// rarely. A floor on a rate that low would be a flaky test rather than an
    /// informative one — so this is stated as a thin spot rather than dressed
    /// up as coverage. Claim 4's oracle is exercised properly by the scenario
    /// walk and by named stories; here it is barely exercised at all.
    pub transfers: usize,
}

/// Drive one registry with a run of arbitrary lines.
///
/// The oracles are checked after *every* step rather than once at the end, for
/// two reasons. A log that violates an invariant and is then repaired by a
/// later burn would pass an end-of-run check, and naming the step that broke
/// it is most of the value of a finding. Runs are at most 64 steps, so the
/// quadratic cost is nothing.
pub fn run_protocol(run: &ProtocolRun) -> Result<Served, String> {
    let mut coord = Coord::new(Fence::Checked);
    let mut served = Served::default();
    let mut offered = Offered::default();
    for (i, w) in run.words.iter().enumerate() {
        let step = Step::from_words(w[0], w[1], w[2], offered);
        let reply = coord.handle(&step.line, step.peer);
        offered = note_reply(offered, &step.line, &reply);
        match step.shape {
            Shape::WellFormed => {}
            Shape::Corrupted => served.corrupted += 1,
            Shape::Junk => served.junk += 1,
            Shape::Empty => served.empty += 1,
        }
        if step.spoofed {
            served.spoofed += 1;
        }
        if !is_a_reply_to(&step.line, &reply) {
            return Err(format!(
                "step {i}: `{}` from {:?} was answered `{reply}`, which is not \
                 a reply that request can have",
                step.line, step.peer
            ));
        }
        // The obligation check. This is the half the oracles cannot do: they
        // read the log, and the log does not record what was asked.
        let owed = owed_for(&step.line, step.peer);
        if owed.owes_anything() {
            served.owed_refusals += 1;
            match owed.exact() {
                Some(wanted) if reply != wanted => {
                    return Err(format!(
                        "step {i}: `{}` from {:?} must be refused `{wanted}` in \
                         every state, and was answered `{reply}`",
                        step.line, step.peer
                    ));
                }
                None if !matches!(reply.as_str(), "NO" | "ERR") => {
                    return Err(format!(
                        "step {i}: `{}` from {:?} is both malformed and not \
                         permitted, so it must be refused in every state, and \
                         was answered `{reply}`",
                        step.line, step.peer
                    ));
                }
                _ => {}
            }
        }
        if matches!(reply.as_str(), "NO" | "ERR" | "FENCED" | "NONE") {
            served.refused += 1;
        } else {
            served.accepted += 1;
        }
        check_invariants(coord.log()).map_err(|e| {
            format!(
                "after step {i} (`{}` from {:?}, answered `{reply}`): {e}",
                step.line, step.peer
            )
        })?;
    }
    served.writes = coord
        .log()
        .iter()
        .filter(|e| matches!(e, Event::Wrote { .. }))
        .count();
    served.transfers = coord
        .log()
        .iter()
        .filter(|e| matches!(e, Event::Released { .. }))
        .count();
    Ok(served)
}

/// Update what the generator knows from one exchange.
///
/// A refusal teaches a node nothing, so it leaves this untouched: `NO` does
/// not say who the registry thinks the owner is, and pretending otherwise
/// would give the generator information the protocol never sends.
fn note_reply(prev: Offered, line: &str, reply: &str) -> Offered {
    if matches!(reply, "NO" | "ERR" | "FENCED" | "NONE") {
        return prev;
    }
    let claimed = line.split_whitespace().nth(1).and_then(|f| f.parse::<u64>().ok());
    Offered {
        node: claimed.filter(|n| *n < NODES).or(prev.node),
        epoch: epoch_named_by(reply).or(prev.epoch),
    }
}

/// The epoch a reply names, if it names one.
///
/// `GRANT` and `REVOKE` carry an epoch. `OK 3` carries a write's sequence
/// number, which is a different quantity that happens to be a `u64`, and
/// reading it as an epoch would be the same category error the protocol's two
/// numeric fields invite everywhere else.
fn epoch_named_by(reply: &str) -> Option<u64> {
    let mut parts = reply.split(' ');
    match (parts.next(), parts.next()) {
        (Some("GRANT" | "REVOKE"), Some(n)) => n.parse().ok(),
        _ => None,
    }
}

/// Replay a run and hand back the audit log, for coverage measurement.
pub fn replay_protocol(run: &ProtocolRun) -> Vec<Event> {
    let mut coord = Coord::new(Fence::Checked);
    let mut offered = Offered::default();
    for w in &run.words {
        let step = Step::from_words(w[0], w[1], w[2], offered);
        let reply = coord.handle(&step.line, step.peer);
        offered = note_reply(offered, &step.line, &reply);
    }
    coord.log().to_vec()
}

/// Every reply the registry may give **to this request**.
///
/// Per verb, not a flat set, and the difference is not cosmetic. A flat set
/// accepts any protocol token for any request, and a wrong-vocabulary refusal
/// changes nothing a log-reading oracle can see — the log is *unchanged*,
/// which is exactly what a refusal is supposed to leave behind. Measured
/// rather than argued: with a refused `RELEASE` answered `FENCED`, and again
/// with a refused `ACQUIRE` answered `NONE`, this search passed 20 000 seeds
/// apiece while the registry spoke a protocol no node parses.
///
/// The vocabulary is read off what each request *asks*, not off the handler's
/// branches:
///
/// * A poll asks what is on offer, so it is answered with a grant, a
///   revocation, or nothing at all.
/// * A write either lands — carrying the sequence number it landed at, which
///   is what makes the log auditable — or is stopped by the fence.
/// * Everything else either takes effect or does not.
///
/// Refusals are the exception and are universal: `NO` and `ERR` are available
/// to every request, including one whose verb the protocol does not have.
/// *When* a refusal is owed is `owed_for`'s business; this says only which
/// words may carry one.
pub fn is_a_reply_to(line: &str, reply: &str) -> bool {
    if matches!(reply, "NO" | "ERR") {
        return true;
    }
    let verb = line.split_whitespace().next().unwrap_or("");
    let mut parts = reply.split(' ');
    match (verb, parts.next(), parts.next(), parts.next()) {
        ("POLL", Some("GRANT" | "REVOKE"), Some(n), None) => n.parse::<u64>().is_ok(),
        ("POLL", Some("NONE"), None, None) => true,
        ("WRITE", Some("OK"), Some(n), None) => n.parse::<u64>().is_ok(),
        ("WRITE", Some("FENCED"), None, None) => true,
        ("ACQUIRE" | "BEGIN" | "RELEASE" | "FORCE", Some("OK"), None, None) => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Reading a search window from the environment
// ---------------------------------------------------------------------------
//
// Shared rather than copied, for the reason stated at the top of both search
// files: a second copy of a rule is a second place for it to be wrong, and
// every one of these four functions exists because the first version of that
// rule was wrong somewhere. They are pure — no environment is touched except
// by `env_u64` — so the tests that pin them live in the search files that use
// them and run on the real toolchain.

/// Read a `u64` from the environment, or fall back if it is not set.
///
/// A value that is present and unparsable is a failure, not a fallback. The
/// comment here used to argue the opposite — that a nightly job dying on a typo
/// in its own workflow finds nothing at all — which is true and beside the
/// point: falling back to zero *also* finds nothing, and does it while
/// reporting success. A typo in `JETSTREAM_SCENARIO_START` would re-run the
/// default window every night, green forever, discovering exactly what the
/// previous night discovered.
///
/// Absent is different from wrong. Absent means "no preference" and takes the
/// default; wrong means somebody tried to say something and it did not arrive.
pub fn env_u64(name: &str, fallback: u64) -> u64 {
    window_bound(name, std::env::var(name), fallback)
}

/// The decision `env_u64` makes, separated from the process environment that
/// supplies it.
///
/// Split out so it can be tested. Environment variables are process-global and
/// this binary runs its tests on threads of one process, so a test that set
/// `JETSTREAM_SCENARIO_START` to something bad would be setting it for the
/// search running alongside it. Taking the `Result` as an argument is how the
/// rule gets checked without the test and the thing it tests sharing state.
pub fn window_bound(name: &str, raw: Result<String, std::env::VarError>, fallback: u64) -> u64 {
    use std::env::VarError;
    match raw {
        Err(VarError::NotPresent) => fallback,
        // Matching `Err(_)` here would have folded this case in with absent,
        // which is the exact defect the doc comment above is about: the
        // variable *is* set, somebody did try to say something, and it did not
        // arrive. Bytes that are not UTF-8 are a wrong value, not a missing
        // one.
        Err(VarError::NotUnicode(bytes)) => panic!(
            "{name} is set to {bytes:?}, which is not valid UTF-8 and so cannot \
             be a u64. Refusing to fall back to {fallback}: the variable is \
             set, so somebody meant something by it."
        ),
        Ok(raw) => raw.trim().parse().unwrap_or_else(|_| {
            panic!(
                "{name} is set to `{raw}`, which is not a u64. Refusing to fall \
                 back to {fallback}: a search that silently runs the wrong \
                 window is worse than one that stops, because it keeps \
                 reporting success."
            )
        }),
    }
}

/// The end of the window, or a failure if there isn't one.
///
/// This was `start.saturating_add(seeds)`, which is the arithmetic version of
/// the `Err(_)` above: it turns a request the program cannot honour into a
/// quietly different request it can. At the `u64` boundary the clamp shortens
/// the window — at `u64::MAX` it empties it — and a window under
/// `FLOOR_WINDOW` skips the coverage floor entirely. So a job asking for 256
/// seeds would run none of them, apply no floor, and report success.
///
/// The doc comment on `env_u64` already states the rule this broke: a search
/// that silently runs the wrong window is worse than one that stops, because
/// it keeps reporting success. Saturating is silently running the wrong
/// window.
pub fn window_end(start: u64, seeds: u64) -> u64 {
    start.checked_add(seeds).unwrap_or_else(|| {
        panic!(
            "a window of {seeds} seeds starting at {start} runs past u64::MAX. \
             Refusing to search a truncated one: the shortened window would \
             fall under the coverage floor and be exempted from it, so the \
             run would report success having searched almost nothing."
        )
    })
}

/// The shortest window the coverage floor is applied to.
pub const FLOOR_WINDOW: u64 = 32;

/// How many accepted writes a window of this size must beat, or `None` if it
/// is too short for a rate to mean anything.
///
/// An empty window is neither, and the distinction is the whole reason this is
/// a function. Zero seeds is not a short window that the floor politely
/// declines to judge; it is no search at all, and the exemption was swallowing
/// it — `JETSTREAM_SCENARIO_SEEDS=0` ran nothing, asserted nothing and
/// reported success.
///
/// I had already fixed exactly this failure one commit earlier, in
/// `window_end`, and looked straight at this case while doing it. The
/// reasoning for leaving it was that the run announces itself in the log, so
/// the emptiness is visible. That is the same argument the overflow case
/// makes — it also prints `searching scenario seeds X..X` — and I rejected it
/// there. A log line is not an exit status. Two standards for one failure
/// mode, four lines apart.
pub fn coverage_floor(window: u64) -> Option<u64> {
    assert!(
        window != 0,
        "a window of zero seeds searches nothing. Refusing to report success \
         on it: the short-window exemption below is for a window too small to \
         have a rate, not for one with nothing in it."
    );
    if window < FLOOR_WINDOW {
        return None;
    }
    Some(window / 16)
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
    run_inner(scenario, Fence::Checked)
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
    let attempts = run_with_log(scenario, Fence::Checked, captured)?;
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
    let _ = run_with_log(scenario, Fence::Never, captured)?;
    let out = log.lock().unwrap().clone();
    Ok(out)
}

/// The same scenario with the coordinator's fence jammed on: every write is
/// refused, including the current owner's at its own epoch.
///
/// The mirror of [`run_scenario_unfenced`], and it exists because the two
/// failures are not symmetric in the oracles. Disabling the fence breaks
/// claims 2/3, which seven oracles are watching for. Jamming it on breaks none
/// of them — it accepts no bad write because it accepts no write — so until
/// `may_mutate (refusals)` was written, this registry passed the entire suite.
///
/// That is the same standard `run_scenario_unfenced` was written to meet: a
/// hand-built log proves an oracle rejects a string of events, and this proves
/// it rejects a *registry*.
pub fn run_scenario_overfenced(scenario: Scenario) -> turmoil::Result<Vec<Event>> {
    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = log.clone();
    let _ = run_with_log(scenario, Fence::Always, captured)?;
    let out = log.lock().unwrap().clone();
    Ok(out)
}

fn run_inner(scenario: Scenario, fence: Fence) -> turmoil::Result<usize> {
    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = log.clone();
    let _ = run_with_log(scenario, fence, captured)?;
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
    fence: Fence,
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
    let coord = Arc::new(Mutex::new(Coord::new(fence)));
    let coord_for_host = coord.clone();
    sim.host("coord", move || {
        let coord = coord_for_host.clone();
        async move {
            let listener =
                TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, peer) = listener.accept().await?;
                let peer_id = peer_of(peer.ip());
                let coord = coord.clone();
                tokio::spawn(async move {
                    let mut reader = BufReader::new(stream);
                    let mut line = String::new();
                    // Same defect as `rpc_inner`, and with more to lose. A
                    // clean EOF is `Ok(0)`, which is not an error, so an empty
                    // `line` went on to be handled as a request: `handle("")`
                    // answers `ERR` harmlessly, but the same block calls
                    // `take_slow_reply`, which is one-shot. A severed
                    // connection could therefore burn the flag that
                    // `Action::SlowReply` had armed, and the story about a
                    // reply arriving after its caller gave up would quietly
                    // get a prompt one instead.
                    match reader.read_line(&mut line).await {
                        Ok(n) if n > 0 && line.ends_with('\n') => {}
                        _ => return,
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
                        let reply = guard.handle(line.trim(), peer_id);
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
    sim.client(CONTROL_HOST, async move {
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
async fn poll(node: u64, state: &mut NodeState) -> Result<(), RpcFailure> {
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
async fn run_cmd(
    node: u64,
    cmd: NodeCmd,
    state: &mut NodeState,
) -> Result<(), RpcFailure> {
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
                    Err(RpcFailure::TimedOut) => state.attempts.writes_timed_out += 1,
                    Err(RpcFailure::Disconnected) => {
                        state.attempts.writes_disconnected += 1;
                    }
                    Err(RpcFailure::NoRoute) => state.attempts.writes_failed += 1,
                    // Counted with the disconnects rather than with the
                    // no-route failures, which is where it used to land. A
                    // send that fails partway leaves the same question open as
                    // a reply that never arrives: the coordinator may have the
                    // request. Only `NoRoute` settles it.
                    Err(RpcFailure::Cut) => state.attempts.writes_disconnected += 1,
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
