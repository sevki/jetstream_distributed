//! The distributed-ownership protocol, as a Jetstream service.
//!
//! The repository's premise is verified Jetstream services. Until now it held
//! the verified half and no service: `src/` is a Verus model of exclusive
//! ownership with epoch fencing, and the coordinator that the simulation suite
//! attacks is a hand-written stand-in in `tests/`, speaking a bespoke line
//! protocol over raw TCP. It exists to be shot at, not to be run. This crate is
//! the other half.
//!
//! # What the service form buys, structurally
//!
//! The line protocol carried the sender as a *field*: `WRITE 0 41` claims to be
//! node 0. So the registry had to be told, in prose and then in a guard, to
//! believe the connection rather than the claim — and the search suite spent
//! four rounds of review hardening that one rule, because every request had to
//! restate it and every restatement was a place to get it wrong.
//!
//! Here there is no such field. No method takes a node number. Who is calling
//! is [`Context`], which the transport fills in and the caller cannot forge, so
//! the entire class of "the line lied about who sent it" is not guarded against
//! — it is unrepresentable.
//!
//! `force` is likewise absent from the trait. It is the coordinator's own
//! transition (`tr_revoke_owner`), and the line protocol needed a dedicated
//! control connection to stop a node sending it. A node-facing service simply
//! does not offer it: see [`Registry::force`], an inherent method on the
//! implementation and not on the wire.
//!
//! # The assumption this rests on, stated
//!
//! [`Context::peer`] is the authenticated identity, and it is `None` over plain
//! TCP — jetstream's own comment says so: *"A plain TCP stream authenticates
//! nothing."* The authenticated forms are a TLS certificate (`x509` feature) or
//! an iroh `NodeId`, and `NodeId`'s inner value is private with no accessor
//! outside `jetstream_rpc`, so neither is usable here yet.
//!
//! So this service identifies a caller by [`Context::remote`] — its address —
//! against a roster fixed at construction. **An address is not a credential.**
//! In the simulated network it is as good as one, because turmoil assigns each
//! host its own address and nothing can spoof it; on a real network it is worth
//! very little. This is an explicit, documented part of the system model rather
//! than something the code quietly assumes, and it is the first thing that
//! should be replaced with TLS identity. What does *not* change when it is
//! replaced is the shape: identity arrives with the connection, never in an
//! argument.
//!
//! # The other assumption, and why it needed code rather than a caveat
//!
//! `System::actors` — the model's registry — is read and written in a single
//! step by every epoch-advancing transition. The README calls that the
//! strongest assumption in the model, and it is really two assumptions wearing
//! one name: the record is updated **atomically**, and it **survives**. A
//! process-local `Mutex` buys the first and none of the second.
//!
//! A registry that forgets can move epochs *backwards*, and every fencing
//! theorem in `distributed_ownership::proofs` assumes they only go up. Say A
//! owns the actor at 41, a handover moves it to 42, and A is partitioned away
//! still believing it owns at 41. Restart a registry that begins wherever its
//! caller says, and it offers 41 again — to A or to anyone. A's stale write now
//! passes [`FenceGuard::accepts`], because 41 is current once more. Nothing was
//! violated; the fence was simply asked about a world that had been rewound.
//!
//! So the starting epoch is no longer a number from the caller. It is read from
//! an [`EpochFloor`]: a durable, monotone record of the highest epoch this
//! registry has ever used. `new` starts strictly above it and writes that down
//! before serving anything, and every later burn is written down *before* the
//! state that depends on it becomes visible. A registry that dies between the
//! two skips an epoch, which is the safe direction to fail — epochs must not
//! repeat, and nothing requires them to be consecutive.
//!
//! What this still does **not** buy is atomicity between two registries. Two
//! processes sharing a [`FileFloor`] would both read it, both raise it, and
//! both believe they had allocated the next epoch. Durability and atomicity
//! want to come from the same place, which is why a real deployment keeps the
//! ownership record in a store with compare-and-swap rather than bolting a
//! counter onto a local file.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write as _};
use std::net::IpAddr;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use distributed_ownership::exec::FenceGuard;
use jetstream::prelude::*;
// Not in the prelude's re-export list, and `jetstream_rpc` is not a direct
// dependency of this crate — so it comes through the `pub extern crate` the
// prelude publishes rather than as a top-level path.
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;

/// What a poll is answered with: the three things the registry can have to say
/// about a node's standing.
///
/// This is an ordinary reply, not an error. A node with nothing on offer has
/// asked a reasonable question and got a truthful answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub enum Offer {
    /// Nothing is on offer for this node.
    Nothing,
    /// The actor is offered at this epoch; `acquire` will take it.
    Grant(u64),
    /// The actor is being taken away; `release` at this epoch acknowledges.
    Revoke(u64),
}

/// The node-facing protocol.
///
/// Six transitions in the model, five methods here, and no method takes a node
/// number — see the module docs. The sixth, `tr_revoke_owner`, is the
/// coordinator's and is not on the wire.
#[service(uses(super::{Offer}))]
pub trait Ownership {
    /// What is on offer for the caller?
    async fn poll(&self, ctx: Context) -> Result<Offer>;

    /// `tr_acquire`: take an offered grant at exactly the epoch it was offered.
    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()>;

    /// `can_mutate`: write as the current owner, returning the sequence number
    /// the write landed at.
    ///
    /// The sequence number is what makes the audit log checkable after the
    /// fact, so it is part of the reply rather than something the caller has to
    /// infer.
    async fn write(&self, ctx: Context, epoch: u64) -> Result<u64>;

    /// `tr_begin_transfer`: the owner agrees to hand the actor to `to`.
    ///
    /// Agreeing is an action *by* the owner, which is why this is a call the
    /// owner makes rather than something done to it.
    async fn begin_transfer(&self, ctx: Context, to: u64) -> Result<()>;

    /// `tr_complete_release`: the outgoing owner acknowledges the revocation,
    /// naming the transfer's new epoch.
    ///
    /// The epoch is carried rather than inferred. Without it a release delayed
    /// on the wire, or replayed, would complete a *later* handover by the same
    /// node.
    async fn release(&self, ctx: Context, epoch: u64) -> Result<()>;
}

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------
//
// The line protocol answered `NO`, `ERR` and `FENCED`, and the search suite in
// `tests/` is built on that alphabet: `owed_for` says which refusal is owed,
// `is_a_reply_to` says which words a request may be refused in, and
// `agrees_with_log` says the reply and the audit log must describe the same
// thing happening.
//
// Those codes are carried over deliberately, as `Error` codes rather than as
// bare strings on a socket. Keeping the alphabet means the oracles port to this
// service instead of being rewritten for it — and an oracle rewritten to suit
// the thing it audits is worth much less than one that survived the move.

/// Not something this caller may ask for, in this state.
fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

/// The request is not one the protocol has, or names something that does not
/// exist.
fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

/// The epoch cannot be burned again without wrapping.
///
/// The model counts epochs in `nat`, which does not run out; this
/// implementation counts them in `u64`, which does. That gap is the
/// implementation's to close, and the only safe way to close it is to refuse:
/// wrapping would take the epoch *backwards*, which is precisely the ordering
/// every fencing proof in `src/proofs` rests on. It is unreachable in any real
/// run — a registry would have to burn an epoch every nanosecond for six
/// hundred years — but a registry starts one above whatever its
/// [`EpochFloor`] remembers, so a floor seeded at `u64::MAX` reaches it in a
/// test, and a panic in debug or a silent wrap in release are both worse than a
/// refusal.
fn exhausted() -> Error {
    Error::new("the epoch space is exhausted").set_code("NO")
}

/// The fence stopped it: the caller is not the current owner at the current
/// epoch.
fn refuse_fenced(what: &str) -> Error {
    Error::new(what).set_code("FENCED")
}

/// The registry could not make a decision durable, so it did not make it.
///
/// **Deliberately outside the line protocol's alphabet.** `NO`, `ERR` and
/// `FENCED` all say the protocol looked at the request and declined it, and an
/// auditor reading them learns something about the actor's state. This says
/// nothing about the actor at all: the request may have been perfectly legal
/// and the registry still could not answer it, because writing the new epoch
/// down failed. The line protocol had no word for this because its registry
/// could not fail — it was a `HashMap` in the test binary.
///
/// Giving it its own code keeps `owed_for` honest. An oracle that had to read
/// this as `NO` would be told a guard was false when no guard was evaluated.
fn refuse_down(what: &str) -> Error {
    Error::new(what).set_code("DOWN")
}

// ---------------------------------------------------------------------------
// The durable epoch floor
// ---------------------------------------------------------------------------

/// A durable, monotone record of the highest epoch a registry has ever used.
///
/// This is the half of the model's atomic-registry assumption that a `Mutex`
/// cannot supply — see the module docs. The contract is short and all of it is
/// load-bearing:
///
/// * [`read`](EpochFloor::read) returns the highest epoch ever recorded, or `0`
///   if nothing ever was. `0` is therefore not usable as an epoch, which costs
///   nothing: the first epoch a registry serves is `read() + 1`.
/// * [`record`](EpochFloor::record) must not return until the value is durable,
///   and must never lower what is stored. Recording an epoch below the current
///   floor is a no-op, not an error — the floor is a high-water mark.
///
/// An implementation that returns `Ok(())` before the value is durable
/// satisfies the type and breaks the protocol, which is the usual shape of this
/// kind of interface. It is stated here rather than left to be inferred.
pub trait EpochFloor: Send + Sync + 'static {
    /// The highest epoch ever recorded, or `0` if none.
    fn read(&self) -> io::Result<u64>;

    /// Raise the floor to at least `epoch`, durably.
    fn record(&self, epoch: u64) -> io::Result<()>;
}

/// A floor that survives the [`Registry`] but not the process.
///
/// This is what the tests use, and it is honest about what it demonstrates: a
/// restart of the *registry* against a floor that remembers. A restart of the
/// machine is [`FileFloor`]'s business. The distinction matters because the
/// defect being guarded against is a registry that comes back not knowing where
/// it was, and that is reproducible without killing a process.
///
/// `fetch_max` rather than a load-then-store: monotonicity by construction
/// rather than by a check that two threads can interleave around.
#[derive(Clone, Debug, Default)]
pub struct MemoryFloor(Arc<AtomicU64>);

impl MemoryFloor {
    /// A floor that has never recorded anything.
    pub fn new() -> Self {
        MemoryFloor(Arc::new(AtomicU64::new(0)))
    }

    /// A floor that already remembers `epoch`, so the next registry to read it
    /// starts at `epoch + 1`.
    pub fn at(epoch: u64) -> Self {
        MemoryFloor(Arc::new(AtomicU64::new(epoch)))
    }
}

impl EpochFloor for MemoryFloor {
    fn read(&self) -> io::Result<u64> {
        Ok(self.0.load(Ordering::SeqCst))
    }

    fn record(&self, epoch: u64) -> io::Result<()> {
        self.0.fetch_max(epoch, Ordering::SeqCst);
        Ok(())
    }
}

/// A floor in a file, written where a crash cannot leave it half-written.
///
/// Write to a temporary, `fsync` it, rename over the target, `fsync` the
/// directory. The rename is what makes the update atomic and the two syncs are
/// what make it durable; without the directory sync the rename itself can be
/// lost, which would resurrect the previous floor — the exact failure this type
/// exists to prevent, arrived at one level down.
pub struct FileFloor {
    path: PathBuf,
}

impl FileFloor {
    pub fn new(path: impl AsRef<Path>) -> Self {
        FileFloor { path: path.as_ref().to_path_buf() }
    }
}

impl EpochFloor for FileFloor {
    fn read(&self) -> io::Result<u64> {
        match fs::read_to_string(&self.path) {
            Ok(text) => text.trim().parse::<u64>().map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: not an epoch: {e}", self.path.display()),
                )
            }),
            // Never recorded. Distinguished from a read failure on purpose: a
            // registry may legitimately start with no history, and may not
            // start by *ignoring* a floor it could not read.
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(0),
            Err(e) => Err(e),
        }
    }

    fn record(&self, epoch: u64) -> io::Result<()> {
        if self.read()? >= epoch {
            return Ok(());
        }
        let tmp = self.path.with_extension("next");
        {
            let mut f = fs::File::create(&tmp)?;
            write!(f, "{epoch}")?;
            f.sync_all()?;
        }
        fs::rename(&tmp, &self.path)?;
        // An empty parent is `Path::parent` reporting the current directory for
        // a bare filename, which `File::open("")` cannot open.
        if let Some(dir) = self.path.parent().filter(|d| !d.as_os_str().is_empty()) {
            fs::File::open(dir)?.sync_all()?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// The audit log
// ---------------------------------------------------------------------------

/// One thing the registry did.
///
/// Identical in shape to the event the simulation suite's oracles already read.
/// The log is the only record an auditor has after the fact, and every oracle in
/// `tests/` is a predicate over it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// A grant was issued to a node at an epoch.
    Granted { node: u64, epoch: u64 },
    /// A node took the actor.
    Acquired { node: u64, epoch: u64 },
    /// A write landed, at this sequence number.
    Wrote { node: u64, epoch: u64, seq: u64 },
    /// A write was refused by the fence. Named by the *request's* epoch.
    Fenced { node: u64, epoch: u64 },
    /// An owner was told to stop.
    Revoked { node: u64, new_epoch: u64 },
    /// An epoch was burned, cooperatively or by force.
    EpochBurned { from_epoch: u64, to_epoch: u64, next: u64, forced: bool },
    /// A revoked owner acknowledged.
    Released { node: u64, new_epoch: u64 },
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// The actor's ownership state: the model's three-case enum, at `u64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Owned {
    Unowned { epoch: u64, intended: u64 },
    Transferring { from: u64, to: u64, new_epoch: u64 },
    Owned { owner: u64, epoch: u64 },
}

struct Inner {
    state: Owned,
    /// Grants actually issued. `tr_acquire`'s second conjunct: a grant has to
    /// have been *issued*, not merely be due.
    ///
    /// A set rather than a list. The only question ever asked of it is "was
    /// this grant issued?", which a set answers in constant time and without
    /// storing the same answer twice — and a node agent polls in a loop, so a
    /// list grew by one entry per poll and `acquire` scanned all of them. The
    /// model's counterpart is `System::network`, which is a `Set` for the same
    /// reason: re-sending a grant is `tr_issue_grant` again, and that
    /// transition is explicitly idempotent.
    issued: HashSet<(u64, u64)>,
    writes: u64,
    log: Vec<Event>,
}

/// The service implementation.
///
/// Cloneable and shared: Jetstream constructs one service per accepted lane, and
/// every lane has to see the same actor. The lock is held only across a single
/// transition, all of which are pure arithmetic over a few words.
#[derive(Clone)]
pub struct Registry {
    inner: Arc<Mutex<Inner>>,
    /// Connection address to node number. See the module docs: this is the
    /// stated assumption, and the first thing to replace with TLS identity.
    roster: Arc<HashMap<IpAddr, u64>>,
    /// Where the epoch goes before it is used. See the module docs.
    floor: Arc<dyn EpochFloor>,
}

impl Registry {
    /// A registry offering the actor to `first_owner`, with `roster` naming
    /// which address is which node.
    ///
    /// **The starting epoch is read, not supplied.** It is one above the
    /// highest epoch `floor` has ever recorded, and that new epoch is recorded
    /// before this function returns — so a registry that restarts, or that dies
    /// during construction, can only ever come back *higher*. Taking the number
    /// from the caller instead is what let a restart rewind the actor to an
    /// epoch a partitioned owner still believed in; see the module docs.
    ///
    /// Recording before serving costs one epoch per restart, and epochs are not
    /// a resource worth conserving: the model's are unbounded, and `u64`'s run
    /// out only after six hundred years of burning one a nanosecond.
    pub fn new(
        roster: HashMap<IpAddr, u64>,
        first_owner: u64,
        floor: Arc<dyn EpochFloor>,
    ) -> io::Result<Self> {
        // An actor held for a node that cannot connect is held for nobody, and
        // nothing later can repair it: `poll` only ever offers to `intended`.
        // The same defect `is_node` exists to stop in `force` and
        // `begin_transfer`, at the one place that was still setting `intended`
        // without asking.
        if !roster.values().any(|&n| n == first_owner) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("node {first_owner} is not on the roster"),
            ));
        }
        let recorded = floor.read()?;
        let Some(epoch) = recorded.checked_add(1) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "the epoch space is exhausted",
            ));
        };
        floor.record(epoch)?;
        Ok(Registry {
            inner: Arc::new(Mutex::new(Inner {
                state: Owned::Unowned { epoch, intended: first_owner },
                issued: HashSet::new(),
                writes: 0,
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
            floor,
        })
    }

    /// Write `to_epoch` down before anything that depends on it is visible.
    ///
    /// Called with the registry's lock held, and that is the point rather than
    /// an oversight: the decision to move to `to_epoch` and the record of
    /// having moved there must not be separable, or a second caller could
    /// allocate the same epoch in the gap. A blocking `fsync` under a lock is
    /// the price of getting atomicity and durability from two different places;
    /// getting them from one — a compare-and-swap on the ownership record
    /// itself — is what a real deployment does instead.
    fn persist(&self, to_epoch: u64) -> Result<()> {
        self.floor
            .record(to_epoch)
            .map_err(|e| refuse_down(&format!("could not record epoch {to_epoch}: {e}")))
    }

    /// Is this one of the nodes the registry knows about?
    ///
    /// Membership in the roster's *values*. This was a range check against the
    /// roster's **size**, which is only the same question when the node
    /// numbers happen to be `0..len`. For a roster of `{a: 10, b: 20}` it was
    /// exactly backwards: it admitted 0 and 1, which no connection can ever
    /// be, and refused 10 and 20, which are the only two nodes there are. A
    /// forced revoke could then hand the actor to a node that cannot take it,
    /// leaving it offered to nobody.
    fn is_node(&self, node: u64) -> bool {
        self.roster.values().any(|&n| n == node)
    }

    /// The audit log so far.
    ///
    /// The oracles are predicates over this, so a test needs to be able to read
    /// it out of a running service.
    pub fn log(&self) -> Vec<Event> {
        self.inner.lock().expect("registry lock").log.clone()
    }

    /// Which node is calling, from the connection rather than from the request.
    ///
    /// `None` when the caller is not on the roster, which is the only honest
    /// answer: a request from a machine the registry has never heard of names
    /// no node, whatever it claims. Note there is nothing to compare *against*
    /// here — no argument claims a node — so this cannot disagree with the
    /// request the way the line protocol's connection could.
    fn caller(&self, ctx: &Context) -> Option<u64> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) => self.roster.get(addr).copied(),
            _ => None,
        }
    }

    /// `tr_revoke_owner`, `tr_reassign_unowned`, `tr_abort_transfer`: the
    /// coordinator forcing progress on its own.
    ///
    /// **Deliberately not on the trait.** No node may cause this, and the line
    /// protocol had to enforce that with a dedicated control connection because
    /// `FORCE` was a verb anybody could send. Leaving it off the wire is the
    /// same guarantee obtained by construction rather than by a check.
    ///
    /// Which transition it is depends on the state, and the three are not
    /// interchangeable — in particular the model gives the coordinator no way
    /// to redirect an interrupted transfer to a node of its choosing. From
    /// `Transferring` the actor goes back to the node it came from, whatever
    /// `next` says.
    ///
    /// **So this returns the node the actor is now offered to, which is not
    /// always `next`.** It used to return `Ok(())`, and a caller who asked for
    /// `next` and got a bare success would reasonably conclude it had happened.
    /// Refusing instead — `next != from` while `Transferring` — was the other
    /// option, and it is worse: `tr_abort_transfer` is a transition the
    /// coordinator genuinely needs, and it would become unreachable through
    /// this method whenever the coordinator's preferred successor was not the
    /// node the transfer came from. Reporting the outcome costs the caller one
    /// comparison and costs the protocol nothing.
    pub fn force(&self, next: u64) -> Result<u64> {
        if !self.is_node(next) {
            return Err(refuse_no("no such node"));
        }
        let mut g = self.inner.lock().expect("registry lock");
        let (from_epoch, offered_to) = match g.state {
            Owned::Owned { epoch, .. } => (epoch, next),
            Owned::Unowned { epoch, .. } => (epoch, next),
            // `tr_abort_transfer`: burn *another* epoch, so a grant for
            // `new_epoch` still in flight is stale on arrival, and offer the
            // actor back to the node it was being taken from.
            Owned::Transferring { from, new_epoch, .. } => (new_epoch, from),
        };
        let Some(to_epoch) = from_epoch.checked_add(1) else {
            return Err(exhausted());
        };
        self.persist(to_epoch)?;
        g.state = Owned::Unowned { epoch: to_epoch, intended: offered_to };
        g.log.push(Event::EpochBurned {
            from_epoch,
            to_epoch,
            next: offered_to,
            forced: true,
        });
        Ok(offered_to)
    }
}

impl Ownership for Registry {
    async fn poll(&self, ctx: Context) -> Result<Offer> {
        let Some(node) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("registry lock");
        match g.state {
            // `tr_issue_grant`. The offer is recorded as issued here, which is
            // what `acquire` later requires to have happened.
            Owned::Unowned { epoch, intended } if intended == node => {
                g.issued.insert((node, epoch));
                // Logged on every poll, including a repeat of an offer already
                // standing. That is noise, and it is deliberate: `agrees_with_log`
                // — the oracle that checks a reply and the audit log describe the
                // same event — pairs a `GRANT` reply with exactly one `Granted`
                // entry, so a deduplicated log would make the service's second
                // answer unwitnessed and the oracle unportable. No oracle counts
                // grants; `Standing::issued` and P8's tracker both ask only
                // whether a grant was issued. The set above is where the
                // duplicate actually mattered.
                g.log.push(Event::Granted { node, epoch });
                Ok(Offer::Grant(epoch))
            }
            // `tr_handle_revoke`: the outgoing owner is told to stop.
            Owned::Transferring { from, new_epoch, .. } if from == node => {
                g.log.push(Event::Revoked { node, new_epoch });
                Ok(Offer::Revoke(new_epoch))
            }
            _ => Ok(Offer::Nothing),
        }
    }

    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()> {
        let Some(node) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("registry lock");
        // The grant has to have been issued, not merely be due. This is
        // `tr_acquire`'s second conjunct, and it is easy to lose: a node agent
        // that always polls before acquiring never exercises it.
        if !g.issued.contains(&(node, epoch)) {
            return Err(refuse_no("no grant was issued"));
        }
        match g.state {
            Owned::Unowned { epoch: e, intended } if intended == node && e == epoch => {
                g.state = Owned::Owned { owner: node, epoch: e };
                g.log.push(Event::Acquired { node, epoch: e });
                Ok(())
            }
            _ => Err(refuse_no("not offered at that epoch")),
        }
    }

    async fn write(&self, ctx: Context, epoch: u64) -> Result<u64> {
        let Some(node) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("registry lock");

        // The fence, at the point where the effect lands.
        //
        // This is the one check in the service with a machine-checked
        // justification: `FenceGuard::accepts` is proved to return exactly
        // `may_mutate` for the generation the guard records. Building the guard
        // from the registry's *own* current state — not from anything the
        // caller sent — is what makes that the authoritative check rather than
        // the node-local staleness test the guard performs for a node. See the
        // module docs of `distributed_ownership::exec` for why the distinction
        // matters: a node cannot fence itself.
        let permitted = match g.state {
            Owned::Owned { owner, epoch: e } => FenceGuard::new(owner, e).accepts(node, epoch),
            _ => false,
        };
        if !permitted {
            g.log.push(Event::Fenced { node, epoch });
            return Err(refuse_fenced("not the owner at that epoch"));
        }
        g.writes += 1;
        let seq = g.writes;
        g.log.push(Event::Wrote { node, epoch, seq });
        Ok(seq)
    }

    async fn begin_transfer(&self, ctx: Context, to: u64) -> Result<()> {
        let Some(from) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        // `pre.nodes.contains(to)`. The model requires the successor to exist,
        // and a precondition enforced only by well-behaved callers is not a
        // precondition the registry has.
        if !self.is_node(to) {
            return Err(refuse_err("no such node"));
        }
        if to == from {
            return Err(refuse_no("cannot hand over to yourself"));
        }
        let mut g = self.inner.lock().expect("registry lock");
        match g.state {
            Owned::Owned { owner, epoch } if owner == from => {
                let Some(new_epoch) = epoch.checked_add(1) else {
                    return Err(exhausted());
                };
                // Durable before visible. A registry that dies here comes back
                // at `new_epoch + 1` with the handover never having happened,
                // which loses a handover and no safety; a registry that burned
                // the epoch without writing it down comes back at `epoch` with
                // the outgoing owner unfenced.
                self.persist(new_epoch)?;
                // The epoch is burned immediately, which fences the outgoing
                // owner from here on rather than at some later acknowledgement.
                g.state = Owned::Transferring { from: owner, to, new_epoch };
                g.log.push(Event::EpochBurned {
                    from_epoch: epoch,
                    to_epoch: new_epoch,
                    next: to,
                    forced: false,
                });
                Ok(())
            }
            _ => Err(refuse_no("not the owner")),
        }
    }

    async fn release(&self, ctx: Context, epoch: u64) -> Result<()> {
        let Some(node) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("registry lock");
        match g.state {
            Owned::Transferring { from, to, new_epoch } if from == node && new_epoch == epoch => {
                g.state = Owned::Unowned { epoch: new_epoch, intended: to };
                g.log.push(Event::Released { node, new_epoch });
                Ok(())
            }
            _ => Err(refuse_no("no transfer of yours at that epoch")),
        }
    }
}
