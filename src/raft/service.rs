//! Raft leader election, as a Jetstream service.
//!
//! `services/ownership` serves a protocol whose exclusivity is *assumed*: the
//! ownership model's registry is updated atomically, which rules out two
//! coordinators by construction, and the README's failure-model table says a
//! real deployment has to buy that from consensus. This is the service that
//! starts buying it.
//!
//! Every decision this server makes about its own record goes through a step
//! function in `distributed_ownership::raft_steps`, each proved in
//! `proofs::raft_refinement` to agree with the model's transition — and the
//! model's `theorem_election_safety` says at most one server leads a term.
//!
//! # Identity comes from the connection, again
//!
//! No method takes a server number. **The candidate asking for a vote is
//! whoever opened the connection**, not whoever the frame says. This is the
//! same design as the ownership service and it matters more here: a protocol
//! whose entire safety argument is "a server votes once per term" is exactly
//! the protocol you do not want taking the voter's *or* the candidate's
//! identity from a field an attacker fills in.
//!
//! The same caveat applies with the same force. [`Context::peer`] is `None`
//! over plain TCP, so identity here is an **address** checked against a roster
//! fixed at construction. An address is not a credential. In a simulated
//! network nothing can spoof one; on a real network it is worth very little,
//! and replacing it with TLS identity is the first thing to do.
//!
//! # What a server writes down before it speaks
//!
//! Raft's own figure 2 requires `currentTerm` and `votedFor` to be *"updated on
//! stable storage before responding to RPCs"*, and that is not an optimisation
//! note — it is the same requirement the ownership registry's epoch floor turned
//! out to have, arrived at from the other end.
//!
//! A server that grants a vote, replies, restarts having forgotten, and grants
//! again has voted twice in one term. Two candidates can then each collect a
//! majority, and Election Safety is gone — not because the proof is wrong, but
//! because `already_voted` was reported `false` when the model's `has_voted`
//! was true. That is the coupling `proofs::raft_refinement` names, and
//! [`Durable`] is what discharges it.
//!
//! So the order is: decide, **persist**, then reply. A server that dies between
//! the persist and the reply has lost a message, which the protocol handles. A
//! server that dies between the reply and the persist has broken the protocol.
//!
//! # What is not here
//!
//! Logs. No `AppendEntries`, no commitment, no state machine — so this is a
//! leader *election* service, not a consensus service, and it cannot yet make
//! the ownership registry's contents a single agreed fact. `heartbeat` carries
//! a term and nothing else: it is how a leader keeps followers from timing out
//! and how everyone learns of a higher term, which is all a leader can do
//! without a log.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write as _};
use std::net::IpAddr;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::raft::steps::{
    become_leader_step, grant_vote_step, is_majority, step_down_step, timeout_step, ExecRole,
    ExecServer, RaftOutcome, RaftRefusal,
};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// The reply to a vote request.
///
/// Both cases carry the voter's term, which is Raft's rule: a candidate that
/// hears a higher term learns it has already lost, and a refusal that did not
/// say so would leave it standing for a term nobody will vote in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub enum Ballot {
    /// The vote is yours, at this term.
    Granted(u64),
    /// Not this time. This is the voter's term.
    Refused(u64),
}

/// What a server says about itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct Standing {
    pub term: u64,
    /// Whether this server believes it leads `term`. **A belief, not a fact**:
    /// a partitioned leader goes on believing this until it hears a higher
    /// term. Election Safety says at most one server can be right.
    pub leading: bool,
}

/// The node-facing protocol.
///
/// Three methods, and none of them takes a server number — see the module docs.
/// Standing for election, tallying votes and taking a term are *not* here: they
/// are things a server does to itself, and putting them on the wire would let a
/// peer declare somebody leader. They are inherent methods on [`Peer`], for the
/// same reason `force` is inherent on the ownership registry.
#[service(uses(super::{Ballot, Standing}))]
pub trait Consensus {
    /// `RequestVote`. The candidate is the caller.
    async fn request_vote(&self, ctx: Context, term: u64) -> Result<Ballot>;

    /// A leader asserting its term. The leader is the caller.
    ///
    /// Carries no entries, because there is no log yet. What it does carry is
    /// the term, which is how a stale leader finds out it is one.
    async fn heartbeat(&self, ctx: Context, term: u64) -> Result<Standing>;

    /// What term is this server in, and does it think it leads?
    async fn standing(&self, ctx: Context) -> Result<Standing>;
}

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

/// The server could not make a decision durable, so it did not make one.
///
/// The same code and the same reasoning as the ownership service's: this says
/// nothing about the protocol's state, so an auditor must not read it as a
/// guard having been evaluated. Here it is load-bearing rather than tidy —
/// answering a vote request the server could not write down is precisely the
/// failure that breaks Election Safety.
fn refuse_down(what: &str) -> Error {
    Error::new(what).set_code("DOWN")
}

/// The `u64` term space is exhausted.
fn exhausted() -> Error {
    Error::new("the term space is exhausted").set_code("NO")
}

fn refuse(why: RaftRefusal) -> Error {
    match why {
        RaftRefusal::Exhausted => exhausted(),
        RaftRefusal::AlreadyVoted => refuse_no("already voted in that term"),
        RaftRefusal::TermBehind => refuse_no("that term is behind mine"),
        RaftRefusal::NotCandidate => refuse_no("not standing for that term"),
        RaftRefusal::NoQuorum => refuse_no("not a majority"),
        RaftRefusal::NotHigher => refuse_no("that term is not ahead of mine"),
        RaftRefusal::AlreadyLeading => refuse_no("already leading a term"),
    }
}

// ---------------------------------------------------------------------------
// Durable state
// ---------------------------------------------------------------------------

/// The two things Raft requires on stable storage.
///
/// Exactly figure 2's "persistent state on all servers", minus the log:
/// `currentTerm` and `votedFor`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Persisted {
    pub current_term: u64,
    /// Who this server voted for **in `current_term`**. Cleared whenever the
    /// term advances, because a vote belongs to the term it was cast in.
    pub voted_for: Option<u64>,
}

/// Stable storage for [`Persisted`].
///
/// `save` must not return until the value is durable. An implementation that
/// returns early satisfies the type and breaks Election Safety, which is the
/// usual shape of this kind of interface and is stated here rather than left
/// to be inferred.
pub trait Durable: Send + Sync + 'static {
    fn load(&self) -> io::Result<Persisted>;
    fn save(&self, state: Persisted) -> io::Result<()>;
}

/// Storage that survives the [`Peer`] but not the process.
///
/// Enough to reproduce the defect that matters — a server that comes back not
/// knowing what it voted for — without killing a process.
#[derive(Clone, Debug, Default)]
pub struct MemoryLog(Arc<Mutex<Persisted>>);

impl MemoryLog {
    pub fn new() -> Self {
        MemoryLog(Arc::new(Mutex::new(Persisted::default())))
    }
}

impl Durable for MemoryLog {
    fn load(&self) -> io::Result<Persisted> {
        Ok(*self.0.lock().expect("vote log lock"))
    }

    fn save(&self, state: Persisted) -> io::Result<()> {
        *self.0.lock().expect("vote log lock") = state;
        Ok(())
    }
}

/// Storage that survives the machine.
///
/// Temporary file, `fsync`, rename, `fsync` the directory — and the directory
/// sync is never skipped, including when the path is a bare filename whose
/// `Path::parent` is the empty path. Skipping it there was a real finding on
/// the ownership service's equivalent: it made durability depend on how the
/// caller spelled the path, and losing the rename resurrects the previous
/// state, which is the exact failure this type exists to prevent.
pub struct FileLog {
    path: PathBuf,
}

impl FileLog {
    pub fn new(path: impl AsRef<Path>) -> Self {
        FileLog { path: path.as_ref().to_path_buf() }
    }
}

impl Durable for FileLog {
    fn load(&self) -> io::Result<Persisted> {
        match fs::read_to_string(&self.path) {
            Ok(text) => {
                let mut parts = text.trim().split_whitespace();
                let bad = || {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("{}: not a persisted Raft state", self.path.display()),
                    )
                };
                let current_term: u64 = parts.next().ok_or_else(bad)?.parse().map_err(|_| bad())?;
                let voted_for = match parts.next().ok_or_else(bad)? {
                    "-" => None,
                    other => Some(other.parse::<u64>().map_err(|_| bad())?),
                };
                Ok(Persisted { current_term, voted_for })
            }
            // Never written. Distinguished from a read failure on purpose: a
            // server may legitimately start with no history, and may not start
            // by *ignoring* a record it could not read.
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(Persisted::default()),
            Err(e) => Err(e),
        }
    }

    fn save(&self, state: Persisted) -> io::Result<()> {
        let tmp = self.path.with_extension("next");
        {
            let mut f = fs::File::create(&tmp)?;
            match state.voted_for {
                Some(c) => write!(f, "{} {}", state.current_term, c)?,
                None => write!(f, "{} -", state.current_term)?,
            }
            f.sync_all()?;
        }
        fs::rename(&tmp, &self.path)?;
        let dir = self.path.parent().unwrap_or_else(|| Path::new(""));
        let dir = if dir.as_os_str().is_empty() { Path::new(".") } else { dir };
        fs::File::open(dir)?.sync_all()?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// The audit log
// ---------------------------------------------------------------------------

/// One thing a server did. The record an auditor reads after the fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// Stood for election in a new term, voting for itself.
    Stood { term: u64 },
    /// Granted its vote.
    Granted { term: u64, to: u64 },
    /// Refused one. Named by the *request's* term.
    RefusedVote { term: u64, to: u64 },
    /// Counted a vote in its own favour.
    Counted { term: u64, from: u64 },
    /// Took a term, with the tally that bought it.
    Led { term: u64, votes: u64 },
    /// Learned of a higher term and stepped down into it.
    SteppedDown { from_term: u64, to_term: u64 },
}

// ---------------------------------------------------------------------------
// The server
// ---------------------------------------------------------------------------

struct Inner {
    server: ExecServer,
    /// Who this server voted for in `server.current_term`.
    voted_for: Option<u64>,
    /// Votes collected for this server's own candidacy at
    /// `server.current_term`. A **set**, because `is_majority`'s precondition
    /// is that the tally does not exceed the membership, and a list would let
    /// one enthusiastic peer vote twice.
    tally: HashSet<u64>,
    log: Vec<Event>,
}

/// One Raft server.
#[derive(Clone)]
pub struct Peer {
    inner: Arc<Mutex<Inner>>,
    /// Connection address to server number. The stated assumption; see the
    /// module docs.
    roster: Arc<HashMap<IpAddr, u64>>,
    /// This server's own number.
    me: u64,
    store: Arc<dyn Durable>,
}

impl Peer {
    /// A server that recovers whatever `store` remembers.
    ///
    /// **The term is read, not supplied.** A server that started at a term of
    /// its caller's choosing could re-enter a term it had already voted in,
    /// which is the same defect the ownership registry had when `new` took its
    /// epoch from the caller, and it breaks the same guarantee.
    pub fn new(
        roster: HashMap<IpAddr, u64>,
        me: u64,
        store: Arc<dyn Durable>,
    ) -> io::Result<Self> {
        if !roster.values().any(|&n| n == me) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("server {me} is not on the roster"),
            ));
        }
        let recovered = store.load()?;
        Ok(Peer {
            inner: Arc::new(Mutex::new(Inner {
                // A recovered server is always a follower. Raft has no durable
                // role, and inventing one would let a restarted leader go on
                // leading a term the cluster has moved past.
                server: ExecServer {
                    role: ExecRole::Follower,
                    current_term: recovered.current_term,
                },
                voted_for: recovered.voted_for,
                tally: HashSet::new(),
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
            me,
            store,
        })
    }

    /// How many servers are in the cluster.
    ///
    /// The count is of **distinct server numbers**, not of roster entries. This
    /// one really is a cardinality question — a majority is about *how many* —
    /// unlike "is this a member", which is about the roster's values; the two
    /// were conflated once already in this repository and are kept visibly
    /// apart here. Counting entries would also be wrong in its own right the
    /// moment one server is reachable at two addresses, which is an ordinary
    /// thing for a server to be.
    fn members(&self) -> u64 {
        self.roster.values().copied().collect::<HashSet<u64>>().len() as u64
    }

    fn is_member(&self, n: u64) -> bool {
        self.roster.values().any(|&v| v == n)
    }

    /// Which server is calling, from the connection rather than the request.
    fn caller(&self, ctx: &Context) -> Option<u64> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) => self.roster.get(addr).copied(),
            _ => None,
        }
    }

    /// Write the decision down before acting on it.
    fn persist(&self, term: u64, voted_for: Option<u64>) -> Result<()> {
        self.store
            .save(Persisted { current_term: term, voted_for })
            .map_err(|e| refuse_down(&format!("could not persist term {term}: {e}")))
    }

    /// The audit log so far.
    pub fn log(&self) -> Vec<Event> {
        self.inner.lock().expect("peer lock").log.clone()
    }

    /// What this server believes about itself.
    pub fn standing_now(&self) -> Standing {
        let g = self.inner.lock().expect("peer lock");
        Standing {
            term: g.server.current_term,
            leading: matches!(g.server.role, ExecRole::Leader),
        }
    }

    /// **Stand for election in the next term**, voting for yourself.
    ///
    /// Inherent rather than on the trait: a timeout is a server's own clock
    /// going off, and a peer that could trigger it could keep the cluster in a
    /// permanent election.
    pub fn stand_for_election(&self) -> Result<u64> {
        let mut g = self.inner.lock().expect("peer lock");
        let next = match timeout_step(g.server) {
            RaftOutcome::Moved(next) => next,
            RaftOutcome::Refused(why) => return Err(refuse(why)),
        };
        let term = next.current_term;
        // Durable before anything else, and the self-vote goes down with the
        // term: they are one decision, and a server that recorded the term
        // without the vote could vote again in it after a restart.
        self.persist(term, Some(self.me))?;
        g.server = next;
        g.voted_for = Some(self.me);
        g.tally = HashSet::new();
        g.tally.insert(self.me);
        g.log.push(Event::Stood { term });
        Ok(term)
    }

    /// Count a vote granted to this server, and take the term if that was the
    /// one that made a majority.
    ///
    /// Returns whether this server now leads.
    pub fn count_vote(&self, from: u64, term: u64) -> Result<bool> {
        if !self.is_member(from) {
            return Err(refuse_err("no such server"));
        }
        let mut g = self.inner.lock().expect("peer lock");
        if g.server.current_term != term {
            // A vote for a term this server has left. Not an error on anyone's
            // part — it is what a reply delayed past a new election looks like
            // — but it must not be counted, or a stale ballot would elect
            // somebody in a term it was never cast for.
            return Ok(matches!(g.server.role, ExecRole::Leader));
        }
        g.tally.insert(from);
        g.log.push(Event::Counted { term, from });

        // Every tallied voter is a member and the set holds each at most once,
        // so the count cannot exceed the membership — which is exactly
        // `is_majority`'s precondition.
        let votes = g.tally.len() as u64;
        let has_quorum = is_majority(votes, self.members());

        match become_leader_step(g.server, term, has_quorum) {
            RaftOutcome::Moved(next) => {
                g.server = next;
                g.log.push(Event::Led { term, votes });
                Ok(true)
            }
            // Not yet a majority, or not standing any more. Neither is a
            // failure of the caller's, so neither is reported as one.
            RaftOutcome::Refused(_) => Ok(false),
        }
    }

    /// Adopt a strictly higher term, durably, and drop to follower.
    ///
    /// Shared by `request_vote` and `heartbeat`, because Raft's rule is about
    /// any RPC: *"if RPC request or response contains term T > currentTerm, set
    /// currentTerm = T, convert to follower"*.
    fn step_down_to(&self, g: &mut Inner, term: u64) -> Result<()> {
        let next = match step_down_step(g.server, term) {
            RaftOutcome::Moved(next) => next,
            // Not actually higher; nothing to do.
            RaftOutcome::Refused(_) => return Ok(()),
        };
        let from_term = g.server.current_term;
        // The vote is cleared as the term advances, and both go down together.
        self.persist(term, None)?;
        g.server = next;
        g.voted_for = None;
        g.tally = HashSet::new();
        g.log.push(Event::SteppedDown { from_term, to_term: term });
        Ok(())
    }
}

impl Consensus for Peer {
    async fn request_vote(&self, ctx: Context, term: u64) -> Result<Ballot> {
        let Some(candidate) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("peer lock");

        // A higher term is adopted before the request is judged, so the vote is
        // considered in the term it was asked about.
        self.step_down_to(&mut g, term)?;

        // Re-granting the *same* vote to the *same* candidate is a
        // retransmission, not a second vote.
        //
        // This is the one place the service is deliberately outside the model's
        // transition rather than inside it. `tr_grant_vote` requires
        // `!has_voted`, so it cannot fire here — but the model's `votes` is a
        // *set*, and re-inserting a vote it already holds changes nothing. The
        // reply is therefore a repeat of an earlier reply, exactly as
        // `tr_issue_grant` is a repeat of an earlier grant in the ownership
        // model, and refusing it instead would lose a vote to any dropped
        // packet.
        if g.server.current_term == term && g.voted_for == Some(candidate) {
            return Ok(Ballot::Granted(term));
        }

        let already_voted = g.server.current_term == term && g.voted_for.is_some();
        match grant_vote_step(g.server, term, already_voted) {
            RaftOutcome::Moved(next) => {
                // Decide, persist, *then* reply. A server that replies first and
                // dies has voted twice in one term as far as the cluster is
                // concerned, and two candidates can then each hold a majority.
                self.persist(term, Some(candidate))?;
                g.server = next;
                g.voted_for = Some(candidate);
                g.log.push(Event::Granted { term, to: candidate });
                Ok(Ballot::Granted(term))
            }
            RaftOutcome::Refused(_) => {
                g.log.push(Event::RefusedVote { term, to: candidate });
                Ok(Ballot::Refused(g.server.current_term))
            }
        }
    }

    async fn heartbeat(&self, ctx: Context, term: u64) -> Result<Standing> {
        let Some(_leader) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("peer lock");
        self.step_down_to(&mut g, term)?;
        Ok(Standing {
            term: g.server.current_term,
            leading: matches!(g.server.role, ExecRole::Leader),
        })
    }

    async fn standing(&self, ctx: Context) -> Result<Standing> {
        if self.caller(&ctx).is_none() {
            return Err(refuse_no("unknown caller"));
        }
        let g = self.inner.lock().expect("peer lock");
        Ok(Standing {
            term: g.server.current_term,
            leading: matches!(g.server.role, ExecRole::Leader),
        })
    }
}
