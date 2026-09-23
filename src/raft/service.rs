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

/// One log entry, on the wire and in storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub struct LogEntry {
    /// The term of the leader that created it. This is what makes an entry's
    /// `(index, term)` pair name a leader: Election Safety says there was only
    /// one leader of that term.
    pub term: u64,
    /// The command. Opaque here, as it is in the model: the safety argument is
    /// about the order entries are applied in, not about what they mean.
    pub value: u64,
}

/// The reply to `append_entries`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, JetStreamWireFormat)]
pub enum Appended {
    /// Taken. This is the follower's log length afterwards, which is what the
    /// leader tracks to decide what is replicated.
    Accepted(u64),
    /// Refused. This is the follower's term, so a stale leader finds out.
    Rejected(u64),
}

/// **The replicated log.**
///
/// A trait, and mockable, for two reasons that pull the same way. A real log is
/// a file with a format, a fsync policy and a truncation story, and none of
/// that belongs in the protocol; and the protocol's own behaviour — the
/// consistency check, the truncation, the up-to-date comparison — is exactly
/// what you want to test without a disk in the way.
///
/// Every mutating method **must be durable before it returns**, for the reason
/// `Durable` gives about votes: a log that forgets an entry it acknowledged has
/// told the leader something untrue, and the leader may have committed on the
/// strength of it.
pub trait LogStore: Send + Sync + 'static {
    /// How many entries there are.
    fn len(&self) -> io::Result<u64>;

    /// The entry at `index`, or `None` past the end.
    fn entry_at(&self, index: u64) -> io::Result<Option<LogEntry>>;

    /// Append one entry, returning the new length.
    fn append(&self, entry: LogEntry) -> io::Result<u64>;

    /// Keep the first `prefix` entries, drop the rest, append `entry`.
    ///
    /// The truncation is the part that matters and the part a naive
    /// implementation gets wrong: a follower that appends without dropping the
    /// divergent tail keeps entries no leader ever committed.
    fn overwrite(&self, prefix: u64, entry: LogEntry) -> io::Result<()>;

    /// The term of the entry at `index`, or `None` past the end.
    fn term_at(&self, index: u64) -> io::Result<Option<u64>> {
        Ok(self.entry_at(index)?.map(|e| e.term))
    }

    /// The `(last term, length)` pair a `RequestVote` carries.
    ///
    /// An empty log reports term 0, which is safe as a floor because no entry
    /// is ever created at term 0: entries come from leaders, and a leader's
    /// term is at least 1.
    fn summary(&self) -> io::Result<(u64, u64)> {
        let n = self.len()?;
        if n == 0 {
            Ok((0, 0))
        } else {
            Ok((self.term_at(n - 1)?.unwrap_or(0), n))
        }
    }
}

/// An in-memory log. The mock, and the thing the tests run against.
#[derive(Clone, Debug, Default)]
pub struct MemoryLogStore(Arc<Mutex<Vec<LogEntry>>>);

impl MemoryLogStore {
    pub fn new() -> Self {
        MemoryLogStore(Arc::new(Mutex::new(Vec::new())))
    }

    /// The whole log, for tests to compare against.
    pub fn entries(&self) -> Vec<LogEntry> {
        self.0.lock().expect("log lock").clone()
    }
}

impl LogStore for MemoryLogStore {
    fn len(&self) -> io::Result<u64> {
        Ok(self.0.lock().expect("log lock").len() as u64)
    }

    fn entry_at(&self, index: u64) -> io::Result<Option<LogEntry>> {
        Ok(self.0.lock().expect("log lock").get(index as usize).copied())
    }

    fn append(&self, entry: LogEntry) -> io::Result<u64> {
        let mut g = self.0.lock().expect("log lock");
        g.push(entry);
        Ok(g.len() as u64)
    }

    fn overwrite(&self, prefix: u64, entry: LogEntry) -> io::Result<()> {
        let mut g = self.0.lock().expect("log lock");
        g.truncate(prefix as usize);
        g.push(entry);
        Ok(())
    }
}

/// The node-facing protocol.
///
/// Three methods, and none of them takes a server number — see the module docs.
/// Standing for election, tallying votes and taking a term are *not* here: they
/// are things a server does to itself, and putting them on the wire would let a
/// peer declare somebody leader. They are inherent methods on [`Peer`], for the
/// same reason `force` is inherent on the ownership registry.
#[service(uses(super::{Appended, Ballot, LogEntry, Standing}))]
pub trait Consensus {
    /// `RequestVote`. The candidate is the caller.
    ///
    /// `last_term` and `last_index` are the candidate's log summary, and the
    /// voter judges them against its own. They are arguments rather than
    /// something the voter looks up, because a vote has to be decided on what
    /// was true when it was asked for — and because the voter cannot see the
    /// candidate's log at all.
    async fn request_vote(
        &self,
        ctx: Context,
        term: u64,
        last_term: u64,
        last_index: u64,
    ) -> Result<Ballot>;

    /// `AppendEntries`, one entry at a time. The leader is the caller.
    ///
    /// `prefix` is how many entries the leader believes the follower already
    /// agrees on, and `prev_term` is the term of the entry before that — the
    /// **consistency check**. A follower that accepts drops whatever it had
    /// beyond `prefix`.
    async fn append_entries(
        &self,
        ctx: Context,
        term: u64,
        prefix: u64,
        prev_term: u64,
        entry: LogEntry,
        leader_commit: u64,
    ) -> Result<Appended>;

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
    /// The leader appended a client command at its own term.
    Appended { term: u64, index: u64 },
    /// A follower accepted an entry, and this is its log length afterwards.
    Accepted { term: u64, prefix: u64, len: u64 },
    /// A follower refused one — the consistency check, or a stale term.
    RefusedAppend { term: u64, prefix: u64 },
    /// The leader advanced the commit point.
    Committed { term: u64, upto: u64 },
}

// ---------------------------------------------------------------------------
// The server
// ---------------------------------------------------------------------------

struct Inner {
    server: ExecServer,
    /// Who this server voted for in `server.current_term`.
    voted_for: Option<u64>,
    /// How many entries are committed. A count, not an index — the same choice
    /// the model makes, and for the same reason.
    commit: u64,
    /// Per-follower replication progress, kept by a leader: how many entries
    /// each is known to hold. This is what a majority is counted over when the
    /// commit point advances.
    match_len: HashMap<u64, u64>,
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
    /// The replicated log. A trait so that the protocol can be exercised
    /// without a disk, and so that a real one can be a real one.
    entries: Arc<dyn LogStore>,
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
        entries: Arc<dyn LogStore>,
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
                // Volatile, per figure 2: a recovered server recomputes what is
                // committed from the leader rather than trusting a number it
                // wrote down. Starting at 0 costs a round trip and cannot be
                // wrong.
                commit: 0,
                match_len: HashMap::new(),
                log: Vec::new(),
            })),
            roster: Arc::new(roster),
            me,
            store,
            entries,
        })
    }

    /// The log, for a caller that needs to read it (a leader deciding what to
    /// send, a test checking what landed).
    pub fn log_store(&self) -> &Arc<dyn LogStore> {
        &self.entries
    }

    /// The `(last term, length)` pair a vote request carries.
    pub fn summary(&self) -> Result<(u64, u64)> {
        self.entries.summary().map_err(|e| refuse_down(&format!("could not read the log: {e}")))
    }

    /// How many entries this server considers committed.
    pub fn commit(&self) -> u64 {
        self.inner.lock().expect("peer lock").commit
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
        let my_len = self
            .entries
            .len()
            .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?;
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
                // A leader holds its own whole log, which is where the
                // replication tally starts from.
                g.match_len.insert(self.me, my_len);
                g.log.push(Event::Led { term, votes });
                Ok(true)
            }
            // Not yet a majority, or not standing any more. Neither is a
            // failure of the caller's, so neither is reported as one.
            RaftOutcome::Refused(_) => Ok(false),
        }
    }

    /// **A client command**, appended by a leader at its own term.
    ///
    /// Inherent rather than on the trait for the reason `stand_for_election` is:
    /// it is the leader acting, not a peer asking. Returns the index the entry
    /// landed at.
    pub fn append_command(&self, value: u64) -> Result<u64> {
        // The lock is held across the append, and that is the point rather than
        // an oversight: "am I the leader" and "what index does this land at"
        // must not be separable, or two concurrent appends both read the same
        // length and one of them is wrong about where its entry went.
        let mut g = self.inner.lock().expect("peer lock");
        if !matches!(g.server.role, ExecRole::Leader) {
            return Err(refuse_no("not the leader"));
        }
        let term = g.server.current_term;
        let len = self
            .entries
            .append(LogEntry { term, value })
            .map_err(|e| refuse_down(&format!("could not append: {e}")))?;
        g.log.push(Event::Appended { term, index: len - 1 });
        // A leader trivially holds its own entries.
        g.match_len.insert(self.me, len);
        Ok(len - 1)
    }

    /// Record that `from` holds `len` entries, and advance the commit point if
    /// that made a majority.
    ///
    /// **The commit rule is the figure-8 one**: a majority holding the prefix is
    /// not enough on its own — the last entry of that prefix has to be from this
    /// leader's own term. A majority *holding* an entry is not a majority having
    /// *voted* on it, and committing on replica count alone lets a later leader
    /// overwrite the entry.
    pub fn record_match(&self, from: u64, len: u64) -> Result<u64> {
        if !self.is_member(from) {
            return Err(refuse_err("no such server"));
        }
        let mut g = self.inner.lock().expect("peer lock");
        if !matches!(g.server.role, ExecRole::Leader) {
            return Err(refuse_no("not the leader"));
        }
        let term = g.server.current_term;
        let best = g.match_len.get(&from).copied().unwrap_or(0);
        if len > best {
            g.match_len.insert(from, len);
        }

        // Try each candidate length from the longest down. Small clusters and
        // short logs; clarity beats cleverness here.
        let mut upto = g.match_len.values().copied().max().unwrap_or(0);
        while upto > g.commit {
            let holders = g.match_len.values().filter(|&&l| l >= upto).count() as u64;
            let of_my_term = self
                .entries
                .term_at(upto - 1)
                .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?
                == Some(term);
            if of_my_term && is_majority(holders.min(self.members()), self.members()) {
                g.commit = upto;
                g.log.push(Event::Committed { term, upto });
                break;
            }
            upto -= 1;
        }
        Ok(g.commit)
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
    async fn request_vote(
        &self,
        ctx: Context,
        term: u64,
        last_term: u64,
        last_index: u64,
    ) -> Result<Ballot> {
        let Some(candidate) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("peer lock");
        // Read under the lock, with everything else this decision depends on: a
        // summary taken before the lock is an answer about a log that may have
        // moved by the time the vote is granted.
        let (my_last_term, my_len) = self.summary()?;

        // A higher term is adopted before the request is judged, so the vote is
        // considered in the term it was asked about.
        self.step_down_to(&mut g, term)?;

        // **The up-to-date check**, and the one guard that exists for the log
        // rather than for the election: a later last term wins, and at equal
        // last terms the longer log wins. Without it a server missing committed
        // entries could be elected and then overwrite them — the reason the log
        // restricts elections rather than the other way round.
        let up_to_date =
            last_term > my_last_term || (last_term == my_last_term && last_index >= my_len);
        if !up_to_date {
            g.log.push(Event::RefusedVote { term, to: candidate });
            return Ok(Ballot::Refused(g.server.current_term));
        }

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

    async fn append_entries(
        &self,
        ctx: Context,
        term: u64,
        prefix: u64,
        prev_term: u64,
        entry: LogEntry,
        leader_commit: u64,
    ) -> Result<Appended> {
        let Some(_leader) = self.caller(&ctx) else {
            return Err(refuse_no("unknown caller"));
        };
        let mut g = self.inner.lock().expect("peer lock");
        // The consistency check reads the log, and the write that follows
        // depends on what it read, so both happen under the one lock.
        let my_len = self
            .entries
            .len()
            .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?;
        let prev = if prefix == 0 {
            None
        } else {
            self.entries
                .term_at(prefix - 1)
                .map_err(|e| refuse_down(&format!("could not read the log: {e}")))?
        };

        // A higher term is adopted first, so the request is judged in its own
        // term.
        self.step_down_to(&mut g, term)?;

        // A stale leader is refused and told the current term.
        if term < g.server.current_term {
            g.log.push(Event::RefusedAppend { term, prefix });
            return Ok(Appended::Rejected(g.server.current_term));
        }

        // **The consistency check.** The follower takes the entry only if it
        // already agrees with the leader on the one before it — which is what
        // makes agreement at one index imply agreement at every earlier one,
        // and is the whole mechanism Log Matching is about.
        let agrees = if prefix == 0 {
            true
        } else {
            prefix <= my_len && prev == Some(prev_term)
        };
        if !agrees {
            g.log.push(Event::RefusedAppend { term, prefix });
            return Ok(Appended::Rejected(g.server.current_term));
        }

        // Accepting means dropping whatever was beyond `prefix`. A follower
        // that appended without truncating would keep entries no leader ever
        // committed.
        //
        // Written under the lock. The consistency check read the log, and a
        // second request that interleaved between the check and the write would
        // be truncating against an answer that was true a moment ago — which is
        // exactly the class of bug the check exists to prevent.
        self.entries
            .overwrite(prefix, entry)
            .map_err(|e| refuse_down(&format!("could not write the log: {e}")))?;
        let new_len = prefix + 1;

        // `min(leaderCommit, index of the last new entry)`, and never
        // backwards.
        let learned = if leader_commit < new_len { leader_commit } else { new_len };
        if learned > g.commit {
            g.commit = learned;
        }
        g.log.push(Event::Accepted { term, prefix, len: new_len });
        Ok(Appended::Accepted(new_len))
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
