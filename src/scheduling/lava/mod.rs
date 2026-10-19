//! LAVA placement (§4.3), NILAS scoring (§4.2), and LARS ordering (§4.4).
//!
//! Time is caller-supplied, monotonic integer seconds. Exits are explicit events;
//! a predicted expiry never removes a job. See README for paper ambiguities and
//! concrete policy choices. No model, runtime, or network service is required.
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
    time::Duration,
};

use crate::{
    compute::{Cpu, Instant, Job, JobId, Memory, Resources},
    host::HostId,
};

/// Seconds in an hour: the first lifetime class's upper bound.
const HOUR: u64 = 3600;

/// `n` hours.
const fn hours(n: u64) -> Duration {
    Duration::from_secs(HOUR * n)
}

// Time is a `Duration` since an epoch the caller chooses, not an `Instant`: an
// `Instant` can only be made by reading the clock, which would put the clock back
// inside a scheduler that takes its time from outside.

/// How much longer a job is predicted to live, in the paper's four decade classes
/// (§4.3): under 1 hour, 1 to 10 hours, 10 to 100 hours, and 100 to 1000 hours;
/// and one more, [`LcForever`](Self::LcForever), which is this port's and not the
/// paper's. Classes are ordered shortest first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LifetimeClass {
    /// Under 1 hour.
    Lc1,
    /// 1 hour up to, not including, 10 hours.
    Lc2,
    /// 10 hours up to, not including, 100 hours.
    Lc3,
    /// 100 hours up to, not including, 1000 hours: the paper's last class.
    Lc4,
    /// 1000 hours and longer. **Not in the paper**, which has no class past LC4
    /// and caps its production lifetimes at 168 hours (§3); it is here for jobs
    /// that outlive every class the paper describes. It has no upper bound, so a
    /// host in it never times out, and a host in LC4 that does is promoted to it.
    LcForever,
}

impl From<LifetimeClass> for Range<Duration> {
    fn from(class: LifetimeClass) -> Self {
        class.range()
    }
}

impl LifetimeClass {
    /// The remaining lifetimes the class takes, as a half-open range: `Lc1` is
    /// 0 to 1 hour, `Lc2` 1 to 10, `Lc3` 10 to 100, `Lc4` 100 to 1000 and
    /// `LcForever` 1000 hours to [`Duration::MAX`].
    ///
    /// This is the one place the boundaries are written down; [`of`](Self::of) and
    /// [`upper_bound`](Self::upper_bound) are read off it.
    pub fn range(self) -> Range<Duration> {
        match self {
            Self::Lc1 => Duration::ZERO..hours(1),
            Self::Lc2 => hours(1)..hours(10),
            Self::Lc3 => hours(10)..hours(100),
            Self::Lc4 => hours(100)..hours(1000),
            Self::LcForever => hours(1000)..Duration::MAX,
        }
    }
    /// The class of a job predicted to live `remaining` longer.
    pub fn of(remaining: Duration) -> Self {
        [Self::Lc1, Self::Lc2, Self::Lc3, Self::Lc4, Self::LcForever]
            .into_iter()
            .find(|class| class.range().contains(&remaining))
            // Only `Duration::MAX` itself, which no half-open range contains.
            .unwrap_or(Self::LcForever)
    }
    /// The class's index: 0 for LC1, 1 for LC2, 2 for LC3, 3 for LC4 and 4 for
    /// `LcForever`.
    pub fn index(self) -> u8 {
        self as u8
    }
    /// The end of the class's range: 1, 10, 100 and 1000 hours, and for
    /// `LcForever` [`Duration::MAX`], which is no bound at all.
    ///
    /// A host's timeout is computed from it (see [`Scheduler`]), so a host in
    /// `LcForever` never times out.
    pub fn upper_bound(self) -> Duration {
        self.range().end
    }
    /// The next class up, or the same one from `LcForever`.
    fn higher(self) -> Self {
        match self {
            Self::Lc1 => Self::Lc2,
            Self::Lc2 => Self::Lc3,
            Self::Lc3 => Self::Lc4,
            Self::Lc4 | Self::LcForever => Self::LcForever,
        }
    }
    /// The next class down, or the same one from LC1.
    fn lower(self) -> Self {
        match self {
            Self::Lc1 | Self::Lc2 => Self::Lc1,
            Self::Lc3 => Self::Lc2,
            Self::Lc4 => Self::Lc3,
            Self::LcForever => Self::Lc4,
        }
    }
}

/// Adapter point for a trained uptime-conditioned regression/survival model.
/// Returned values are *remaining* lifetime, never total lifetime or exit time.
pub trait LifetimePredictor<F> {
    /// The expected remaining lifetime of a job with `features` that has already
    /// run for `uptime`: the paper's E(Tr | Tu) (§3). The scheduler asks again as
    /// uptime grows, which is the paper's *reprediction*, so the answer should
    /// depend on `uptime` and not only on `features`.
    fn remaining(&self, features: &F, uptime: Duration) -> Duration;
}

/// Empirical total-lifetime distribution with equally weighted samples.
/// Reprediction calculates E[T-uptime | T>uptime]. If all observations have
/// been outlived, `tail_remaining` is an explicit caller-selected fallback.
#[derive(Debug, Clone)]
pub struct EmpiricalLifetime {
    samples: Vec<Duration>,
    tail_remaining: Duration,
}

impl EmpiricalLifetime {
    /// A distribution from observed total lifetimes.
    ///
    /// `tail_remaining` is what to predict once `uptime` has passed every sample.
    /// It is the caller's choice: the data says nothing about a job that has
    /// outlived all of it. [`Error::InvalidDistribution`] if there are no samples,
    /// if any sample is zero, or if `tail_remaining` is zero.
    pub fn new(samples: Vec<Duration>, tail_remaining: Duration) -> Result<Self, Error> {
        if samples.is_empty()
            || samples.contains(&Duration::default())
            || tail_remaining == Duration::default()
        {
            return Err(Error::InvalidDistribution);
        }
        Ok(Self {
            samples,
            tail_remaining,
        })
    }
}
/// Predicts remaining lifetime from an [`EmpiricalLifetime`]: the mean, over the
/// samples that outlived `uptime`, of how much longer they lived.
///
/// A stand-in for the paper's learned model (§3), which predicts the same
/// quantity, E(Tr | Tu), with a gradient-boosted decision tree.
#[derive(Debug, Clone, Copy, Default)]
pub struct EmpiricalPredictor;
impl LifetimePredictor<EmpiricalLifetime> for EmpiricalPredictor {
    fn remaining(&self, features: &EmpiricalLifetime, uptime: Duration) -> Duration {
        let (sum, count) = features
            .samples
            .iter()
            .filter(|&&t| t > uptime)
            .fold((Duration::ZERO, 0_u32), |(sum, n), &t| {
                (sum.saturating_add(t - uptime), n.saturating_add(1))
            });
        // `None` only when no sample outlived `uptime`: the explicit fallback.
        sum.checked_div(count).unwrap_or(features.tail_remaining)
    }
}

/// Where a host is in LAVA's life cycle (§4.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostState {
    /// No jobs, and no lifetime class. A new job may start here as a last resort.
    Empty,
    /// Filling up. It takes only jobs of its own lifetime class.
    Open,
    /// Over 90% of its CPU or memory is used, so it only drains: it takes jobs at
    /// least one class lower than its own, which should be gone before it is.
    Recycling,
}

/// A host and the Jobs on it, with the lifetime class LAVA has given it.
///
/// It is a view: only the [`Scheduler`] changes one.
#[derive(Debug, Clone)]
pub struct Host<F> {
    id: HostId,
    capacity: Resources,
    jobs: BTreeMap<JobId, Job<F>>,
    state: HostState,
    class: Option<LifetimeClass>,
    deadline: Option<Instant>,
    residual: BTreeSet<JobId>,
    schedulable: bool,
}

impl<F> Host<F> {
    /// The host's identifier.
    pub fn id(&self) -> HostId {
        self.id
    }
    /// The CPU and memory the host has in total.
    pub fn capacity(&self) -> Resources {
        self.capacity
    }
    /// The jobs on the host, in order of id.
    pub fn jobs(&self) -> impl Iterator<Item = &Job<F>> {
        self.jobs.values()
    }
    /// Where the host is in its life cycle.
    pub fn state(&self) -> HostState {
        self.state
    }
    /// The lifetime class the host was given, or `None` while it is empty.
    pub fn class(&self) -> Option<LifetimeClass> {
        self.class
    }
    /// When the host is promoted a class if it has not emptied by then (§4.3), or
    /// `None` while it is empty. [`Duration::MAX`] means never, which is what a
    /// host in [`LcForever`](LifetimeClass::LcForever) has. The paper does not give
    /// the timeout; see [`Scheduler`] for the one used here.
    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }
    /// The jobs that were on the host at its last class change: when the host
    /// became recycling, was demoted, or was promoted (§4.3). When the last of
    /// them exits, a recycling host drops a class.
    pub fn residual(&self) -> &BTreeSet<JobId> {
        &self.residual
    }
    /// Whether new jobs may be placed on the host. It is off while the host is
    /// being drained (LARS, §4.4) or under maintenance.
    pub fn schedulable(&self) -> bool {
        self.schedulable
    }
    /// The CPU and memory the jobs on the host use together.
    pub fn used(&self) -> Resources {
        self.jobs
            .values()
            .fold(Resources::ZERO, |r, job| Resources {
                cpu: r.cpu + job.resources.cpu,
                memory: r.memory + job.resources.memory,
            })
    }
    fn free(&self) -> Resources {
        let used = self.used();
        Resources {
            cpu: self.capacity.cpu - used.cpu,
            memory: self.capacity.memory - used.memory,
        }
    }
    fn reset(&mut self) {
        self.state = HostState::Empty;
        self.class = None;
        self.deadline = None;
        self.residual.clear();
        // Scheduling availability is independently controlled by maintenance.
    }
    fn assign_class(&mut self, class: LifetimeClass, now: Instant) {
        self.class = Some(class);
        // The paper leaves the precise timeout unspecified. Use 1.1x the
        // class upper bound, anchored at each assignment, with saturation.
        let upper = class.upper_bound();
        self.deadline = Some(now.saturating_add(upper.saturating_add(upper / 10)));
    }
    fn refresh(&mut self, now: Instant) {
        if self.jobs.is_empty() {
            self.reset();
            return;
        }
        if self.state == HostState::Recycling && self.residual.is_empty() {
            self.assign_class(self.class.unwrap().lower(), now);
            self.residual = self.jobs.keys().copied().collect();
        }
        // One promotion per refresh, rather than inventing transitions through
        // unobserved intermediate epochs when the caller advances a long time.
        if self
            .deadline
            .is_some_and(|d| d != Instant::MAX && now >= d)
        {
            self.assign_class(self.class.unwrap().higher(), now);
            self.residual = self.jobs.keys().copied().collect();
        }
    }
}

/// Why a [`Scheduler`] or [`EmpiricalLifetime`] call was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// Invalid capacity: a host was added with no CPU or no memory.
    InvalidCapacity,
    /// Invalid request: a job asked for no CPU and no memory.
    InvalidRequest,
    /// Invalid distribution: an [`EmpiricalLifetime`] had no samples, a zero sample, or a zero tail.
    InvalidDistribution,
    /// Duplicate host: a host with this id is already known.
    DuplicateHost,
    /// Duplicate job: a job with this id is already placed.
    DuplicateJob,
    /// Unknown host: no host with this id is known.
    UnknownHost,
    /// Unknown job: no job with this id is known.
    UnknownJob,
    /// Clock went backwards: the time given is earlier than one already given.
    ClockWentBackwards,
    /// Future job: the job is said to have started after `now`.
    FutureJob,
    /// No capacity: no schedulable, eligible host has room for the job.
    NoCapacity,
    /// Migration not approved: [`Scheduler::begin_drain`] was refused because the approval gate did not
    /// cover every job on the host.
    MigrationNotApproved,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Error::InvalidCapacity => "invalid capacity",
            Error::InvalidRequest => "invalid request",
            Error::InvalidDistribution => "invalid distribution",
            Error::DuplicateHost => "duplicate host",
            Error::DuplicateJob => "duplicate job",
            Error::UnknownHost => "unknown host",
            Error::UnknownJob => "unknown job",
            Error::ClockWentBackwards => "clock went backwards",
            Error::FutureJob => "future job",
            Error::NoCapacity => "no capacity",
            Error::MigrationNotApproved => "migration not approved",
        })
    }
}

impl std::error::Error for Error {}

/// Bucket indices follow §4.2's example: 70 minutes has temporal cost 2.
/// Boundaries are lower edges, with [168h,infinity) an overflow bucket.
pub fn temporal_cost(extension: Duration) -> usize {
    const BOUNDS: [u64; 11] = [
        0, 1800, 3600, 5400, 7200, 10800, 14400, 21600, 43200, 86400, 604800,
    ];
    BOUNDS
        .iter()
        .rposition(|&b| extension >= Duration::from_secs(b))
        .unwrap()
}

/// A single-owner, in-memory scheduler. Callers serialize operations and apply
/// additional hard constraints via `place_with`; no external effects occur here.
///
/// A job is placed on the first host that exists in this order (§4.3, Algorithm
/// 3): a recycling host of a higher class than the job's, the nearest class first;
/// an open host of the job's own class; any other host that has jobs; an empty host.
/// Among hosts of the same kind the choice is NILAS (§4.2): the lowest temporal
/// cost, then the least wasted CPU and memory, then the lowest host id.
///
/// Where the paper leaves a choice open this makes one:
/// * a host's promotion deadline is 1.1 times its class's upper bound after the
///   class was assigned (the paper says a host's lifetime should stay within 1.1
///   times its class, but not the timeout). So an LC4 host times out at 1100 hours
///   and is promoted to `LcForever`, which has no upper bound and so never times out;
/// * a host is promoted at most one class each time the clock advances, however
///   far it advances.
pub struct Scheduler<F, P> {
    predictor: P,
    hosts: BTreeMap<HostId, Host<F>>,
    locations: BTreeMap<JobId, HostId>,
    now: Instant,
}

impl<F, P: LifetimePredictor<F>> Scheduler<F, P> {
    /// A scheduler with no hosts, whose clock starts at zero, that asks
    /// `predictor` how long each job has left.
    pub fn new(predictor: P) -> Self {
        Self {
            predictor,
            hosts: BTreeMap::new(),
            locations: BTreeMap::new(),
            now: Instant::EPOCH,
        }
    }
    /// Every host, in order of id.
    pub fn hosts(&self) -> impl Iterator<Item = &Host<F>> {
        self.hosts.values()
    }
    /// The host with this id, if there is one.
    pub fn host(&self, id: HostId) -> Option<&Host<F>> {
        self.hosts.get(&id)
    }
    /// The host a job is on, if it is placed.
    pub fn location(&self, job: JobId) -> Option<HostId> {
        self.locations.get(&job).copied()
    }
    /// Add an empty, schedulable host. [`Error::InvalidCapacity`] if it has no
    /// CPU or no memory, [`Error::DuplicateHost`] if the id is taken.
    pub fn add_host(&mut self, id: HostId, capacity: Resources) -> Result<(), Error> {
        if capacity.cpu == Cpu::ZERO || capacity.memory == Memory::ZERO {
            return Err(Error::InvalidCapacity);
        }
        if self.hosts.contains_key(&id) {
            return Err(Error::DuplicateHost);
        }
        self.hosts.insert(
            id,
            Host {
                id,
                capacity,
                jobs: BTreeMap::new(),
                state: HostState::Empty,
                class: None,
                deadline: None,
                residual: BTreeSet::new(),
                schedulable: true,
            },
        );
        Ok(())
    }
    /// Advance the clock to `now` and update every host: an empty host loses its
    /// class, a recycling host whose residual jobs have all gone drops a class, and
    /// a host past its deadline is promoted one class (§4.3).
    ///
    /// Time only moves forward: [`Error::ClockWentBackwards`] if `now` is earlier
    /// than a time already given. A predicted exit never removes a job; only
    /// [`remove`](Self::remove) does.
    pub fn tick(&mut self, now: Instant) -> Result<(), Error> {
        if now < self.now {
            return Err(Error::ClockWentBackwards);
        }
        self.now = now;
        for host in self.hosts.values_mut() {
            host.refresh(now);
        }
        Ok(())
    }
    /// Allow or forbid placing new jobs on a host, independently of its life cycle.
    /// [`begin_drain`](Self::begin_drain) turns it off, and maintenance may too.
    /// [`Error::UnknownHost`] if there is no such host.
    pub fn set_schedulable(&mut self, id: HostId, value: bool) -> Result<(), Error> {
        self.hosts
            .get_mut(&id)
            .ok_or(Error::UnknownHost)?
            .schedulable = value;
        Ok(())
    }
    /// Place a job on the best host, at `now`, and return the host's id. Every
    /// schedulable host with room is a candidate; see
    /// [`place_with`](Self::place_with) to restrict them.
    pub fn place(&mut self, job: Job<F>, now: Instant) -> Result<HostId, Error> {
        self.place_with(job, now, |_, _| true)
    }
    /// As [`place`](Self::place), but only on hosts `eligible` accepts: a hard
    /// constraint LAVA knows nothing about, such as a zone or an anti-affinity rule.
    ///
    /// The job's class comes from its predicted remaining lifetime at `now`. A job
    /// placed on an empty host gives the host that class and makes it open; a host
    /// that goes over 90% of its CPU or memory becomes recycling, and the jobs on it
    /// at that moment become its residual set.
    ///
    /// [`Error::DuplicateJob`], [`Error::InvalidRequest`], [`Error::FutureJob`],
    /// [`Error::ClockWentBackwards`] for a bad request, and [`Error::NoCapacity`]
    /// if no candidate has room.
    pub fn place_with(
        &mut self,
        job: Job<F>,
        now: Instant,
        eligible: impl Fn(&Host<F>, &Job<F>) -> bool,
    ) -> Result<HostId, Error> {
        if self.locations.contains_key(&job.id) {
            return Err(Error::DuplicateJob);
        }
        if job.resources.cpu == Cpu::ZERO && job.resources.memory == Memory::ZERO {
            return Err(Error::InvalidRequest);
        }
        if job.started_at > now {
            return Err(Error::FutureJob);
        }
        self.tick(now)?;
        let remaining = self
            .predictor
            .remaining(&job.features, now - job.started_at);
        let class = LifetimeClass::of(remaining);
        let target = self
            .hosts
            .values()
            .filter(|h| h.schedulable && job.resources.fits(h.free()) && eligible(h, &job))
            .min_by_key(|h| self.score(h, &job, class, remaining, now))
            .map(|h| h.id)
            .ok_or(Error::NoCapacity)?;
        let host = self.hosts.get_mut(&target).unwrap();
        if host.state == HostState::Empty {
            host.state = HostState::Open;
            host.assign_class(class, now);
        }
        self.locations.insert(job.id, target);
        host.jobs.insert(job.id, job);
        let used = host.used();
        if host.state == HostState::Open
            && (u128::from(used.cpu.as_millicores()) * 10 > u128::from(host.capacity.cpu.as_millicores()) * 9
                || u128::from(used.memory.as_bytes()) * 10 > u128::from(host.capacity.memory.as_bytes()) * 9)
        {
            host.state = HostState::Recycling;
            host.residual = host.jobs.keys().copied().collect();
        }
        Ok(target)
    }
    fn score(
        &self,
        host: &Host<F>,
        job: &Job<F>,
        class: LifetimeClass,
        remaining: Duration,
        now: Instant,
    ) -> (u8, u8, usize, u128, HostId) {
        let (tier, distance) = match (host.state, host.class) {
            (HostState::Recycling, Some(c)) if c > class => (0, c.index() - class.index()),
            (HostState::Open, Some(c)) if c == class => (1, 0),
            (HostState::Empty, _) => (3, 0),
            _ => (2, 0), // Algorithm 3 explicitly permits non-matching fallback.
        };
        let host_remaining = host
            .jobs
            .values()
            .map(|v| self.predictor.remaining(&v.features, now - v.started_at))
            .max()
            .unwrap_or(Duration::ZERO);
        let temporal = temporal_cost(remaining.saturating_sub(host_remaining));
        let free = host.free();
        // Normalized CPU+memory slack in millionths, lower is tighter packing.
        let waste = u128::from(free.cpu.as_millicores() - job.resources.cpu.as_millicores()) * 1_000_000
            / u128::from(host.capacity.cpu.as_millicores())
            + u128::from(free.memory.as_bytes() - job.resources.memory.as_bytes()) * 1_000_000
                / u128::from(host.capacity.memory.as_bytes());
        (tier, distance, temporal, waste, host.id)
    }
    /// A job has exited: take it off its host and return it. Exits are events the
    /// caller reports, never inferred from a prediction.
    ///
    /// The job leaves the host's residual set before the host is refreshed, so an
    /// exit at the moment of a deadline counts as an exit and not as a timeout.
    /// [`Error::UnknownJob`] if it is not placed.
    pub fn remove(&mut self, id: JobId, now: Instant) -> Result<Job<F>, Error> {
        let host_id = self.location(id).ok_or(Error::UnknownJob)?;
        if now < self.now {
            return Err(Error::ClockWentBackwards);
        }
        // Remove before refresh so a natural exit at a deadline wins over a
        // timeout and the residual generation is not accidentally replaced.
        let host = self.hosts.get_mut(&host_id).unwrap();
        let job = host.jobs.remove(&id).unwrap();
        host.residual.remove(&id);
        host.refresh(now);
        self.locations.remove(&id);
        self.tick(now)?;
        Ok(job)
    }
    /// LARS approval gate and longest-remaining-first snapshot. The caller
    /// performs migrations one at a time and skips jobs that have since exited.
    /// Approval must cover every resident job before scheduling is disabled.
    ///
    /// The order is the paper's (§4.4): the job with the longest predicted remaining
    /// lifetime first, so shorter-lived jobs may exit while the long ones are
    /// moving. Ties go to the lower id. Each job is then placed again with
    /// [`place`](Self::place), the same algorithm as for a new job. The approval
    /// gate is this port's, not the paper's: `approved` says whether a job may be
    /// migrated at all, and a single refusal leaves the host untouched.
    ///
    /// [`Error::UnknownHost`] if there is no such host.
    pub fn begin_drain(
        &mut self,
        id: HostId,
        now: Instant,
        approved: impl Fn(&Job<F>) -> bool,
    ) -> Result<Vec<JobId>, Error> {
        let host = self.hosts.get(&id).ok_or(Error::UnknownHost)?;
        if !host.jobs.values().all(approved) {
            return Err(Error::MigrationNotApproved);
        }
        self.tick(now)?;
        let host = self.hosts.get_mut(&id).unwrap();
        let mut order: Vec<_> = host
            .jobs
            .values()
            .map(|v| {
                (
                    self.predictor.remaining(&v.features, now - v.started_at),
                    v.id,
                )
            })
            .collect();
        order.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        host.schedulable = false;
        Ok(order.into_iter().map(|(_, id)| id).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::LifetimeClass::{Lc1, Lc2, Lc3, Lc4, LcForever};
    use super::*;

    const H: u64 = HOUR;

    /// The paper's classes (§4.3) and their edges, and the one beyond them: a lower
    /// edge belongs to the class it starts, and nothing is left without one.
    #[test]
    fn the_papers_four_classes_and_their_edges() {
        let of = LifetimeClass::of;
        assert_eq!(of(Duration::ZERO), Lc1);
        assert_eq!(of(Duration::from_secs(H - 1)), Lc1);
        assert_eq!(of(hours(1)), Lc2);
        assert_eq!(of(Duration::from_secs(10 * H - 1)), Lc2);
        assert_eq!(of(hours(10)), Lc3);
        assert_eq!(of(Duration::from_secs(100 * H - 1)), Lc3);
        assert_eq!(of(hours(100)), Lc4);
        assert_eq!(of(Duration::from_secs(1000 * H - 1)), Lc4);
        // The paper stops at 1000 hours; this port's LcForever starts there.
        assert_eq!(of(hours(1000)), LcForever);
        assert_eq!(of(hours(100_000)), LcForever);
        assert_eq!(of(Duration::MAX), LcForever);
    }

    #[test]
    fn classes_are_ordered_shortest_first_and_move_one_step_at_a_time() {
        let all = [Lc1, Lc2, Lc3, Lc4, LcForever];
        assert!(all.windows(2).all(|pair| pair[0] < pair[1]));
        assert_eq!(all.map(LifetimeClass::index), [0, 1, 2, 3, 4]);
        assert_eq!(
            all.map(LifetimeClass::higher),
            [Lc2, Lc3, Lc4, LcForever, LcForever]
        );
        assert_eq!(all.map(LifetimeClass::lower), [Lc1, Lc1, Lc2, Lc3, Lc4]);
    }

    /// The end of each range is the next one's start, and the last has no end.
    #[test]
    fn upper_bounds_are_one_ten_a_hundred_a_thousand_hours_and_then_none() {
        assert_eq!(
            [Lc1, Lc2, Lc3, Lc4, LcForever].map(LifetimeClass::upper_bound),
            [hours(1), hours(10), hours(100), hours(1000), Duration::MAX]
        );
    }

    /// `of` and `range` agree: every class takes exactly the remaining lifetimes in
    /// its range, edges included, and the ranges tile with no gap and no overlap.
    #[test]
    fn of_and_range_agree_and_the_ranges_tile() {
        let classes = [Lc1, Lc2, Lc3, Lc4, LcForever];
        for class in classes {
            let range = class.range();
            assert_eq!(LifetimeClass::of(range.start), class);
            assert_eq!(
                LifetimeClass::of(range.end - Duration::from_nanos(1)),
                class
            );
        }
        for pair in classes.windows(2) {
            assert_eq!(pair[0].range().end, pair[1].range().start);
        }
        assert_eq!(Lc1.range().start, Duration::ZERO);
        // The last class is open-ended: it holds lifetimes far past the paper's 1000 hours.
        assert!(LcForever.range().contains(&hours(100_000)));
        // `From` is the same range.
        let range: Range<Duration> = Lc2.into();
        assert_eq!(range, Lc2.range());
    }

    /// One job, predicted to live `predicted` more, placed on an empty host at time
    /// zero.
    fn scheduler_with_one_job(
        predicted: Duration,
    ) -> Scheduler<EmpiricalLifetime, EmpiricalPredictor> {
        let mut scheduler = Scheduler::new(EmpiricalPredictor);
        let capacity = Resources {
            cpu: Cpu::millicores(100),
            memory: Memory::bytes(100),
        };
        scheduler.add_host(1, capacity).unwrap();
        let job = Job {
            id: 7,
            resources: Resources {
                cpu: Cpu::millicores(1),
                memory: Memory::bytes(1),
            },
            started_at: Instant::EPOCH,
            features: EmpiricalLifetime::new(vec![predicted], hours(1)).unwrap(),
        };
        scheduler.place(job, Instant::EPOCH).unwrap();
        scheduler
    }

    /// LcForever has nowhere to be promoted to and no upper bound, so a host in it
    /// never times out: however far the clock goes, its jobs do not become residual.
    #[test]
    fn a_host_in_lc_forever_never_times_out() {
        let mut scheduler = scheduler_with_one_job(hours(5000));
        let host = scheduler.host(1).unwrap();
        assert_eq!(host.class(), Some(LcForever));
        assert_eq!(host.deadline(), Some(Instant::MAX));

        scheduler.tick(Instant::from_epoch(hours(1_000_000))).unwrap();
        let host = scheduler.host(1).unwrap();
        assert_eq!(host.class(), Some(LcForever));
        assert!(
            host.residual().is_empty(),
            "a timeout would have made the job residual"
        );
    }

    /// An LC4 host keeps the paper's timeout, 1.1 times its class's bound, and is
    /// promoted to LcForever when it passes it, its jobs becoming residual.
    #[test]
    fn an_lc4_host_times_out_at_1100_hours_and_is_promoted() {
        let mut scheduler = scheduler_with_one_job(hours(500));
        let host = scheduler.host(1).unwrap();
        assert_eq!(host.class(), Some(Lc4));
        assert_eq!(host.deadline(), Some(Instant::from_epoch(hours(1100))));

        scheduler.tick(Instant::from_epoch(hours(1099))).unwrap();
        assert_eq!(scheduler.host(1).unwrap().class(), Some(Lc4));
        assert!(scheduler.host(1).unwrap().residual().is_empty());

        scheduler.tick(Instant::from_epoch(hours(1100))).unwrap();
        let host = scheduler.host(1).unwrap();
        assert_eq!(host.class(), Some(LcForever));
        assert_eq!(host.residual().iter().copied().collect::<Vec<_>>(), [7]);
        assert_eq!(host.deadline(), Some(Instant::MAX));
    }

    /// §4.2's own example: a 70-minute extension has temporal cost 2.
    #[test]
    fn seventy_minutes_costs_two() {
        assert_eq!(temporal_cost(Duration::from_secs(70 * 60)), 2);
        assert_eq!(temporal_cost(Duration::ZERO), 0);
    }

    /// A job on an empty host opens it, gives it the job's class, and sets its
    /// timeout at 1.1 times the class's upper bound (this port's choice, §4.3).
    #[test]
    fn a_job_on_an_empty_host_opens_it_with_its_class_and_a_deadline() {
        let mut scheduler = Scheduler::new(EmpiricalPredictor);
        let capacity = Resources {
            cpu: Cpu::millicores(100),
            memory: Memory::bytes(100),
        };
        scheduler.add_host(1, capacity).unwrap();

        let job = Job {
            id: 7,
            resources: Resources {
                cpu: Cpu::millicores(1),
                memory: Memory::bytes(1),
            },
            started_at: Instant::EPOCH,
            // Predicted to live two more hours: LC2.
            features: EmpiricalLifetime::new(vec![hours(2)], hours(1)).unwrap(),
        };
        assert_eq!(scheduler.place(job, Instant::EPOCH), Ok(1));

        let host = scheduler.host(1).unwrap();
        assert_eq!(host.state(), HostState::Open);
        assert_eq!(host.class(), Some(Lc2));
        assert_eq!(host.deadline(), Some(Instant::from_epoch(hours(11))));
        assert_eq!(scheduler.location(7), Some(1));
    }
}
