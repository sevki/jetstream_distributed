//! LAVA placement (§4.3), NILAS scoring (§4.2), and LARS ordering (§4.4).
//!
//! Time is caller-supplied, monotonic integer seconds. Exits are explicit events;
//! a predicted expiry never removes a VM. See README for paper ambiguities and
//! concrete policy choices. No model, runtime, or network service is required.
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use crate::{
    compute::{ComputerId, Job, Resources},
    host::HostId,
};

/// Seconds in an hour: the first lifetime class's upper bound.
const HOUR: u64 = 3600;

// Time is a `Duration` since an epoch the caller chooses, not an `Instant`: an
// `Instant` can only be made by reading the clock, which would put the clock back
// inside a scheduler that takes its time from outside.

/// LC1 is index 0 (<1h), LC2 index 1 ([1h,10h)), etc.
/// Decade classes extend beyond the paper's four example classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LifetimeClass(u8);
impl LifetimeClass {
    /// The class of a VM predicted to live `remaining` longer: the first class
    /// whose [`upper_bound`](Self::upper_bound) is above it. Index 16 is the last
    /// class and takes everything longer.
    pub fn of(remaining: Duration) -> Self {
        let mut class = Self(0);
        while remaining >= class.upper_bound() && class.0 < 16 {
            class.0 += 1;
        }
        class
    }
    /// The class's index: 0 for LC1 (under an hour), 1 for LC2, and so on.
    pub fn index(self) -> u8 {
        self.0
    }
    /// The exclusive upper bound of the class: one hour times ten to the power of
    /// its index, saturating at `u64::MAX` seconds.
    pub fn upper_bound(self) -> Duration {
        Duration::from_secs(HOUR.saturating_mul(10_u64.saturating_pow(u32::from(self.0))))
    }
    fn higher(self) -> Self {
        Self((self.0 + 1).min(16))
    }
    fn lower(self) -> Self {
        Self(self.0.saturating_sub(1))
    }
}

/// Adapter point for a trained uptime-conditioned regression/survival model.
/// Returned values are *remaining* lifetime, never total lifetime or exit time.
pub trait LifetimePredictor<F> {
    /// The expected remaining lifetime of a VM with `features` that has already
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
    /// It is the caller's choice: the data says nothing about a VM that has
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
    /// No VMs, and no lifetime class. A new VM may start here as a last resort.
    Empty,
    /// Filling up. It takes only VMs of its own lifetime class.
    Open,
    /// Over 90% of its CPU or memory is used, so it only drains: it takes VMs at
    /// least one class lower than its own, which should be gone before it is.
    Recycling,
}

/// A host and the VMs on it, with the lifetime class LAVA has given it.
///
/// It is a view: only the [`Scheduler`] changes one.
#[derive(Debug, Clone)]
pub struct Host<F> {
    id: HostId,
    capacity: Resources,
    vms: BTreeMap<ComputerId, Job<F>>,
    state: HostState,
    class: Option<LifetimeClass>,
    deadline: Option<Duration>,
    residual: BTreeSet<ComputerId>,
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
    /// The VMs on the host, in order of id.
    pub fn vms(&self) -> impl Iterator<Item = &Job<F>> {
        self.vms.values()
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
    /// `None` while it is empty. The paper does not give the timeout; see
    /// [`Scheduler`] for the one used here.
    pub fn deadline(&self) -> Option<Duration> {
        self.deadline
    }
    /// The VMs that were on the host at its last class change: when the host
    /// became recycling, was demoted, or was promoted (§4.3). When the last of
    /// them exits, a recycling host drops a class.
    pub fn residual(&self) -> &BTreeSet<ComputerId> {
        &self.residual
    }
    /// Whether new VMs may be placed on the host. It is off while the host is
    /// being drained (LARS, §4.4) or under maintenance.
    pub fn schedulable(&self) -> bool {
        self.schedulable
    }
    /// The CPU and memory the VMs on the host use together.
    pub fn used(&self) -> Resources {
        self.vms
            .values()
            .fold(Resources { cpu: 0, memory: 0 }, |r, vm| Resources {
                cpu: r.cpu + vm.resources.cpu,
                memory: r.memory + vm.resources.memory,
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
    fn assign_class(&mut self, class: LifetimeClass, now: Duration) {
        self.class = Some(class);
        // The paper leaves the precise timeout unspecified. Use 1.1x the
        // class upper bound, anchored at each assignment, with saturation.
        let upper = class.upper_bound();
        self.deadline = Some(now.saturating_add(upper.saturating_add(upper / 10)));
    }
    fn refresh(&mut self, now: Duration) {
        if self.vms.is_empty() {
            self.reset();
            return;
        }
        if self.state == HostState::Recycling && self.residual.is_empty() {
            self.assign_class(self.class.unwrap().lower(), now);
            self.residual = self.vms.keys().copied().collect();
        }
        // One promotion per refresh, rather than inventing transitions through
        // unobserved intermediate epochs when the caller advances a long time.
        if self
            .deadline
            .is_some_and(|d| d != Duration::MAX && now >= d)
        {
            self.assign_class(self.class.unwrap().higher(), now);
            self.residual = self.vms.keys().copied().collect();
        }
    }
}

/// Why a [`Scheduler`] or [`EmpiricalLifetime`] call was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// Invalid capacity: a host was added with no CPU or no memory.
    InvalidCapacity,
    /// Invalid request: a VM asked for no CPU and no memory.
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
    /// No capacity: no schedulable, eligible host has room for the VM.
    NoCapacity,
    /// Migration not approved: [`Scheduler::begin_drain`] was refused because the approval gate did not
    /// cover every VM on the host.
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
/// A VM is placed on the first host that exists in this order (§4.3, Algorithm
/// 3): a recycling host of a higher class than the VM's, the nearest class first;
/// an open host of the VM's own class; any other host that has VMs; an empty host.
/// Among hosts of the same kind the choice is NILAS (§4.2): the lowest temporal
/// cost, then the least wasted CPU and memory, then the lowest host id.
///
/// Where the paper leaves a choice open this makes one:
/// * a host's promotion deadline is 1.1 times its class's upper bound after the
///   class was assigned (the paper says a host's lifetime should stay within 1.1
///   times its class, but not the timeout);
/// * a host is promoted at most one class each time the clock advances, however
///   far it advances.
pub struct Scheduler<F, P> {
    predictor: P,
    hosts: BTreeMap<HostId, Host<F>>,
    locations: BTreeMap<ComputerId, HostId>,
    now: Duration,
}

impl<F, P: LifetimePredictor<F>> Scheduler<F, P> {
    /// A scheduler with no hosts, whose clock starts at zero, that asks
    /// `predictor` how long each VM has left.
    pub fn new(predictor: P) -> Self {
        Self {
            predictor,
            hosts: BTreeMap::new(),
            locations: BTreeMap::new(),
            now: Duration::ZERO,
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
    /// The host a VM is on, if it is placed.
    pub fn location(&self, vm: ComputerId) -> Option<HostId> {
        self.locations.get(&vm).copied()
    }
    /// Add an empty, schedulable host. [`Error::InvalidCapacity`] if it has no
    /// CPU or no memory, [`Error::DuplicateHost`] if the id is taken.
    pub fn add_host(&mut self, id: HostId, capacity: Resources) -> Result<(), Error> {
        if capacity.cpu == 0 || capacity.memory == 0 {
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
                vms: BTreeMap::new(),
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
    /// class, a recycling host whose residual VMs have all gone drops a class, and
    /// a host past its deadline is promoted one class (§4.3).
    ///
    /// Time only moves forward: [`Error::ClockWentBackwards`] if `now` is earlier
    /// than a time already given. A predicted exit never removes a VM; only
    /// [`remove`](Self::remove) does.
    pub fn tick(&mut self, now: Duration) -> Result<(), Error> {
        if now < self.now {
            return Err(Error::ClockWentBackwards);
        }
        self.now = now;
        for host in self.hosts.values_mut() {
            host.refresh(now);
        }
        Ok(())
    }
    /// Allow or forbid placing new VMs on a host, independently of its life cycle.
    /// [`begin_drain`](Self::begin_drain) turns it off, and maintenance may too.
    /// [`Error::UnknownHost`] if there is no such host.
    pub fn set_schedulable(&mut self, id: HostId, value: bool) -> Result<(), Error> {
        self.hosts
            .get_mut(&id)
            .ok_or(Error::UnknownHost)?
            .schedulable = value;
        Ok(())
    }
    /// Place a VM on the best host, at `now`, and return the host's id. Every
    /// schedulable host with room is a candidate; see
    /// [`place_with`](Self::place_with) to restrict them.
    pub fn place(&mut self, job: Job<F>, now: Duration) -> Result<HostId, Error> {
        self.place_with(job, now, |_, _| true)
    }
    /// As [`place`](Self::place), but only on hosts `eligible` accepts: a hard
    /// constraint LAVA knows nothing about, such as a zone or an anti-affinity rule.
    ///
    /// The VM's class comes from its predicted remaining lifetime at `now`. A VM
    /// placed on an empty host gives the host that class and makes it open; a host
    /// that goes over 90% of its CPU or memory becomes recycling, and the VMs on it
    /// at that moment become its residual set.
    ///
    /// [`Error::DuplicateJob`], [`Error::InvalidRequest`], [`Error::FutureJob`],
    /// [`Error::ClockWentBackwards`] for a bad request, and [`Error::NoCapacity`]
    /// if no candidate has room.
    pub fn place_with(
        &mut self,
        job: Job<F>,
        now: Duration,
        eligible: impl Fn(&Host<F>, &Job<F>) -> bool,
    ) -> Result<HostId, Error> {
        if self.locations.contains_key(&job.id) {
            return Err(Error::DuplicateJob);
        }
        if job.resources.cpu == 0 && job.resources.memory == 0 {
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
        host.vms.insert(job.id, job);
        let used = host.used();
        if host.state == HostState::Open
            && (u128::from(used.cpu) * 10 > u128::from(host.capacity.cpu) * 9
                || u128::from(used.memory) * 10 > u128::from(host.capacity.memory) * 9)
        {
            host.state = HostState::Recycling;
            host.residual = host.vms.keys().copied().collect();
        }
        Ok(target)
    }
    fn score(
        &self,
        host: &Host<F>,
        job: &Job<F>,
        class: LifetimeClass,
        remaining: Duration,
        now: Duration,
    ) -> (u8, u8, usize, u128, HostId) {
        let (tier, distance) = match (host.state, host.class) {
            (HostState::Recycling, Some(c)) if c > class => (0, c.0 - class.0),
            (HostState::Open, Some(c)) if c == class => (1, 0),
            (HostState::Empty, _) => (3, 0),
            _ => (2, 0), // Algorithm 3 explicitly permits non-matching fallback.
        };
        let host_remaining = host
            .vms
            .values()
            .map(|v| self.predictor.remaining(&v.features, now - v.started_at))
            .max()
            .unwrap_or(Duration::ZERO);
        let temporal = temporal_cost(remaining.saturating_sub(host_remaining));
        let free = host.free();
        // Normalized CPU+memory slack in millionths, lower is tighter packing.
        let waste = u128::from(free.cpu - job.resources.cpu) * 1_000_000
            / u128::from(host.capacity.cpu)
            + u128::from(free.memory - job.resources.memory) * 1_000_000
                / u128::from(host.capacity.memory);
        (tier, distance, temporal, waste, host.id)
    }
    /// A VM has exited: take it off its host and return it. Exits are events the
    /// caller reports, never inferred from a prediction.
    ///
    /// The VM leaves the host's residual set before the host is refreshed, so an
    /// exit at the moment of a deadline counts as an exit and not as a timeout.
    /// [`Error::UnknownJob`] if it is not placed.
    pub fn remove(&mut self, id: ComputerId, now: Duration) -> Result<Job<F>, Error> {
        let host_id = self.location(id).ok_or(Error::UnknownJob)?;
        if now < self.now {
            return Err(Error::ClockWentBackwards);
        }
        // Remove before refresh so a natural exit at a deadline wins over a
        // timeout and the residual generation is not accidentally replaced.
        let host = self.hosts.get_mut(&host_id).unwrap();
        let vm = host.vms.remove(&id).unwrap();
        host.residual.remove(&id);
        host.refresh(now);
        self.locations.remove(&id);
        self.tick(now)?;
        Ok(vm)
    }
    /// LARS approval gate and longest-remaining-first snapshot. The caller
    /// performs migrations one at a time and skips VMs that have since exited.
    /// Approval must cover every resident VM before scheduling is disabled.
    ///
    /// The order is the paper's (§4.4): the VM with the longest predicted remaining
    /// lifetime first, so shorter-lived VMs may exit while the long ones are
    /// moving. Ties go to the lower id. Each VM is then placed again with
    /// [`place`](Self::place), the same algorithm as for a new VM. The approval
    /// gate is this port's, not the paper's: `approved` says whether a VM may be
    /// migrated at all, and a single refusal leaves the host untouched.
    ///
    /// [`Error::UnknownHost`] if there is no such host.
    pub fn begin_drain(
        &mut self,
        id: HostId,
        now: Duration,
        approved: impl Fn(&Job<F>) -> bool,
    ) -> Result<Vec<ComputerId>, Error> {
        let host = self.hosts.get(&id).ok_or(Error::UnknownHost)?;
        if !host.vms.values().all(approved) {
            return Err(Error::MigrationNotApproved);
        }
        self.tick(now)?;
        let host = self.hosts.get_mut(&id).unwrap();
        let mut order: Vec<_> = host
            .vms
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
