//! Prequal is an implementation of the paper "Load is not what you should balance:
//! Introducing Prequal" <https://www.usenix.org/system/files/nsdi24-wydrowski.pdf>
//! (NSDI '24).
//!
//! Prequal picks which replica gets a request. It does not balance load; it asks a
//! few replicas how they are doing, keeps the answers, and sends each request to
//! the replica that looks best **now**, by the *hot-cold lexicographic* rule:
//!
//! * a replica answers a **probe** with its requests in flight (RIF) and an
//!   estimate of the latency a request would see at that RIF ([`Load`]);
//! * the client keeps a small **pool** of recent answers, probing a few random
//!   replicas on every request and again when it has been idle ([`Prequal`]);
//! * to pick, it calls a probe **hot** if its RIF is above a quantile of the RIF
//!   across the pool, and **cold** otherwise. If every probe is hot it takes the
//!   lowest RIF; otherwise the cold probe with the lowest latency.
//!
//! # What this is, and is not
//!
//! Everything here is a decision: no sockets, no clock, no thread. A caller holds
//! a [`Prequal`], hands it the time and the set of replicas, and gets back who to
//! send to and who to probe; it sends the probes itself and hands the answers
//! back. Time is [`Instant`], so a test drives it, and randomness is a [`Random`]
//! the caller supplies, so a run replays from a seed. The module is in the
//! dependency-free build for the same reason.
//!
//! It is plain Rust, not verified, and the tests are the evidence.
//!
//! # Where this departs from the paper, or fills a gap
//!
//! The paper leaves these open and this makes a choice; each is stated where it is
//! made.
//!
//! * **One probe per replica in the pool.** A newer answer from a replica replaces
//!   the older one, so a replica is not counted twice.
//! * **"At or near" the current RIF** (the latency estimate) is: the samples taken
//!   at exactly the current RIF, or if there are none, at the nearest RIF there
//!   are samples for.
//! * **Ties** are broken by the other signal, then by age.
//! * **Sinkholing is not handled.** A replica that fails fast looks idle and
//!   attracts traffic; the paper leaves its heuristics out and so does this.

use std::collections::VecDeque;
use std::fmt;
use std::time::Duration;

use crate::compute::Instant;
use crate::id::Id;

/// Where randomness comes from.
///
/// The caller supplies it so that a run can be replayed: [`SplitMix64`] from a
/// seed is enough for tests and for a service that does not care to do better.
pub trait Random {
    /// The next 64 random bits.
    fn next_u64(&mut self) -> u64;

    /// A number below `bound`, which must not be 0. The tiny bias of taking a
    /// remainder is nothing next to the sizes this is used for.
    fn below(&mut self, bound: u32) -> u32 {
        // `bound` is non-zero, and the remainder fits a `u32` because it is
        // smaller than `bound`.
        (self.next_u64() % u64::from(bound)) as u32
    }

    /// A number in `[0, 1)`.
    fn unit(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// SplitMix64: a 64-bit generator that is small, fast and passes the usual tests.
/// Not for secrets.
#[derive(Debug, Clone)]
pub struct SplitMix64(u64);

impl SplitMix64 {
    /// A generator that starts from `seed`.
    pub const fn new(seed: u64) -> Self {
        SplitMix64(seed)
    }
}

impl Random for SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// What a configuration got wrong.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConfigError {
    /// The pool must hold at least one probe.
    EmptyPool,
    /// A rate (`probes_per_query`, `removals_per_query`, `delta`) is negative, or
    /// not a number.
    BadRate,
    /// `probes_per_query` is 0: nothing would ever fill the pool.
    NoProbing,
    /// The RIF quantile is not in `[0, 1]`.
    BadQuantile,
    /// The RIF history must hold at least one response.
    EmptyHistory,
}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ConfigError::EmptyPool => "the probe pool must hold at least one probe",
            ConfigError::BadRate => "a rate must be a number that is not negative",
            ConfigError::NoProbing => "the probing rate is 0, so the pool would never fill",
            ConfigError::BadQuantile => "the RIF quantile must be in [0, 1]",
            ConfigError::EmptyHistory => "the RIF history must hold at least one response",
        })
    }
}

impl std::error::Error for ConfigError {}

/// The knobs, with the paper's testbed values as the default.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Config {
    /// The most probes the pool holds. The paper: 16 "suffices".
    pub pool_size: u32,
    /// `r_probe`: probes sent per request. May be fractional; the long-run average
    /// is exactly this. The paper: performance holds until it falls below about 1.
    pub probes_per_query: f64,
    /// `r_remove`: probes removed per request, alternating the oldest and the worst.
    pub removals_per_query: f64,
    /// `Q_RIF`: a probe is hot if its RIF is above this quantile of the pool's
    /// RIFs. The paper suggests `[0.6, 0.9]`, and 0 (RIF alone) still works.
    pub hot_quantile: f64,
    /// A probe older than this is dropped. The paper's testbed: 1 second.
    pub max_age: Duration,
    /// After this long without a request, [`Prequal::idle`] asks for fresh probes,
    /// so the pool is not stale when the next request comes. The paper gives no
    /// value; this is a choice.
    pub max_idle: Duration,
    /// `δ`, the pool's net drift in the reuse formula. The paper: 1.
    pub delta: f64,
    /// How many probe responses the RIF distribution is estimated from. The paper
    /// says "recent probe responses" and no number. It has to be wider than the
    /// pool: measured against the pool alone, the lowest RIF in it is never above
    /// the quantile, so "every probe is hot" could not happen.
    pub rif_history: u32,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            pool_size: 16,
            probes_per_query: 3.0,
            removals_per_query: 1.0,
            hot_quantile: 0.84,
            max_age: Duration::from_secs(1),
            max_idle: Duration::from_millis(250),
            delta: 1.0,
            rif_history: 128,
        }
    }
}

impl Config {
    /// Check the knobs make sense together.
    pub fn validate(&self) -> Result<(), ConfigError> {
        if self.pool_size == 0 {
            return Err(ConfigError::EmptyPool);
        }
        let rates = [self.probes_per_query, self.removals_per_query, self.delta];
        if rates.iter().any(|r| !r.is_finite() || *r < 0.0) {
            return Err(ConfigError::BadRate);
        }
        if self.probes_per_query == 0.0 {
            return Err(ConfigError::NoProbing);
        }
        if !(0.0..=1.0).contains(&self.hot_quantile) {
            return Err(ConfigError::BadQuantile);
        }
        if self.rif_history == 0 {
            return Err(ConfigError::EmptyHistory);
        }
        Ok(())
    }

    /// `b_reuse`: how many requests one probe may serve before it is removed,
    /// given `replicas` to choose among.
    ///
    /// `max{1, (1 + δ) / ((1 − m/n)·r_probe − r_remove)}`, with `m` the pool size
    /// and `n` the replica count. Where the denominator is not positive, removals
    /// outpace probing and no finite budget keeps the pool from draining, so the
    /// budget is unlimited and only age and the removal rule retire a probe.
    pub fn reuse_budget(&self, replicas: u32) -> f64 {
        if replicas == 0 {
            return f64::INFINITY;
        }
        let m = f64::from(self.pool_size);
        let n = f64::from(replicas);
        let net = (1.0 - m / n) * self.probes_per_query - self.removals_per_query;
        if net <= 0.0 {
            return f64::INFINITY;
        }
        ((1.0 + self.delta) / net).max(1.0)
    }
}

/// A replica's answer to a probe.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reading {
    /// Requests in flight at the replica.
    pub rif: u32,
    /// The latency a request would see at that RIF: the median of recent requests
    /// that arrived at about it.
    pub latency: Duration,
}

/// One answer, as the pool keeps it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Probe {
    /// Who answered.
    pub replica: Id,
    /// What it said. The RIF is bumped by one each time this client sends the
    /// replica a request on the strength of it, since the replica cannot yet have
    /// counted the request; the latency is left as it was, as the paper does.
    pub reading: Reading,
    /// When the answer arrived. Arrival and not departure, so no clock but ours.
    pub received_at: Instant,
    /// How many requests this probe has served.
    pub uses: u32,
}

/// What [`Prequal::query`] decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decision {
    /// Where to send the request.
    pub replica: Id,
    /// Whom to probe now, and hand the answers to [`Prequal::probed`].
    pub probe: Vec<Id>,
}

/// The time between `then` and `now`, none if `then` is later.
fn since(now: Instant, then: Instant) -> Duration {
    if then > now {
        Duration::ZERO
    } else {
        now - then
    }
}

/// A client's balancer: the probe pool and the rules that use it.
#[derive(Debug, Clone)]
pub struct Prequal<R> {
    config: Config,
    rng: R,
    /// Oldest first.
    pool: Vec<Probe>,
    /// Fractions of a probe owed, so a fractional rate averages out exactly.
    probe_owed: f64,
    remove_owed: f64,
    /// Whether the next removal takes the oldest probe (else the worst).
    remove_oldest: bool,
    /// When this client last probed, for [`Prequal::idle`].
    last_probe: Option<Instant>,
    /// The RIFs of the last probe responses, whether or not their probes are still
    /// in the pool: the distribution "hot" is measured against.
    history: VecDeque<u32>,
}

impl<R: Random> Prequal<R> {
    /// A balancer with an empty pool.
    pub fn new(config: Config, rng: R) -> Result<Self, ConfigError> {
        config.validate()?;
        Ok(Prequal {
            config,
            rng,
            pool: Vec::new(),
            probe_owed: 0.0,
            remove_owed: 0.0,
            remove_oldest: true,
            last_probe: None,
            history: VecDeque::new(),
        })
    }

    /// The probes held now, oldest first.
    pub fn pool(&self) -> &[Probe] {
        &self.pool
    }

    /// Choose where `now` sends a request among `replicas`, and whom to probe.
    ///
    /// `None` only if there are no replicas. With fewer than two probes held the
    /// choice is a uniformly random replica, as the paper suggests: one probe is
    /// not a comparison.
    pub fn query(&mut self, now: Instant, replicas: &[Id]) -> Option<Decision> {
        if replicas.is_empty() {
            return None;
        }
        // Forget what is stale, or about a replica that has gone.
        let max_age = self.config.max_age;
        self.pool
            .retain(|p| since(now, p.received_at) <= max_age && replicas.contains(&p.replica));

        let replica = match self.select() {
            Some(index) => self.use_probe(index, replicas.len() as u32),
            None => replicas[self.rng.below(replicas.len() as u32) as usize],
        };
        let removals = self.owed(Owed::Remove);
        self.remove(removals);

        let probes = self.owed(Owed::Probe);
        let probe = self.sample(replicas, probes);
        if !probe.is_empty() {
            self.last_probe = Some(now);
        }
        Some(Decision { replica, probe })
    }

    /// File a replica's answer to a probe.
    ///
    /// A replica has one probe in the pool: this replaces any older one from it.
    /// When the pool is full the oldest probe makes room.
    pub fn probed(&mut self, now: Instant, replica: Id, reading: Reading) {
        self.history.push_back(reading.rif);
        while self.history.len() as u32 > self.config.rif_history {
            self.history.pop_front();
        }
        self.pool.retain(|p| p.replica != replica);
        while self.pool.len() as u32 >= self.config.pool_size {
            self.pool.remove(0);
        }
        self.pool.push(Probe {
            replica,
            reading,
            received_at: now,
            uses: 0,
        });
    }

    /// Whom to probe because nothing has asked for a while.
    ///
    /// Empty unless it has been [`Config::max_idle`] since this client last
    /// probed. A caller with sparse traffic calls this on a timer, so the first
    /// request after a quiet spell finds a pool that is not stale.
    pub fn idle(&mut self, now: Instant, replicas: &[Id]) -> Vec<Id> {
        if replicas.is_empty() {
            return Vec::new();
        }
        let quiet = match self.last_probe {
            Some(last) => since(now, last) >= self.config.max_idle,
            None => true,
        };
        if !quiet {
            return Vec::new();
        }
        let max_age = self.config.max_age;
        self.pool.retain(|p| since(now, p.received_at) <= max_age);
        let probes = self.owed(Owed::Probe).max(1);
        let probe = self.sample(replicas, probes);
        self.last_probe = Some(now);
        probe
    }

    /// The RIF above which a probe is hot: the `hot_quantile` of the pool's RIFs,
    /// interpolated between the two nearest when it falls between them.
    ///
    /// Interpolated, not the nearest rank: the nearest rank of a small pool is its
    /// largest RIF, which nothing can exceed, so no probe would ever be hot until
    /// the pool held enough that `1 − q` of it is a whole probe.
    fn hot_threshold(&self) -> Option<f64> {
        if self.pool.is_empty() {
            return None;
        }
        let mut rifs: Vec<u32> = self.history.iter().copied().collect();
        rifs.sort_unstable();
        let position = self.config.hot_quantile * (rifs.len() - 1) as f64;
        let low = position.floor() as usize;
        let high = position.ceil() as usize;
        let (low_rif, high_rif) = (f64::from(rifs[low]), f64::from(rifs[high]));
        Some(low_rif + (position - low as f64) * (high_rif - low_rif))
    }

    /// The hot-cold lexicographic choice: the index of the probe to use.
    fn select(&self) -> Option<usize> {
        if self.pool.len() < 2 {
            return None;
        }
        let threshold = self.hot_threshold()?;
        let cold = |p: &Probe| f64::from(p.reading.rif) <= threshold;
        let best = |by: &dyn Fn(&Probe) -> (u64, u64)| {
            self.pool
                .iter()
                .enumerate()
                .filter(|(_, p)| cold(p) || self.pool.iter().all(|q| !cold(q)))
                .min_by_key(|(i, p)| (by(p), *i))
                .map(|(i, _)| i)
        };
        if self.pool.iter().any(cold) {
            // Some are cold: the lowest latency among them, then the lowest RIF.
            best(&|p| (p.reading.latency.as_nanos() as u64, u64::from(p.reading.rif)))
        } else {
            // All are hot: the lowest RIF, then the lowest latency.
            best(&|p| (u64::from(p.reading.rif), p.reading.latency.as_nanos() as u64))
        }
    }

    /// Send a request on the strength of `pool[index]`: count it, and retire the
    /// probe once it has served its budget.
    fn use_probe(&mut self, index: usize, replicas: u32) -> Id {
        let budget = self.round(self.config.reuse_budget(replicas));
        let probe = &mut self.pool[index];
        probe.uses += 1;
        // The replica has not counted this request yet.
        probe.reading.rif += 1;
        let replica = probe.replica;
        if u64::from(probe.uses) >= budget {
            self.pool.remove(index);
        }
        replica
    }

    /// An integer with the same expectation as `x`: its floor or its ceiling,
    /// chosen at random.
    fn round(&mut self, x: f64) -> u64 {
        if !x.is_finite() || x >= u64::MAX as f64 {
            return u64::MAX;
        }
        let floor = x.floor();
        let extra = u64::from(self.rng.unit() < x - floor);
        floor as u64 + extra
    }

    /// How many of `kind` a request owes: its rate, rounded so the average over
    /// many requests is exactly the rate.
    fn owed(&mut self, kind: Owed) -> u32 {
        let (rate, owed) = match kind {
            Owed::Probe => (self.config.probes_per_query, &mut self.probe_owed),
            Owed::Remove => (self.config.removals_per_query, &mut self.remove_owed),
        };
        *owed += rate;
        let whole = owed.floor();
        *owed -= whole;
        whole as u32
    }

    /// Remove `count` probes, alternating the oldest and the worst.
    fn remove(&mut self, count: u32) {
        for _ in 0..count {
            if self.pool.is_empty() {
                return;
            }
            let index = if self.remove_oldest {
                0
            } else {
                self.worst()
            };
            self.remove_oldest = !self.remove_oldest;
            self.pool.remove(index);
        }
    }

    /// The worst probe under the same ordering: the hottest if any is hot,
    /// otherwise the cold one with the highest latency.
    fn worst(&self) -> usize {
        let threshold = self.hot_threshold().unwrap_or(0.0);
        let hot = |p: &Probe| f64::from(p.reading.rif) > threshold;
        let key = |p: &Probe| {
            if self.pool.iter().any(hot) {
                (u64::from(hot(p)), u64::from(p.reading.rif))
            } else {
                (1, p.reading.latency.as_nanos() as u64)
            }
        };
        self.pool
            .iter()
            .enumerate()
            .max_by_key(|(i, p)| (key(p), std::cmp::Reverse(*i)))
            .map_or(0, |(i, _)| i)
    }

    /// `count` replicas from `replicas`, uniformly at random and without repeats.
    fn sample(&mut self, replicas: &[Id], count: u32) -> Vec<Id> {
        let mut rest = replicas.to_vec();
        let take = (count as usize).min(rest.len());
        // A partial Fisher-Yates shuffle: the first `take` places are the sample.
        for i in 0..take {
            let j = i + self.rng.below((rest.len() - i) as u32) as usize;
            rest.swap(i, j);
        }
        rest.truncate(take);
        rest
    }
}

/// Which owed count [`Prequal::owed`] is asked for.
#[derive(Clone, Copy)]
enum Owed {
    Probe,
    Remove,
}

/// A replica's side: counts what is in flight and answers probes.
///
/// A request calls [`arrive`](Load::arrive) when it starts and
/// [`finish`](Load::finish) when it ends, and a probe is answered by
/// [`reading`](Load::reading). Each finished request is remembered with the RIF it
/// arrived at, because latency depends on load and a probe asks about the load
/// *now*.
#[derive(Debug, Clone)]
pub struct Load {
    in_flight: u32,
    /// Finished requests, oldest first.
    samples: VecDeque<Sample>,
    window: Duration,
    capacity: u32,
}

#[derive(Debug, Clone, Copy)]
struct Sample {
    finished_at: Instant,
    rif: u32,
    latency: Duration,
}

/// A request in progress, from [`Load::arrive`]: the RIF it saw on arrival,
/// counting itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ticket {
    rif: u32,
}

impl Load {
    /// A replica that remembers finished requests for `window`, and at most
    /// `capacity` of them. The paper uses requests from the last 1 to 10 ms at a
    /// high query rate; a quiet replica wants a longer window.
    pub fn new(window: Duration, capacity: u32) -> Self {
        Load {
            in_flight: 0,
            samples: VecDeque::new(),
            window,
            capacity: capacity.max(1),
        }
    }

    /// Requests in flight now.
    pub fn in_flight(&self) -> u32 {
        self.in_flight
    }

    /// A request starts.
    pub fn arrive(&mut self) -> Ticket {
        self.in_flight += 1;
        Ticket { rif: self.in_flight }
    }

    /// The request behind `ticket` ended at `now`, `latency` after it began.
    pub fn finish(&mut self, ticket: Ticket, now: Instant, latency: Duration) {
        self.in_flight = self.in_flight.saturating_sub(1);
        self.samples.push_back(Sample {
            finished_at: now,
            rif: ticket.rif,
            latency,
        });
        while self.samples.len() as u32 > self.capacity {
            self.samples.pop_front();
        }
    }

    /// The answer to a probe at `now`: the RIF, and the median latency of recent
    /// requests that arrived at about that RIF. With no recent request there is
    /// no estimate, and the latency is zero, which makes the replica look as good
    /// as can be: a replica nobody has used lately should be tried.
    pub fn reading(&mut self, now: Instant) -> Reading {
        let window = self.window;
        while self
            .samples
            .front()
            .is_some_and(|s| since(now, s.finished_at) > window)
        {
            self.samples.pop_front();
        }
        // At the current RIF, or failing that at the nearest RIF there is.
        let target = self.in_flight;
        let nearest = self
            .samples
            .iter()
            .map(|s| s.rif.abs_diff(target))
            .min();
        let mut latencies: Vec<Duration> = match nearest {
            Some(gap) => self
                .samples
                .iter()
                .filter(|s| s.rif.abs_diff(target) == gap)
                .map(|s| s.latency)
                .collect(),
            None => Vec::new(),
        };
        latencies.sort_unstable();
        let latency = if latencies.is_empty() {
            Duration::ZERO
        } else {
            latencies[(latencies.len() - 1) / 2]
        };
        Reading {
            rif: self.in_flight,
            latency,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(ms: u64) -> Instant {
        Instant::from_epoch(Duration::from_millis(ms))
    }

    fn ms(n: u64) -> Duration {
        Duration::from_millis(n)
    }

    fn ids(n: u128) -> Vec<Id> {
        (1..=n).map(Id::from).collect()
    }

    fn reading(rif: u32, latency_ms: u64) -> Reading {
        Reading {
            rif,
            latency: ms(latency_ms),
        }
    }

    /// A balancer that probes nothing and removes nothing by itself, so a test
    /// sees only the rule it is about.
    fn still() -> Prequal<SplitMix64> {
        let config = Config {
            probes_per_query: 1e-9,
            removals_per_query: 0.0,
            ..Config::default()
        };
        Prequal::new(config, SplitMix64::new(1)).unwrap()
    }

    fn fill(p: &mut Prequal<SplitMix64>, readings: &[(u128, u32, u64)]) {
        for &(id, rif, latency) in readings {
            p.probed(at(0), Id::from(id), reading(rif, latency));
        }
    }

    #[test]
    fn the_default_configuration_is_valid() {
        assert_eq!(Config::default().validate(), Ok(()));
    }

    #[test]
    fn a_nonsense_configuration_is_refused() {
        let bad = |f: fn(&mut Config)| {
            let mut c = Config::default();
            f(&mut c);
            c.validate()
        };
        assert_eq!(bad(|c| c.pool_size = 0), Err(ConfigError::EmptyPool));
        assert_eq!(bad(|c| c.probes_per_query = -1.0), Err(ConfigError::BadRate));
        assert_eq!(bad(|c| c.delta = f64::NAN), Err(ConfigError::BadRate));
        assert_eq!(bad(|c| c.probes_per_query = 0.0), Err(ConfigError::NoProbing));
        assert_eq!(bad(|c| c.hot_quantile = 1.5), Err(ConfigError::BadQuantile));
    }

    /// The paper's formula, worked: m = 16, n = 100, r_probe = 3, r_remove = 1,
    /// δ = 1 gives (1 + 1) / ((1 − 0.16)·3 − 1) = 2 / 1.52.
    #[test]
    fn the_reuse_budget_is_the_papers_formula() {
        let budget = Config::default().reuse_budget(100);
        assert!((budget - 2.0 / 1.52).abs() < 1e-12, "{budget}");
    }

    /// With few replicas the pool covers most of them, and probes are scarce.
    #[test]
    fn the_reuse_budget_is_unlimited_when_removals_outpace_probing() {
        // m/n = 16/16: the pool is every replica, so (1 − 1)·3 − 1 < 0.
        assert!(Config::default().reuse_budget(16).is_infinite());
        // And it is never below one use.
        let config = Config {
            probes_per_query: 100.0,
            ..Config::default()
        };
        assert_eq!(config.reuse_budget(1000), 1.0);
    }

    /// **Cold probes compete on latency**, even a cold one with a higher RIF.
    #[test]
    fn a_cold_probe_with_the_lowest_latency_wins() {
        let mut p = still();
        // Five replicas; with q = 0.84 the highest RIF (replica 5) is hot.
        fill(
            &mut p,
            &[(1, 2, 30), (2, 3, 10), (3, 1, 20), (4, 2, 40), (5, 9, 1)],
        );
        let d = p.query(at(1), &ids(5)).unwrap();
        // Replica 5 has the best latency of all and is hot, so it is not eligible.
        assert_eq!(d.replica, Id::from(2));
    }

    /// **When every probe is hot, the lowest RIF wins.**
    #[test]
    fn with_everything_hot_the_lowest_rif_wins() {
        // A pool that holds only the last three probes, and a history that
        // remembers twenty earlier responses from idle replicas (RIF 0). Hot is
        // measured against the history, so the three in the pool, at RIF 7 to 9,
        // are all hot.
        let config = Config {
            pool_size: 3,
            probes_per_query: 1e-9,
            removals_per_query: 0.0,
            ..Config::default()
        };
        let mut p = Prequal::new(config, SplitMix64::new(1)).unwrap();
        for id in 100..120 {
            p.probed(at(0), Id::from(id), reading(0, 1));
        }
        // Replica 2 has the lowest RIF; replica 1 has the lowest latency.
        fill(&mut p, &[(1, 9, 1), (2, 7, 9), (3, 8, 5)]);
        assert_eq!(p.pool().len(), 3);
        let threshold = p.hot_threshold().unwrap();
        assert!(p.pool().iter().all(|x| f64::from(x.reading.rif) > threshold));

        assert_eq!(p.query(at(1), &ids(3)).unwrap().replica, Id::from(2));
    }

    /// Cold wins on latency even when a hot probe is faster: speed bought with a
    /// queue is not speed.
    #[test]
    fn a_hot_probe_is_not_chosen_while_a_cold_one_exists() {
        let mut p = still();
        for id in 100..120 {
            p.probed(at(0), Id::from(id), reading(1, 50));
        }
        p.pool.clear();
        // Against a history of RIF 1, the probe at RIF 30 is hot and fast.
        fill(&mut p, &[(1, 30, 1), (2, 1, 40), (3, 1, 20)]);
        assert_eq!(p.query(at(1), &ids(3)).unwrap().replica, Id::from(3));
    }

    /// The hot threshold is the quantile of the recent responses' RIFs.
    #[test]
    fn the_threshold_is_the_quantile_of_the_recent_rifs() {
        let responses = [(1, 1, 1), (2, 2, 1), (3, 3, 1), (4, 4, 1), (5, 100, 1)];
        let mut p = still();
        fill(&mut p, &responses);
        // Sorted 1, 2, 3, 4, 100. At 0.84 the position is 0.84 · 4 = 3.36, which is
        // 4 + 0.36 · (100 − 4) = 38.56.
        let threshold = p.hot_threshold().unwrap();
        assert!((threshold - 38.56).abs() < 1e-9, "{threshold}");

        let config = Config {
            hot_quantile: 0.5,
            ..Config::default()
        };
        let mut q = Prequal::new(config, SplitMix64::new(1)).unwrap();
        fill(&mut q, &responses);
        // The median.
        assert_eq!(q.hot_threshold(), Some(3.0));
    }

    /// The history is bounded, and old responses fall out of it.
    #[test]
    fn the_history_keeps_only_the_recent_responses() {
        let config = Config {
            rif_history: 3,
            probes_per_query: 1e-9,
            ..Config::default()
        };
        let mut p = Prequal::new(config, SplitMix64::new(1)).unwrap();
        for (id, rif) in [(1u128, 100u32), (2, 1), (3, 2), (4, 3)] {
            p.probed(at(0), Id::from(id), reading(rif, 1));
        }
        // The 100 has fallen out: the median of 1, 2, 3 is 2.
        let config = Config {
            hot_quantile: 0.5,
            ..config
        };
        let mut q = Prequal::new(config, SplitMix64::new(1)).unwrap();
        for (id, rif) in [(1u128, 100u32), (2, 1), (3, 2), (4, 3)] {
            q.probed(at(0), Id::from(id), reading(rif, 1));
        }
        assert_eq!(q.hot_threshold(), Some(2.0));
    }

    /// One probe is not a comparison.
    #[test]
    fn with_fewer_than_two_probes_the_choice_is_random() {
        let replicas = ids(8);
        let mut seen = std::collections::HashSet::new();
        let mut p = still();
        for t in 0..200 {
            seen.insert(p.query(at(t), &replicas).unwrap().replica);
        }
        assert!(seen.len() > 4, "only {} replicas ever chosen", seen.len());
        assert!(p.pool().is_empty());

        p.probed(at(300), Id::from(3), reading(0, 1));
        let mut chosen = std::collections::HashSet::new();
        for t in 301..400 {
            // Re-add so the pool never grows past one.
            p.pool.clear();
            p.probed(at(t), Id::from(3), reading(0, 1));
            chosen.insert(p.query(at(t), &replicas).unwrap().replica);
        }
        assert!(chosen.len() > 4, "a lone probe was trusted: {chosen:?}");
    }

    #[test]
    fn no_replicas_means_no_decision() {
        assert_eq!(still().query(at(0), &[]), None);
    }

    /// The client counts its own request against the replica it chose, so the next
    /// pick does not pile on while the replica has not yet reported.
    #[test]
    fn using_a_probe_bumps_its_rif() {
        let config = Config {
            removals_per_query: 0.0,
            probes_per_query: 1e-9,
            // A big delta makes the budget large, so the probe survives its use.
            delta: 100.0,
            ..Config::default()
        };
        let mut p = Prequal::new(config, SplitMix64::new(1)).unwrap();
        fill(&mut p, &[(1, 0, 5), (2, 0, 6)]);
        let replicas = ids(1000);
        let first = p.query(at(1), &replicas).unwrap().replica;
        assert_eq!(first, Id::from(1));
        let probe = p.pool().iter().find(|x| x.replica == first).unwrap();
        assert_eq!((probe.uses, probe.reading.rif), (1, 1));
        // Its latency is as probed: the paper does not adjust it.
        assert_eq!(probe.reading.latency, ms(5));
    }

    #[test]
    fn a_probe_is_retired_after_its_budget() {
        // m/n = 16/20, r_probe = 3, r_remove = 0 → budget 2/(0.2·3) = 3.33.
        let config = Config {
            removals_per_query: 0.0,
            probes_per_query: 3.0,
            ..Config::default()
        };
        let budget = config.reuse_budget(20);
        assert!(budget > 3.0 && budget < 4.0, "{budget}");
        let mut p = Prequal::new(config, SplitMix64::new(7)).unwrap();
        fill(&mut p, &[(1, 0, 1), (2, 5, 2)]);
        let replicas = ids(20);
        let mut uses = 0;
        // Replica 1 stays the best cold probe until its budget runs out.
        while p.pool().iter().any(|x| x.replica == Id::from(1) && x.uses < 100) {
            let d = p.query(at(1), &replicas).unwrap();
            if d.replica != Id::from(1) {
                break;
            }
            uses += 1;
            assert!(uses <= 4, "a probe served {uses} requests");
        }
        assert!((3..=4).contains(&uses), "served {uses}");
    }

    #[test]
    fn a_newer_answer_replaces_an_older_one_from_the_same_replica() {
        let mut p = still();
        p.probed(at(0), Id::from(1), reading(9, 9));
        p.probed(at(5), Id::from(1), reading(1, 1));
        assert_eq!(p.pool().len(), 1);
        assert_eq!(p.pool()[0].reading, reading(1, 1));
    }

    #[test]
    fn a_full_pool_drops_its_oldest_probe() {
        let mut p = still();
        for id in 1..=16 {
            p.probed(at(id as u64), Id::from(id), reading(0, 1));
        }
        assert_eq!(p.pool().len(), 16);
        p.probed(at(100), Id::from(99), reading(0, 1));
        assert_eq!(p.pool().len(), 16);
        assert!(p.pool().iter().all(|x| x.replica != Id::from(1)));
        assert!(p.pool().iter().any(|x| x.replica == Id::from(99)));
    }

    #[test]
    fn an_old_probe_is_dropped() {
        let mut p = still();
        p.probed(at(0), Id::from(1), reading(0, 1));
        p.probed(at(600), Id::from(2), reading(0, 1));
        // At 1100 ms, probe 1 is 1100 ms old (past the 1 s limit), probe 2 is not.
        p.query(at(1100), &ids(2));
        assert_eq!(p.pool().len(), 1);
        assert_eq!(p.pool()[0].replica, Id::from(2));
    }

    #[test]
    fn a_probe_of_a_replica_that_left_is_dropped() {
        let mut p = still();
        fill(&mut p, &[(1, 0, 1), (2, 0, 1), (3, 0, 1)]);
        p.query(at(1), &[Id::from(1), Id::from(3)]);
        assert!(p.pool().iter().all(|x| x.replica != Id::from(2)));
    }

    /// Removals alternate between the oldest probe and the worst.
    #[test]
    fn removal_alternates_oldest_and_worst() {
        let mut p = still();
        // 1 is oldest; 3 has the highest RIF (so is hot and worst).
        for (t, (id, rif)) in [(1u128, 1u32), (2, 2), (3, 50), (4, 3), (5, 4)]
            .into_iter()
            .enumerate()
        {
            p.probed(at(t as u64), Id::from(id), reading(rif, 10));
        }
        p.remove(1);
        assert!(p.pool().iter().all(|x| x.replica != Id::from(1)), "oldest first");
        p.remove(1);
        assert!(p.pool().iter().all(|x| x.replica != Id::from(3)), "then the worst");
        assert_eq!(p.pool().len(), 3);
    }

    /// With no hot probe, the worst is the cold one with the highest latency.
    #[test]
    fn the_worst_cold_probe_has_the_highest_latency() {
        let mut p = still();
        fill(&mut p, &[(1, 2, 5), (2, 2, 90), (3, 2, 7)]);
        assert_eq!(p.worst(), 1);
    }

    /// A fractional rate averages out exactly.
    #[test]
    fn a_fractional_probing_rate_is_exact_on_average() {
        let config = Config {
            probes_per_query: 2.5,
            ..Config::default()
        };
        let mut p = Prequal::new(config, SplitMix64::new(3)).unwrap();
        let replicas = ids(50);
        let sent: usize = (0..1000)
            .map(|t| p.query(at(t), &replicas).unwrap().probe.len())
            .sum();
        assert_eq!(sent, 2500);
    }

    #[test]
    fn probes_are_distinct_replicas_from_the_set() {
        let config = Config {
            probes_per_query: 5.0,
            ..Config::default()
        };
        let mut p = Prequal::new(config, SplitMix64::new(4)).unwrap();
        let replicas = ids(10);
        for t in 0..100 {
            let d = p.query(at(t), &replicas).unwrap();
            assert_eq!(d.probe.len(), 5);
            let distinct: std::collections::HashSet<_> = d.probe.iter().collect();
            assert_eq!(distinct.len(), 5);
            assert!(d.probe.iter().all(|r| replicas.contains(r)));
        }
        // Asking for more than exist gives them all, once each.
        let config = Config {
            probes_per_query: 5.0,
            ..Config::default()
        };
        let mut few = Prequal::new(config, SplitMix64::new(4)).unwrap();
        assert_eq!(few.query(at(0), &ids(3)).unwrap().probe.len(), 3);
    }

    #[test]
    fn an_idle_client_asks_for_fresh_probes_only_when_quiet() {
        let mut p = Prequal::new(Config::default(), SplitMix64::new(5)).unwrap();
        let replicas = ids(10);
        // Never probed: quiet.
        assert!(!p.idle(at(0), &replicas).is_empty());
        // Just probed: not quiet.
        assert!(p.idle(at(100), &replicas).is_empty());
        // After max_idle (250 ms) it is.
        assert!(!p.idle(at(300), &replicas).is_empty());
        // A request probes too, which resets the quiet.
        p.query(at(1000), &replicas);
        assert!(p.idle(at(1100), &replicas).is_empty());
    }

    // -- A replica's side ----------------------------------------------------------

    #[test]
    fn a_replica_counts_what_is_in_flight() {
        let mut load = Load::new(ms(100), 64);
        let a = load.arrive();
        let b = load.arrive();
        assert_eq!((a, b), (Ticket { rif: 1 }, Ticket { rif: 2 }));
        assert_eq!(load.reading(at(0)).rif, 2);
        load.finish(a, at(5), ms(5));
        assert_eq!(load.in_flight(), 1);
    }

    /// The estimate is the median of requests that arrived at the current RIF.
    #[test]
    fn the_latency_estimate_is_the_median_at_the_current_rif() {
        let mut load = Load::new(ms(1000), 64);
        // Three requests that each ran alone (RIF 1), at 10, 30 and 20 ms.
        for (t, l) in [(10u64, 10u64), (40, 30), (70, 20)] {
            let ticket = load.arrive();
            load.finish(ticket, at(t), ms(l));
        }
        // And one that ran at RIF 2, slowly.
        let a = load.arrive();
        let b = load.arrive();
        load.finish(a, at(90), ms(200));
        load.finish(b, at(95), ms(210));
        // Idle now, so the RIF is 0 and the nearest samples are those at RIF 1.
        let r = load.reading(at(100));
        assert_eq!(r.rif, 0);
        assert_eq!(r.latency, ms(20));
        // At RIF 2 only the second arrival, which saw RIF 2, counts.
        let _x = load.arrive();
        let _y = load.arrive();
        assert_eq!(load.reading(at(100)).latency, ms(210));
    }

    #[test]
    fn old_samples_are_forgotten() {
        let mut load = Load::new(ms(50), 64);
        let t = load.arrive();
        load.finish(t, at(0), ms(10));
        assert_eq!(load.reading(at(40)).latency, ms(10));
        assert_eq!(load.reading(at(100)).latency, Duration::ZERO);
    }

    #[test]
    fn a_replica_remembers_at_most_its_capacity() {
        let mut load = Load::new(ms(10_000), 3);
        for l in [1u64, 2, 3, 4, 5] {
            let t = load.arrive();
            load.finish(t, at(l), ms(l));
        }
        // Only 3, 4, 5 are left; the median is 4.
        assert_eq!(load.reading(at(10)).latency, ms(4));
    }

    // -- Together ------------------------------------------------------------------

    /// **The point of it.** Ten replicas, one slow. Nothing here knows which; it
    /// finds out from probes, and sends it far less than its share.
    #[test]
    fn a_slow_replica_gets_less_than_its_share() {
        let replicas = ids(10);
        let slow = Id::from(7);
        // A replica's true cost: slow ones take ten times as long.
        let service = |id: Id| if id == slow { 100u64 } else { 10 };
        let mut loads: Vec<Load> = replicas.iter().map(|_| Load::new(ms(200), 64)).collect();
        let mut p = Prequal::new(Config::default(), SplitMix64::new(11)).unwrap();
        let mut sent = std::collections::HashMap::<Id, u32>::new();
        let mut now = 0u64;
        // Requests arrive every millisecond; each lasts its replica's service time
        // plus a little for every request already in flight there.
        let mut done: Vec<(u64, usize, Ticket, u64)> = Vec::new();
        for _ in 0..4000 {
            now += 1;
            // Finish what is due.
            done.retain(|&(due, index, ticket, latency)| {
                if due <= now {
                    loads[index].finish(ticket, at(now), ms(latency));
                    false
                } else {
                    true
                }
            });
            let d = p.query(at(now), &replicas).unwrap();
            for target in &d.probe {
                let index = replicas.iter().position(|r| r == target).unwrap();
                let r = loads[index].reading(at(now));
                p.probed(at(now), *target, r);
            }
            let index = replicas.iter().position(|r| *r == d.replica).unwrap();
            let ticket = loads[index].arrive();
            let latency = service(d.replica) + 5 * u64::from(ticket.rif);
            done.push((now + latency, index, ticket, latency));
            *sent.entry(d.replica).or_default() += 1;
        }
        let to_slow = f64::from(sent[&slow]) / 4000.0;
        assert!(to_slow < 0.05, "the slow replica got {to_slow:.3} of the traffic");
        // And the rest were not starved: every other replica was used.
        assert!(replicas.iter().filter(|r| **r != slow).all(|r| sent.get(r).copied().unwrap_or(0) > 100));
    }
}
