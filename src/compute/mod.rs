use std::{
    fmt,
    ops::{Add, Sub},
    time::Duration,
};

// Only the wire format needs Jetstream, and this module is in the verified build,
// which has no dependencies: the derive is behind `service`.
#[cfg(feature = "service")]
use jetstream::prelude::*;

// A job, or anything that does compute, e.g. a VM, container, v8 isolate, or
// interpreter, is named by an `Id`.
pub use crate::id::Id;
use crate::scheduling;

/// CPU, held as millicores: 1000 of them are one core.
///
/// The unit is in the constructors and the accessor rather than in a comment,
/// so a call site says which one it means.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "service", derive(JetStreamWireFormat))]
pub struct Cpu(u64);

impl Cpu {
    pub const ZERO: Self = Cpu(0);

    pub const fn millicores(millicores: u64) -> Self {
        Cpu(millicores)
    }

    pub const fn cores(cores: u64) -> Self {
        Cpu(cores * 1000)
    }

    pub const fn as_millicores(self) -> u64 {
        self.0
    }
}

/// Memory, held as bytes. The binary multiples (KiB, MiB, GiB) are powers of
/// 1024, not 1000.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "service", derive(JetStreamWireFormat))]
pub struct Memory(u64);

impl Memory {
    pub const ZERO: Self = Memory(0);

    pub const fn bytes(bytes: u64) -> Self {
        Memory(bytes)
    }

    pub const fn kib(kib: u64) -> Self {
        Memory(kib * 1024)
    }

    pub const fn mib(mib: u64) -> Self {
        Memory(mib * 1024 * 1024)
    }

    pub const fn gib(gib: u64) -> Self {
        Memory(gib * 1024 * 1024 * 1024)
    }

    pub const fn as_bytes(self) -> u64 {
        self.0
    }
}

impl fmt::Display for Cpu {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}m", self.0)
    }
}

/// For people, in binary units: the formatting is `humansize`'s, which is a
/// dependency of the services and not of the verified core, so this exists
/// only with `service`. Not a format to parse back; `as_bytes` is exact.
#[cfg(feature = "service")]
impl fmt::Display for Memory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&humansize::format_size(self.0, humansize::BINARY))
    }
}

#[cfg(all(test, feature = "service"))]
mod tests {
    use super::*;

    #[test]
    fn memory_prints_in_binary_units() {
        assert_eq!(Memory::ZERO.to_string(), "0 B");
        assert_eq!(Memory::bytes(1023).to_string(), "1023 B");
        assert_eq!(Memory::kib(1).to_string(), "1 KiB");
        assert_eq!(Memory::mib(512).to_string(), "512 MiB");
        assert_eq!(Memory::mib(1536).to_string(), "1.50 GiB");
        assert_eq!(Memory::gib(64).to_string(), "64 GiB");
    }
}

impl Add for Cpu {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Cpu(self.0 + rhs.0)
    }
}

impl Sub for Cpu {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Cpu(self.0 - rhs.0)
    }
}

impl Add for Memory {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Memory(self.0 + rhs.0)
    }
}

impl Sub for Memory {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Memory(self.0 - rhs.0)
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "service", derive(JetStreamWireFormat))]
pub struct Resources {
    pub cpu: Cpu,
    pub memory: Memory,
}

impl Resources {
    pub const ZERO: Self = Self {
        cpu: Cpu::ZERO,
        memory: Memory::ZERO,
    };
}

impl Resources {
    /// Whether these resources fit within `capacity`.
    pub fn fits(self, capacity: Self) -> bool {
        self.cpu <= capacity.cpu && self.memory <= capacity.memory
    }
}

/// A point in time: how long after the epoch of a clock the caller supplies.
///
/// This is not [`std::time::Instant`] on purpose. That one can only be read off
/// the local clock, so a scheduler could not be driven by a test, replayed, or
/// told when a job on another host started; it has no maximum, which a
/// deadline of "never" needs; and it cannot be sent. An [`Instant`] is made
/// from a number, compares and subtracts like a point in time, and only means
/// something against other instants of the same clock. A span is still a
/// [`Duration`], so a point and a span cannot be swapped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Instant(Duration);

impl Instant {
    /// The clock's zero.
    pub const EPOCH: Self = Instant(Duration::ZERO);

    /// Later than every other instant: a deadline that never arrives.
    pub const MAX: Self = Instant(Duration::MAX);

    /// `since_epoch` after the clock's zero.
    pub const fn from_epoch(since_epoch: Duration) -> Self {
        Instant(since_epoch)
    }

    pub const fn since_epoch(self) -> Duration {
        self.0
    }

    /// `self + span`, stopping at [`Instant::MAX`].
    pub fn saturating_add(self, span: Duration) -> Self {
        Instant(self.0.saturating_add(span))
    }

    /// The process's own monotonic clock, whose zero is the first call. It never
    /// goes backwards, which a scheduler's `tick` requires, and it is not a wall
    /// clock: instants from two processes are not comparable, and neither is one
    /// across a restart. A caller that needs either supplies its own clock with
    /// [`Instant::from_epoch`].
    pub fn now() -> Self {
        static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
        Instant(START.get_or_init(std::time::Instant::now).elapsed())
    }
}

/// The span between two instants. Panics if `rhs` is later, like
/// [`std::time::Instant`]'s; callers check the order first.
impl Sub for Instant {
    type Output = Duration;

    fn sub(self, rhs: Self) -> Duration {
        self.0 - rhs.0
    }
}

#[derive(Debug, Clone)]
pub struct Job<F> {
    pub id: Id,
    pub resources: Resources,
    /// When the job started, on the scheduler's clock.
    pub started_at: Instant,
    pub features: F,
}

impl<F: 'static> scheduling::Resource for Job<F> {}
