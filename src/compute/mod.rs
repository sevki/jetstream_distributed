use std::{
    fmt,
    ops::{Add, Sub},
    time::Duration,
};

// Only the wire format needs Jetstream, and this module is in the verified build,
// which has no dependencies: the derive is behind `service`.
#[cfg(feature = "service")]
use jetstream::prelude::*;

// Something that does compute, e.g. a VM, container, v8 isolate, or interpreter.
pub type JobId = u128;

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

#[derive(Debug, Clone)]
pub struct Job<F> {
    pub id: JobId,
    pub resources: Resources,
    // TODO: surely this must be an Instant???
    pub started_at: Duration,
    pub features: F,
}
