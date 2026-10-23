//! A node's own resources: what it has, and what is free right now.
//!
//! [`Sampler`] asks the machine ([`sysinfo`]) and returns a [`Reading`], the
//! numbers as the operating system gives them; [`Reading::measure`] turns that
//! into [`Resources`], the units the scheduler speaks (millicores and bytes), as a
//! [`Measure`] of the node's **capacity** and what is **available** of it. The
//! scheduler's `Host` is a capacity and a set of jobs; the event a monitor
//! publishes is the available part, so a reader can tell what room the node has
//! left without knowing what it was running.
//!
//! The conversion is a pure function of a [`Reading`], so it is tested without a
//! machine; the sampler is a thin shell around `sysinfo`.
//!
//! # What it does not see
//!
//! * **A container's CPU limit.** `sysinfo` reports a cgroup's *memory* limit and
//!   this honours it, but the CPU count is the host's, not a CFS quota's. A node
//!   confined to two cores of a sixty-four-core machine reports sixty-four.
//! * **Which of the CPU is yours.** Usage is the machine's, all processes, not
//!   this service's share of it. For a node that is the point: what is free is
//!   what anyone could use.
//! * **A first reading is not a measurement.** CPU usage is a difference between
//!   two refreshes at least [`MIN_INTERVAL`] apart; right after [`Sampler::new`]
//!   there is no difference yet, and the busy share reads as 0. Wait that long
//!   before the first [`Sampler::read`], or discard it.

use sysinfo::{CpuRefreshKind, MemoryRefreshKind, RefreshKind, System};

use crate::compute::{Cpu, Memory, Resources};

/// The shortest time between two reads that makes the CPU usage in the second one
/// mean something.
pub const MIN_INTERVAL: std::time::Duration = sysinfo::MINIMUM_CPU_UPDATE_INTERVAL;

/// What the machine says, before it becomes [`Resources`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Reading {
    /// Logical cores.
    pub cores: u32,
    /// The share of all cores that was busy since the last read, in percent: 0 for
    /// idle, 100 for every core saturated.
    pub cpu_busy_percent: f32,
    /// Memory this node may use, in bytes: the machine's, or its cgroup's if that
    /// is smaller.
    pub memory_total: u64,
    /// Of that, what is free to take without swapping others out.
    pub memory_available: u64,
}

/// A node's capacity, and what is available of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Measure {
    /// All it has.
    pub capacity: Resources,
    /// What is free now. Never more than `capacity`, in either part.
    pub available: Resources,
}

impl Reading {
    /// The same numbers in the scheduler's units.
    ///
    /// CPU is the cores' millicores, scaled by the idle share and rounded down: a
    /// node that reports less than it has is the safe way to be wrong. A busy
    /// share that is not a number is taken to mean fully busy, and one outside
    /// 0 to 100 is clamped. Available memory is held to the total.
    pub fn measure(self) -> Measure {
        let capacity = Resources {
            cpu: Cpu::cores(u64::from(self.cores)),
            memory: Memory::bytes(self.memory_total),
        };
        let busy = if self.cpu_busy_percent.is_nan() {
            100.0
        } else {
            f64::from(self.cpu_busy_percent).clamp(0.0, 100.0)
        };
        let idle = (100.0 - busy) / 100.0;
        let available = Resources {
            cpu: Cpu::millicores((capacity.cpu.as_millicores() as f64 * idle).floor() as u64),
            memory: Memory::bytes(self.memory_available.min(self.memory_total)),
        };
        Measure {
            capacity,
            available,
        }
    }
}

/// Reads this machine's [`Reading`].
pub struct Sampler {
    system: System,
}

impl Sampler {
    /// A sampler that has loaded the CPU list and memory, and taken the first of
    /// the two CPU refreshes a usage figure needs. See [`MIN_INTERVAL`].
    pub fn new() -> Self {
        let mut system = System::new_with_specifics(
            RefreshKind::nothing()
                .with_cpu(CpuRefreshKind::nothing().with_cpu_usage())
                .with_memory(MemoryRefreshKind::nothing().with_ram()),
        );
        system.refresh_cpu_usage();
        Sampler { system }
    }

    /// The machine now.
    pub fn read(&mut self) -> Reading {
        self.system.refresh_cpu_usage();
        self.system.refresh_memory();
        let mut memory_total = self.system.total_memory();
        let mut memory_available = self.system.available_memory();
        // A container's memory limit is the memory it has, whatever the machine
        // behind it does.
        if let Some(limits) = self.system.cgroup_limits() {
            memory_total = memory_total.min(limits.total_memory);
            memory_available = memory_available.min(limits.free_memory);
        }
        Reading {
            cores: u32::try_from(self.system.cpus().len()).unwrap_or(u32::MAX),
            cpu_busy_percent: self.system.global_cpu_usage(),
            memory_total,
            memory_available,
        }
    }

    /// [`read`](Sampler::read) and [`measure`](Reading::measure) in one.
    pub fn measure(&mut self) -> Measure {
        self.read().measure()
    }
}

impl Default for Sampler {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for Sampler {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sampler").finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const GIB: u64 = 1 << 30;

    fn reading(cores: u32, busy: f32, total: u64, available: u64) -> Reading {
        Reading {
            cores,
            cpu_busy_percent: busy,
            memory_total: total,
            memory_available: available,
        }
    }

    #[test]
    fn capacity_is_the_cores_in_millicores_and_the_memory_in_bytes() {
        let m = reading(8, 0.0, 16 * GIB, 16 * GIB).measure();
        assert_eq!(m.capacity.cpu, Cpu::millicores(8000));
        assert_eq!(m.capacity.memory, Memory::gib(16));
    }

    #[test]
    fn available_cpu_is_the_idle_share_of_the_capacity() {
        let m = reading(8, 25.0, GIB, GIB).measure();
        assert_eq!(m.available.cpu, Cpu::millicores(6000));
        // Idle: all of it. Saturated: none.
        assert_eq!(reading(8, 0.0, GIB, GIB).measure().available.cpu, Cpu::millicores(8000));
        assert_eq!(reading(8, 100.0, GIB, GIB).measure().available.cpu, Cpu::ZERO);
    }

    /// Rounded down, so a node never promises more than it has.
    #[test]
    fn available_cpu_rounds_down() {
        // 1 core at 33.33% busy is 66.67% idle: 666.7 millicores free.
        let m = reading(1, 33.33, GIB, GIB).measure();
        assert_eq!(m.available.cpu, Cpu::millicores(666));
    }

    #[test]
    fn a_busy_share_out_of_range_or_not_a_number_is_made_safe() {
        let cpu = |busy| reading(4, busy, GIB, GIB).measure().available.cpu;
        assert_eq!(cpu(-5.0), Cpu::millicores(4000), "below 0 is idle");
        assert_eq!(cpu(250.0), Cpu::ZERO, "above 100 is saturated");
        assert_eq!(cpu(f32::NAN), Cpu::ZERO, "not a number is taken as busy");
    }

    #[test]
    fn available_memory_is_held_to_the_total() {
        let m = reading(2, 0.0, 4 * GIB, 6 * GIB).measure();
        assert_eq!(m.available.memory, Memory::gib(4));
        let m = reading(2, 0.0, 4 * GIB, GIB).measure();
        assert_eq!(m.available.memory, Memory::gib(1));
    }

    #[test]
    fn available_never_exceeds_capacity() {
        for busy in [0.0, 12.5, 99.9, 100.0] {
            let m = reading(16, busy, 8 * GIB, 3 * GIB).measure();
            assert!(m.available.fits(m.capacity), "{m:?}");
        }
    }

    /// The real machine, whatever it is: the numbers must at least be possible.
    #[test]
    fn the_sampler_reads_a_plausible_machine() {
        let mut sampler = Sampler::new();
        std::thread::sleep(MIN_INTERVAL);
        let read = sampler.read();
        assert!(read.cores >= 1, "{read:?}");
        assert!(read.memory_total > 0, "{read:?}");
        assert!(read.memory_available <= read.memory_total, "{read:?}");
        assert!((0.0..=100.0).contains(&read.cpu_busy_percent), "{read:?}");

        let m = read.measure();
        assert!(m.available.fits(m.capacity), "{m:?}");
        assert!(m.capacity.cpu >= Cpu::millicores(1000));
    }
}
