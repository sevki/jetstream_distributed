use std::time::Duration;

// Only the wire format needs Jetstream, and this module is in the verified build,
// which has no dependencies: the derive is behind `service`.
#[cfg(feature = "service")]
use jetstream::prelude::*;

// Something that does compute, e.g. a VM, container, v8 isolate, or interpreter.
pub type JobId = u128;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "service", derive(JetStreamWireFormat))]
pub struct Resources {
    pub cpu: u64,
    pub memory: u64,
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
    pub started_at: Duration,
    pub features: F,
}
