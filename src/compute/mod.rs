use std::time::Duration;

// Something that does compute, e.g. a VM, container, v8 isolate, or interpreter.
pub type JobId = u128;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
