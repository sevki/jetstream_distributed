//! Traits for placing and discovering resources.
//!
//! This module is in the verified build, which has `std` and `vstd` and nothing
//! else, so it names no Jetstream type: [`Placement`] answers with [`Id`]s,
//! and turning a host into an address is the service layer's business. What does
//! need an address, [`Discovery`], is behind the `service` feature.
use std::any::Any;
use std::fmt;
use std::result::Result;

#[cfg(feature = "service")]
use jetstream::prelude::async_trait;

use crate::id::Id;
use crate::scheduling::Resource;

/// Errors that can occur during placement.
#[derive(Debug, Clone, PartialEq)]
pub enum PlacementError {
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

impl fmt::Display for PlacementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            PlacementError::InvalidCapacity => "invalid capacity",
            PlacementError::InvalidRequest => "invalid request",
            PlacementError::InvalidDistribution => "invalid distribution",
            PlacementError::DuplicateHost => "duplicate host",
            PlacementError::DuplicateJob => "duplicate job",
            PlacementError::UnknownHost => "unknown host",
            PlacementError::UnknownJob => "unknown job",
            PlacementError::ClockWentBackwards => "clock went backwards",
            PlacementError::FutureJob => "future job",
            PlacementError::NoCapacity => "no capacity",
            PlacementError::MigrationNotApproved => "migration not approved",
        })
    }
}

impl std::error::Error for PlacementError {}

/// A trait for placing resources. It is async, which is Jetstream's
/// `async_trait`, so it exists with `service`; [`PlacementError`] does not need it.
#[cfg(feature = "service")]
#[async_trait]
pub trait Placement {
    /// The type of resource to place.
    type Resource: Resource + Send + Sync;

    /// Place a resource and return the hosts that should host it, in order of
    /// preference.
    async fn place(&mut self, what: Self::Resource) -> Result<Vec<Id>, PlacementError>;
}
