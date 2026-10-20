//! Traits for placing and discovering resources.
//!
//! This module is in the verified build, which has `std` and `vstd` and nothing
//! else, so it names no Jetstream type: [`Placement`] answers with [`Id`]s,
//! and turning a host into an address is the service layer's business. What does
//! need an address, [`Discovery`], is behind the `service` feature.
use std::any::Any;
use std::fmt;
use std::result::Result;

use crate::id::Id;
use crate::scheduling::Resource;

/// Errors that can occur during placement.
#[derive(Debug, Clone, PartialEq)]
pub enum PlacementError {
    /// The requested resource was not found.
    NotFound,
    /// The requested resource conflicts with an existing resource.
    Conflict,
    /// An internal error occurred.
    InternalError,
}

impl fmt::Display for PlacementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            PlacementError::NotFound => "not found",
            PlacementError::Conflict => "conflict",
            PlacementError::InternalError => "internal error",
        })
    }
}

impl std::error::Error for PlacementError {}

/// A trait for placing resources.
pub trait Placement {
    /// Place a resource and return the hosts that should host it, in order of
    /// preference.
    fn place<W: Resource>(&self, what: W) -> Result<Vec<Id>, PlacementError>;
}
