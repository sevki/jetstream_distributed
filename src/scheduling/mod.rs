#![deny(missing_docs)]
//! Traits for placing and discovering resources.
//!
//! This module is in the verified build, which has `std` and `vstd` and nothing
//! else, so it names no Jetstream type: [`Placement`] answers with [`HostId`]s,
//! and turning a host into an address is the service layer's business. What does
//! need an address, [`Discovery`], is behind the `service` feature.
use std::any::Any;
use std::fmt;
use std::result::Result;

use crate::host::HostId;

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

/// An error that can occur during discovery.
#[cfg(feature = "service")]
#[derive(Debug, Clone, PartialEq)]
pub enum DiscoveryError {
    /// The requested resource was not found.
    NotFound,
    /// An internal error occurred.
    InternalError,
}

#[cfg(feature = "service")]
impl fmt::Display for DiscoveryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            DiscoveryError::NotFound => "not found",
            DiscoveryError::InternalError => "internal error",
        })
    }
}

#[cfg(feature = "service")]
impl std::error::Error for DiscoveryError {}

/// A trait for resources that can be placed and discovered.
pub trait Resource: Any {}

/// A trait for placing resources.
pub trait Placement {
    /// Place a resource and return the hosts that should host it, in order of
    /// preference.
    fn place<W: Resource>(&self, what: W) -> Result<Vec<HostId>, PlacementError>;
}

/// A trait for discovering resources.
#[cfg(feature = "service")]
pub trait Discovery {
    /// Discover a resource and return the remote addresses of the nodes that
    /// host it.
    fn discover<W: Resource>(
        &self,
        what: W,
    ) -> Result<Vec<jetstream::prelude::jetstream_rpc::context::RemoteAddr>, DiscoveryError>;
}

#[cfg(feature = "crush")]
pub mod crush;

pub mod lava;
