#![deny(missing_docs)]
//! Traits for placing and discovering resources.
//!
//! This module is in the verified build, which has `std` and `vstd` and nothing
//! else, so it names no Jetstream type: [`Placement`] answers with [`HostId`]s,
//! and turning a host into an address is the service layer's business. What does
//! need an address, [`Discovery`], is behind the `service` feature.
use std::any::Any;
use std::result::Result;

use thiserror::Error;

use crate::host::HostId;

/// Errors that can occur during placement.
#[derive(Debug, Clone, PartialEq, Error)]
pub enum PlacementError {
    /// The requested resource was not found.
    #[error("not found")]
    NotFound,
    /// The requested resource conflicts with an existing resource.
    #[error("conflict")]
    Conflict,
    /// An internal error occurred.
    #[error("internal error")]
    InternalError,
}

/// An error that can occur during discovery.
#[cfg(feature = "service")]
#[derive(Debug, Clone, PartialEq, Error)]
pub enum DiscoveryError {
    /// The requested resource was not found.
    #[error("not found")]
    NotFound,
    /// An internal error occurred.
    #[error("internal error")]
    InternalError,
}

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
