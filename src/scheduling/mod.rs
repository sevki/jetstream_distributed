#![deny(missing_docs)]
//! Traits for placing and discovering resources.
use std::any::Any;

use jetstream::prelude::*;
use jetstream_rpc::context::RemoteAddr;
use std::result::Result;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Error)]
/// Errors that can occur during placement and discovery.
pub enum PlacementError {
    #[error("not found")]
    /// The requested resource was not found.
    NotFound,
    #[error("conflict")]
    /// The requested resource conflicts with an existing resource.
    Conflict,
    #[error("internal error")]
    /// An internal error occurred.
    InternalError,
}

#[derive(Debug, Clone, PartialEq, Error)]
/// An error that can occur during discovery.
pub enum DiscoveryError {
    #[error("not found")]
    /// The requested resource was not found.
    NotFound,
    #[error("internal error")]
    /// An internal error occurred.
    InternalError,
}

/// A trait for resources that can be placed and discovered.
pub trait Resource: Any {}

/// A trait for placing resources.
pub trait Placement {
    /// Place a resource and return the remote addresses of the nodes that
    /// should host it.
    fn place<W: Resource>(&self, what: W) -> Result<Vec<RemoteAddr>, PlacementError>;
}

/// A trait for discovering resources.
pub trait Discovery {
    /// Discover a resource and return the remote addresses of the nodes that
    /// host it.
    fn discover<W: Resource>(&self, what: W) -> Result<Vec<RemoteAddr>, DiscoveryError>;
}

#[cfg(feature = "crush")]
pub mod crush;

pub mod lava;
