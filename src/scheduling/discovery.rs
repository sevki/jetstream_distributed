#![cfg(feature = "service")]
use core::fmt;

use crate::id::Id;
use jetstream::prelude::*;
use std::result::Result;

use super::Resource;

/// An error that can occur during discovery.
#[derive(Debug, Clone, PartialEq)]
pub enum DiscoveryError {
    /// The requested resource was not found.
    NotFound,
    /// An internal error occurred.
    InternalError,
}

impl fmt::Display for DiscoveryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            DiscoveryError::NotFound => "not found",
            DiscoveryError::InternalError => "internal error",
        })
    }
}

impl std::error::Error for DiscoveryError {}

/// A trait for discovering resources.
#[async_trait]
pub trait Discovery {
    /// The type of resource to discover.
    type Resource: Resource + Send + Sync;
    /// The type of location to return.
    type Location: Send + Sync;
    /// Discover a resource and return the remote addresses of the nodes that
    /// host it.
    async fn discover(&self, what: Self::Resource) -> Result<Vec<Self::Location>, DiscoveryError>;
}
