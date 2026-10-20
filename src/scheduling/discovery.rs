#[cfg(feature = "service")]
use core::fmt;

use crate::id::Id;

use super::Resource;

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

/// A trait for discovering resources.
#[cfg(feature = "service")]
pub trait Discovery {
    /// Discover a resource and return the remote addresses of the nodes that
    /// host it.
    fn discover<W: Resource>(&self, what: W) -> Result<Vec<Id>, DiscoveryError>;
}
