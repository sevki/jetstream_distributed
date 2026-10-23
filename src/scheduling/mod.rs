#![deny(missing_docs)]
//! Placement
use std::any::Any;
/// Discovery features
pub mod discovery;
/// Placement features
pub mod placement;

/// A trait for resources that can be placed and discovered.
pub trait Resource: Any {}

#[cfg(feature = "crush")]
pub mod crush;

pub mod lava;
pub mod prequal;
