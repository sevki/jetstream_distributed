#![deny(missing_docs)]
//! Placement
use std::any::Any;
/// Discovery features
pub mod discovery;
/// Placement features
pub mod placement;

/// A trait for resources that can be placed and discovered.
pub trait Resource: Any {}

// A job is a resource. This is here and not in `compute` so that the dependency runs
// one way: scheduling places what compute describes, and compute names nothing of
// scheduling.
impl<F: 'static> Resource for crate::compute::Job<F> {}

#[cfg(feature = "crush")]
pub mod crush;

pub mod lava;
pub mod prequal;
