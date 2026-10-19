#![deny(missing_docs)]
//! Host types

/// HostId is a unique identifier for a host.
pub type HostId = u128;

trait Lookup {
    type Item;
    fn lookup(&self, host_id: HostId) -> Option<&Self::Item>;
}

#[path = "set_v.rs"]
pub mod set;

pub use set::HostSet;
