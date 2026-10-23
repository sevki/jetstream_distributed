#![deny(missing_docs)]
//! One identifier, for everything that has one: a host, an actor, a job.
//!
//! An [`Id`] is 128 bits, which is what a UUID and a ULID are, so either converts to
//! one and back without a dependency here: `Id::from(uuid.as_u128())` and
//! `u128::from(id)`.
//!
//! It is a newtype and not an alias, so an `Id` is never a number by accident. It is
//! also one type for every kind of thing, so the compiler does not tell a host from
//! an actor: what an `Id` names is the position it is used in.
//!
//! [`IdSet`] is the verified set of them.
// `Lookup` is async, which is Jetstream's `async_trait`; the verified core has no
// dependencies, so it is a service's trait and exists with `service`.
#[cfg(feature = "service")]
use jetstream::prelude::async_trait;

/// A trait for looking up an item by its [`Id`].
#[cfg(feature = "service")]
#[async_trait]
pub trait Lookup {
    /// The type of item being looked up.
    type Item;
    /// Look up the item by its [`Id`].
    async fn lookup(&self, id: Id) -> Option<&Self::Item>;
}

#[path = "set_v.rs"]
pub mod set;
#[path = "value_v.rs"]
pub mod value;

pub use set::IdSet;
pub use value::Id;
