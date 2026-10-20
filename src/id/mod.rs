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

trait Lookup {
    type Item;
    fn lookup(&self, id: Id) -> Option<&Self::Item>;
}

#[path = "set_v.rs"]
pub mod set;
#[path = "value_v.rs"]
pub mod value;

pub use set::IdSet;
pub use value::Id;
