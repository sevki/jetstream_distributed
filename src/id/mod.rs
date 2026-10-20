#![deny(missing_docs)]
//! One identifier, for a host or a job.
//!
//! An [`Id`] is 128 bits, which is what a UUID and a ULID are, so either converts to
//! one and back without a dependency here: `Id::from(uuid.as_u128())` and
//! `u128::from(id)`.
//!
//! It is a newtype and not an alias, so an `Id` is never a number by accident. It is
//! also one type for both kinds of thing, so the compiler does not tell a host from a
//! job: what an `Id` names is the position it is used in.
//!
//! **Not yet an actor's.** An actor is still named by `ActorId`: a `nat` in the
//! ownership model and a `u64` in `actor::service`. Moving it to `Id` changes the
//! trusted model, and is a change of its own.
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
