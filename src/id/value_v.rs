//! [`Id`]: the one identifier.
//!
//! # What is trusted
//!
//! Nothing beyond Verus. Equality on an `Id` is defined here, in the language, with
//! vstd's `PartialEqSpecImpl`: executable `==` agrees with the spec equality, which
//! for this struct is equality of the `u128`. (A `derive(PartialEq)` would compile
//! and prove nothing about `==`.)
//!
//! An `Id` is **not** a key for vstd's `HashSet` or `HashMap`: their specifications
//! assume `obeys_key_model::<K>()`, which holds for the built-in key types and
//! cannot be proved for a type of ours. [`IdSet`](super::IdSet) stores the `u128`
//! and presents a `Set<Id>`.
#![allow(unused_imports)]

use std::fmt;

// Only the wire format needs Jetstream, and this module is in the verified build,
// which has no dependencies: the derive is behind `service`.
#[cfg(feature = "service")]
use jetstream::prelude::*;
use vstd::prelude::*;

verus! {

/// An identifier: 128 bits, as a UUID or a ULID is.
// allowed because this is in the verified build, not the wire format
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Clone, Copy, Debug, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "service", derive(JetStreamWireFormat))]
pub struct Id(pub u128);

impl PartialEq for Id {
    fn eq(&self, other: &Id) -> (r: bool)
        ensures
            r == (self.0 == other.0),
    {
        self.0 == other.0
    }
}

impl Eq for Id {}

// What `==` means for an `Id`, for the verifier. vstd's `std_specs` exists only in the
// Verus build, so the impl does too.
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialEqSpecImpl for Id {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Id) -> bool {
        self.0 == other.0
    }
}

/// Two ids are equal exactly when their numbers are.
pub proof fn lemma_id_eq(a: Id, b: Id)
    ensures
        (a == b) <==> (a.0 == b.0),
{
}

} // verus!

impl From<u128> for Id {
    fn from(n: u128) -> Id {
        Id(n)
    }
}

impl From<Id> for u128 {
    fn from(id: Id) -> u128 {
        id.0
    }
}

/// Read as the decimal number [`Display`](fmt::Display) writes.
impl std::str::FromStr for Id {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> std::result::Result<Id, Self::Err> {
        s.parse::<u128>().map(Id)
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
