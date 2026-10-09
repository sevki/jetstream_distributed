//! The service's refusals, in the same alphabet the other services use: `NO` is
//! a request the protocol looked at and declined, `ERR` one that names something
//! that does not exist.

use crate::swim::steps::SwimRefusal;
use jetstream::prelude::*;

/// Not something this caller may ask for.
pub(super) fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

/// The request names something that does not exist, or is not one the protocol
/// has.
pub(super) fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

/// The incarnation space is exhausted.
///
/// The model counts incarnations in `nat`; this counts them in `u64`. See
/// [`crate::swim::steps::refute_step`].
fn exhausted() -> Error {
    Error::new("the incarnation space is exhausted").set_code("NO")
}

/// A step's refusal, in the alphabet above.
pub(super) fn refuse(why: SwimRefusal) -> Error {
    match why {
        SwimRefusal::Exhausted => exhausted(),
    }
}
