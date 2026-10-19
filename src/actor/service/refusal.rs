//! The service's refusals, in the same alphabet the other services use: `NO` is
//! a request the protocol looked at and declined, `ERR` one that names something
//! that does not exist, `FENCED` one the fence stopped.

use crate::actor::steps::ActorRefusal;
use jetstream::prelude::*;

/// Not something this caller may ask for, in this state.
pub(super) fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

/// The request names something that does not exist.
pub(super) fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

/// A step's refusal, in the alphabet above.
pub(super) fn refuse(why: ActorRefusal) -> Error {
    match why {
        ActorRefusal::Fenced => Error::new("not the owner at that epoch").set_code("FENCED"),
        ActorRefusal::NotSent => refuse_err("no such message was sent"),
        ActorRefusal::Duplicate => refuse_no("already accepted"),
        ActorRefusal::AheadOfItsTurn => refuse_no("not yet its turn"),
        ActorRefusal::Exhausted => refuse_no("the sequence space is exhausted"),
    }
}
