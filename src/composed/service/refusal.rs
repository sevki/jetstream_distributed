//! The service's refusals, in the same alphabet the other services use: `NO` is
//! a request the protocol looked at and declined, `ERR` one that names something
//! that does not exist.

use crate::composed::steps::CoupledRefusal;
use jetstream::prelude::*;

pub(super) fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

pub(super) fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

pub(super) fn refuse(why: CoupledRefusal) -> Error {
    match why {
        CoupledRefusal::ActorNotReleased => {
            refuse_no("the actor has not been released; the privilege may not move")
        }
        CoupledRefusal::NotPrivileged => {
            refuse_no("only the node holding the privilege may acquire")
        }
        CoupledRefusal::NothingToSeize => {
            refuse_no("nothing to seize: the target already holds it")
        }
        CoupledRefusal::NotANode => refuse_err("not a node"),
        CoupledRefusal::NotSeized => refuse_no("this node owes no reconciliation"),
        CoupledRefusal::NotStale => refuse_no("this node's belief is not stale"),
    }
}
