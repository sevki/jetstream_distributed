//! The service's refusals, in the same alphabet the other services use: `NO` is
//! a request the protocol looked at and declined, `ERR` one that names something
//! that does not exist.

use crate::raymond::steps::RayRefusal;
use jetstream::prelude::*;

pub(super) fn refuse_no(what: &str) -> Error {
    Error::new(what).set_code("NO")
}

pub(super) fn refuse_err(what: &str) -> Error {
    Error::new(what).set_code("ERR")
}

pub(crate) fn refuse(why: RayRefusal) -> Error {
    match why {
        RayRefusal::HoldsPrivilege => refuse_no("this node holds the privilege; nobody to ask"),
        RayRefusal::EmptyQueue => refuse_no("nothing is queued"),
        RayRefusal::AlreadyAsked => refuse_no("a request is already outstanding"),
        RayRefusal::NotSent => refuse_no("no such request was sent"),
        RayRefusal::NotPrivileged => refuse_no("this node does not hold the privilege"),
        RayRefusal::NotHolder => refuse_no("this node does not believe it holds the privilege"),
        RayRefusal::InCriticalSection => refuse_no("this node is inside its critical section"),
        RayRefusal::NotInCriticalSection => refuse_no("this node is not in its critical section"),
        RayRefusal::HeadIsSelf => refuse_no("the head of the queue is this node"),
        RayRefusal::HeadIsNotSelf => refuse_no("the head of the queue is not this node"),
        RayRefusal::HeadNotANode => refuse_err("the head of the queue is not a node"),
        RayRefusal::NotANode => refuse_err("not a node"),
    }
}
