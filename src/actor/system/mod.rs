#![cfg(feature = "service")]

use jetstream::prelude::*;

use crate::{
    actor::service::Actor,
    compute::Job,
    id::Lookup,
    ownership::service::Offer,
    scheduling::{discovery::Discovery, placement::Placement},
};

pub trait ActorSystem<F> {
    type Actor: Actor;
    type ActorRef;
    type Discovery: Discovery<Resource = Self::ActorRef>;
    type Placement: Placement<Resource = Job<F>>;
}

mod iroh;
mod quic;
