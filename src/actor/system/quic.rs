#![cfg(all(feature = "service", feature = "quic"))]

use std::collections::HashMap;
use std::marker::PhantomData;

use crate::actor::service::ActorRef;
use crate::compute::{Instant, Job};
use crate::scheduling::discovery::{Discovery, DiscoveryError};
use crate::scheduling::lava::{LifetimePredictor, Scheduler};
use crate::scheduling::placement::{Placement, PlacementError};
use crate::{
    actor::{
        service::{Actor, Receipt, Record, Snapshot},
        system::ActorSystem,
    },
    id::Id,
    ownership::service::Offer,
};
use jetstream::prelude::*;

pub(crate) struct QuicActorSystem<F, P> {
    _f: PhantomData<(F, P)>,
}

pub(crate) struct QuicActor {}

impl Actor for QuicActor {
    async fn poll(&self, ctx: Context) -> Result<Offer> {
        todo!()
    }

    async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()> {
        todo!()
    }

    async fn begin_transfer(&self, ctx: Context, to: Id) -> Result<()> {
        todo!()
    }

    async fn release(&self, ctx: Context, epoch: u64) -> Result<()> {
        todo!()
    }

    async fn send(&self, ctx: Context, body: u64) -> Result<u64> {
        todo!()
    }

    async fn accept(&self, ctx: Context, epoch: u64, sender: Id, seq: u64) -> Result<Receipt> {
        todo!()
    }

    async fn state(&self, ctx: Context) -> Result<Snapshot> {
        todo!()
    }

    async fn journal(&self, ctx: Context, from: u64, limit: u64) -> Result<Vec<Record>> {
        todo!()
    }
}

pub struct QuicDirectory<F, P: LifetimePredictor<F>> {
    placed_actors: HashMap<ActorRef, url::Url>,
    scheduler: Scheduler<F, P>,
}

impl<F, P> QuicDirectory<F, P>
where
    P: LifetimePredictor<F>,
{
    pub fn new(scheduler: Scheduler<F, P>) -> Self {
        Self {
            placed_actors: HashMap::default(),
            scheduler,
        }
    }
}

#[async_trait]
impl<F, P> Discovery for QuicDirectory<F, P>
where
    F: Sync + Send + 'static,
    P: LifetimePredictor<F> + Sync,
{
    type Resource = ActorRef;
    type Location = url::Url;

    async fn discover(
        &self,
        what: Self::Resource,
    ) -> std::result::Result<Vec<Self::Location>, DiscoveryError> {
        self.placed_actors
            .get(&what)
            .cloned()
            .ok_or(DiscoveryError::NotFound)
            .map(|url| vec![url])
    }
}

#[async_trait]
impl<F, P: LifetimePredictor<F>> Placement for QuicDirectory<F, P>
where
    F: Sync + Send + 'static,
    Self: Send + Sync,
{
    type Resource = Job<F>;

    async fn place(
        &mut self,
        what: Self::Resource,
    ) -> std::result::Result<Vec<Id>, PlacementError> {
        self.scheduler
            .place(what, Instant::now())
            .map(|id| vec![id])
    }
}

impl<F, P> ActorSystem<F> for QuicActorSystem<F, P>
where
    F: Sync + Send + 'static,
    P: LifetimePredictor<F> + std::marker::Sync + std::marker::Send,
{
    type Actor = QuicActor;
    type ActorRef = ActorRef;
    type Discovery = QuicDirectory<F, P>;
    type Placement = QuicDirectory<F, P>;
}
