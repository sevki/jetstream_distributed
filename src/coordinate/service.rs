use jetstream::prelude::*;

use crate::coordinate::Coordinate;

/// What the room says when a subscription ends normally. This is the
/// value a plain `Stream` has nowhere to put.
#[derive(Debug, Clone, JetStreamWireFormat)]
pub struct Closed {
    pub last_seq: u64,
}

#[service(uses(super::{Closed, Coordinate}))]
pub trait Metrics {
    #[subscription]
    fn coordinates(&self, ctx: Context, from: u64) -> Subscription<Coordinate, Closed>;
}

struct CoordinateService {}

impl Metrics for CoordinateService {
    fn coordinates(&self, _ctx: Context, from: u64) -> Subscription<Coordinate, Closed> {
        Subscription::producing(64, async move |producer| {
            loop {
                let coord = Coordinate {
                    vec: vec![],
                    error: 0.0,
                    adjustment: 0.0,
                    height: 0.0,
                };
                producer.send(coord).await.unwrap();
            }
        })
    }
}
