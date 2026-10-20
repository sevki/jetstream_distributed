//! The composed service over Jetstream RPC, on a simulated network.
//!
//! `tests/composed_handover.rs` drives the `Coordinator` directly. This runs the
//! one thing the composition exists to enforce across hosts, through the
//! generated client and server: **the privilege does not move while the actor is
//! held, and does once it is released.** It is also what shows the coordinator's
//! gate — an async mutex held across the layers' own `await`s — yields futures
//! the generated server can actually run.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use jetstream_distributed::id::Id;
use jetstream_distributed::composed::service::{
    composed_protocol::{ComposedChannel, ComposedService},
    Composed, Coordinator,
};
use jetstream_distributed::ownership::service::{MemoryFloor, Offer};
use jetstream::prelude::*;
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9300;

const A: Id = Id(0);
const B: Id = Id(1);

/// Who is which node, by address. Built inside a host or a client:
/// `turmoil::lookup` panics outside a live simulation.
fn roster() -> HashMap<IpAddr, Id> {
    HashMap::from([(turmoil::lookup("a"), A), (turmoil::lookup("b"), B)])
}

/// Wait until `secs` of *simulated* time have passed since the simulation began.
///
/// Absolute rather than a chain of relative sleeps: relative sleeps add up in
/// each client separately, so two clients that mean to act "one after the other"
/// can land on the same instant and race. Steps here are ten seconds apart, far
/// more than the simulated network's latency, so the order is the schedule's and
/// not the scheduler's.
async fn at(secs: u64) {
    let target = Duration::from_secs(secs);
    let now = turmoil::sim_elapsed().expect("inside a simulation");
    if let Some(wait) = target.checked_sub(now) {
        tokio::time::sleep(wait).await;
    }
}

macro_rules! connect {
    ($session:ident, $channel:ident) => {
        let stream = TcpStream::connect(("coord", PORT))
            .await
            .expect("the coordinator is listening");
        let $session = SingleLaneSession::<ComposedChannel, _, _>::client_io(stream);
        let lane = Session::<ComposedChannel>::open_lane(&$session)
            .await
            .expect("the one lane is available");
        let $channel = ComposedChannel::new(64, Box::new(lane));
        $channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the coordinator speaks this version");
    };
}

#[test]
fn the_privilege_moves_only_after_the_release_over_the_wire() {
    // Turmoil ends a simulation after ten simulated seconds unless told
    // otherwise, and this schedule runs to t = 90.
    let mut sim = turmoil::Builder::new()
        .simulation_duration(Duration::from_secs(120))
        .build();

    let slot: Arc<OnceLock<Coordinator>> = Arc::new(OnceLock::new());
    let hosted = slot.clone();
    sim.host("coord", move || {
        let hosted = hosted.clone();
        async move {
            let coordinator = hosted
                .get_or_init(|| {
                    Coordinator::star(roster(), A, Arc::new(MemoryFloor::new()), A)
                        .expect("a star rooted at A")
                })
                .clone();
            let listener = TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let coordinator = coordinator.clone();
                tokio::spawn(async move {
                    let session = SingleLaneSession::<ComposedChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<ComposedChannel>::accept_lane(&session).await else {
                        return;
                    };
                    let mut service = ComposedService { inner: coordinator };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        }
    });

    // B asks for the privilege at t = 10.
    sim.client("b", async move {
        at(10).await;
        {
            connect!(_s, ch);
            ch.request_cs(Context::default()).await.unwrap();
            assert_eq!(ch.make_request(Context::default()).await.unwrap(), A);
        }
        // Offered the actor once A releases at t = 50, but cannot take it until
        // the privilege arrives at t = 80.
        at(60).await;
        connect!(_s, ch);
        assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(2));
        let early = ch.acquire(Context::default(), 2).await.unwrap_err();
        assert_eq!(
            early.code(),
            Some("NO"),
            "offered the actor, but not yet elected"
        );
        at(90).await;
        ch.acquire(Context::default(), 2).await.unwrap();
        Ok(())
    });

    sim.client("a", async move {
        at(20).await;
        connect!(_s, ch);
        assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(1));
        ch.acquire(Context::default(), 1).await.unwrap();
        ch.receive_request(Context::default(), B).await.unwrap();
        ch.begin_transfer(Context::default(), B).await.unwrap();

        // The routing layer would pass the privilege; the coupling refuses,
        // because the outgoing owner has not acknowledged the revoke.
        let held = ch.assign_privilege(Context::default()).await.unwrap_err();
        assert_eq!(held.code(), Some("NO"), "the actor is mid-transfer");

        at(50).await;
        ch.release(Context::default(), 2).await.unwrap();

        // Released. The privilege may move now.
        at(80).await;
        assert_eq!(ch.assign_privilege(Context::default()).await.unwrap(), B);
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let c = slot.get().expect("the coordinator was built");
    assert_eq!(c.privilege(), B);
    assert!(c.well_formed());
}
