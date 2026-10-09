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

use distributed_ownership::composed::service::{
    composed_protocol::{ComposedChannel, ComposedService},
    Composed, Coordinator,
};
use distributed_ownership::ownership::service::{MemoryFloor, Offer, Registry};
use distributed_ownership::raymond::service::Router;
use jetstream::prelude::*;
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9300;

const A: u64 = 0;
const B: u64 = 1;

/// Who is which node, by address. Built inside a host or a client:
/// `turmoil::lookup` panics outside a live simulation.
fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([(turmoil::lookup("a"), A), (turmoil::lookup("b"), B)])
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
    let mut sim = turmoil::Builder::new().build();

    let slot: Arc<OnceLock<Coordinator>> = Arc::new(OnceLock::new());
    let hosted = slot.clone();
    sim.host("coord", move || {
        let hosted = hosted.clone();
        async move {
            let coordinator = hosted
                .get_or_init(|| {
                    let registry = Registry::new(roster(), A, Arc::new(MemoryFloor::new()))
                        .expect("A is on the roster");
                    let router = Router::star(roster(), A).expect("a star rooted at A");
                    Coordinator::new(registry, router, roster())
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

    // B asks for the privilege at t = 1.
    sim.client("b", async move {
        tokio::time::sleep(Duration::from_secs(1)).await;
        {
            connect!(_s, ch);
            ch.request_cs(Context::default()).await.unwrap();
            assert_eq!(ch.make_request(Context::default()).await.unwrap(), A);
        }
        // Offered the actor once A releases at t = 5, but cannot take it until
        // the privilege arrives at t = 8.
        tokio::time::sleep(Duration::from_secs(5)).await;
        connect!(_s, ch);
        assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(2));
        let early = ch.acquire(Context::default(), 2).await.unwrap_err();
        assert_eq!(
            early.code(),
            Some("NO"),
            "offered the actor, but not yet elected"
        );
        tokio::time::sleep(Duration::from_secs(3)).await;
        ch.acquire(Context::default(), 2).await.unwrap();
        Ok(())
    });

    sim.client("a", async move {
        tokio::time::sleep(Duration::from_secs(2)).await;
        connect!(_s, ch);
        assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(1));
        ch.acquire(Context::default(), 1).await.unwrap();
        ch.receive_request(Context::default(), B).await.unwrap();
        ch.begin_transfer(Context::default(), B).await.unwrap();

        // The routing layer would pass the privilege; the coupling refuses,
        // because the outgoing owner has not acknowledged the revoke.
        let held = ch.assign_privilege(Context::default()).await.unwrap_err();
        assert_eq!(held.code(), Some("NO"), "the actor is mid-transfer");

        tokio::time::sleep(Duration::from_secs(3)).await;
        ch.release(Context::default(), 2).await.unwrap();

        // Released. The privilege may move now.
        tokio::time::sleep(Duration::from_secs(3)).await;
        assert_eq!(ch.assign_privilege(Context::default()).await.unwrap(), B);
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let c = slot.get().expect("the coordinator was built");
    assert_eq!(c.router().privilege(), B);
    assert!(c.router().well_formed());
}
