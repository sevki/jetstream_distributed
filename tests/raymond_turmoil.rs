//! The Raymond routing service over Jetstream RPC, on a simulated network.
//!
//! `tests/raymond_routing.rs` drives the `Router` directly, which tests the
//! routing rules and leaves the generated `#[service]` client and server
//! compiled and never run. This runs the textbook request path across hosts:
//!
//! ```text
//! request:  D -> B -> A -> C[token]
//! token:    C -> A -> B -> D
//! ```
//!
//! Each node is its own host, so each call arrives from that node's own address
//! and the router learns who is acting the only way the service lets it: from
//! the connection. The steps are sequenced by the simulated clock, which is
//! deterministic, so the run is the same every time.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use distributed_ownership::raymond::service::{
    routing_protocol::{RoutingChannel, RoutingService},
    Router, Routing,
};
use jetstream::prelude::*;
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9200;

const A: u64 = 0;
const B: u64 = 1;
const C: u64 = 2;
const D: u64 = 3;

/// Who is which node, by address. Built inside a host or a client:
/// `turmoil::lookup` panics outside a live simulation.
fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([
        (turmoil::lookup("a"), A),
        (turmoil::lookup("b"), B),
        (turmoil::lookup("c"), C),
        (turmoil::lookup("d"), D),
    ])
}

macro_rules! connect {
    ($session:ident, $channel:ident) => {
        let stream = TcpStream::connect(("router", PORT))
            .await
            .expect("the router is listening");
        let $session = SingleLaneSession::<RoutingChannel, _, _>::client_io(stream);
        let lane = Session::<RoutingChannel>::open_lane(&$session)
            .await
            .expect("the one lane is available");
        let $channel = RoutingChannel::new(64, Box::new(lane));
        $channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the router speaks this protocol version");
    };
}

#[test]
fn the_privilege_travels_back_along_the_request_path_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();

    let slot: Arc<OnceLock<Router>> = Arc::new(OnceLock::new());
    let hosted = slot.clone();
    sim.host("router", move || {
        let hosted = hosted.clone();
        async move {
            // C holds the privilege; A points at C, B at A, D at B.
            let router = hosted
                .get_or_init(|| {
                    Router::new(roster(), C, HashMap::from([(A, C), (B, A), (D, B)]))
                        .expect("a tree rooted at C")
                })
                .clone();
            let listener = TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let router = router.clone();
                tokio::spawn(async move {
                    let session = SingleLaneSession::<RoutingChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<RoutingChannel>::accept_lane(&session).await else {
                        return;
                    };
                    let mut service = RoutingService { inner: router };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        }
    });

    // Each node acts at its own simulated instant, from its own address. The
    // request goes D -> B -> A -> C at t = 1..3; C hands the privilege to A at
    // t = 4, A to B at t = 5 and B to D at t = 6; D enters at t = 7.
    sim.client("d", async move {
        tokio::time::sleep(Duration::from_secs(1)).await;
        {
            connect!(_s, ch);
            ch.request_cs(Context::default()).await.unwrap();
            assert_eq!(ch.make_request(Context::default()).await.unwrap(), B);
        }
        tokio::time::sleep(Duration::from_secs(6)).await;
        connect!(_s, ch);
        // D believes it holds the privilege, and does: it was told in the same
        // step that B handed it over.
        let standing = ch.standing(Context::default()).await.unwrap();
        assert!(standing.privileged);
        assert_eq!(standing.holder, D);
        ch.enter_cs(Context::default()).await.unwrap();
        assert!(ch.standing(Context::default()).await.unwrap().using);
        Ok(())
    });
    sim.client("b", async move {
        tokio::time::sleep(Duration::from_secs(2)).await;
        {
            connect!(_s, ch);
            ch.receive_request(Context::default(), D).await.unwrap();
            assert_eq!(ch.make_request(Context::default()).await.unwrap(), A);
        }
        tokio::time::sleep(Duration::from_secs(3)).await;
        connect!(_s, ch);
        assert_eq!(ch.assign_privilege(Context::default()).await.unwrap(), D);
        Ok(())
    });
    sim.client("a", async move {
        tokio::time::sleep(Duration::from_secs(3)).await;
        {
            connect!(_s, ch);
            ch.receive_request(Context::default(), B).await.unwrap();
            assert_eq!(ch.make_request(Context::default()).await.unwrap(), C);
        }
        tokio::time::sleep(Duration::from_secs(2)).await;
        connect!(_s, ch);
        assert_eq!(ch.assign_privilege(Context::default()).await.unwrap(), B);
        Ok(())
    });
    sim.client("c", async move {
        tokio::time::sleep(Duration::from_secs(4)).await;
        connect!(_s, ch);
        ch.receive_request(Context::default(), A).await.unwrap();
        assert_eq!(ch.assign_privilege(Context::default()).await.unwrap(), A);
        // C no longer holds the privilege, and finds out by asking.
        assert!(!ch.standing(Context::default()).await.unwrap().privileged);
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");

    let router = slot.get().expect("the router was built");
    assert!(router.well_formed());
    assert_eq!(
        router.privilege(),
        D,
        "the privilege came all the way back to D"
    );
    assert!(
        router.standing_of(D).unwrap().using,
        "and D is in its critical section"
    );
}

/// A caller whose address is not on the roster is refused over the wire.
#[test]
fn a_stranger_is_refused_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    let slot: Arc<OnceLock<Router>> = Arc::new(OnceLock::new());
    let hosted = slot.clone();
    sim.host("router", move || {
        let hosted = hosted.clone();
        async move {
            let router = hosted
                .get_or_init(|| Router::star(roster(), C).expect("a star rooted at C"))
                .clone();
            let listener = TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let router = router.clone();
                tokio::spawn(async move {
                    let session = SingleLaneSession::<RoutingChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<RoutingChannel>::accept_lane(&session).await else {
                        return;
                    };
                    let mut service = RoutingService { inner: router };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        }
    });

    // "a" ... "d" exist so the roster can resolve; "x" is not on it.
    for name in ["a", "b", "c", "d"] {
        sim.client(name, async { Ok(()) });
    }
    sim.client("x", async move {
        connect!(_s, ch);
        let err = ch.request_cs(Context::default()).await.unwrap_err();
        assert_eq!(err.code(), Some("NO"));
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    assert!(
        slot.get().expect("built").log().is_empty(),
        "and nothing was recorded"
    );
}
