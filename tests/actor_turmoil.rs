//! The actor service over Jetstream RPC, on a simulated network.
//!
//! `tests/actor_journal.rs` exercises the guarantees over an in-process Jetstream
//! session (`Host::connect`). This runs the actor's whole story across hosts, on
//! a simulated TCP network: a sender sends, the owner
//! accepts, the actor is handed to another node, the old owner — still believing —
//! is refused, and the new owner picks up from the journal.
//!
//! Each node is its own host, so each call arrives from that node's own address and
//! the service learns who is acting the only way it lets it: from the connection.
//! The steps are sequenced by the simulated clock, which is deterministic.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use jetstream_distributed::id::Id;
use jetstream_distributed::actor::service::{
    actor_protocol::{ActorChannel, ActorService},
    Actor, Host, Receipt, Snapshot,
};
use jetstream_distributed::ownership::service::{MemoryFloor, Offer};
use jetstream::prelude::*;
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9400;

const A: Id = Id(1);
const B: Id = Id(2);
const C: Id = Id(3);

/// Who is which node, by address. Built inside a host or a client:
/// `turmoil::lookup` panics outside a live simulation.
fn roster() -> HashMap<IpAddr, Id> {
    HashMap::from([
        (turmoil::lookup("a"), A),
        (turmoil::lookup("b"), B),
        (turmoil::lookup("c"), C),
    ])
}

/// Wait until `secs` of *simulated* time have passed since the simulation began.
///
/// Absolute rather than a chain of relative sleeps: relative sleeps add up in each
/// client separately, so two clients that mean to act one after the other can land
/// on the same instant and race. Steps are ten seconds apart, far more than the
/// simulated network's latency, so the order is the schedule's.
async fn at(secs: u64) {
    let target = Duration::from_secs(secs);
    let now = turmoil::sim_elapsed().expect("inside a simulation");
    if let Some(wait) = target.checked_sub(now) {
        tokio::time::sleep(wait).await;
    }
}

macro_rules! connect {
    ($session:ident, $channel:ident) => {
        let stream = TcpStream::connect(("actor", PORT))
            .await
            .expect("the actor is listening");
        let $session = SingleLaneSession::<ActorChannel, _, _>::client_io(stream);
        let lane = Session::<ActorChannel>::open_lane(&$session)
            .await
            .expect("the one lane is available");
        let $channel = ActorChannel::new(64, Box::new(lane));
        $channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the actor speaks this version");
    };
}

fn code(e: Error) -> Option<String> {
    e.code().map(String::from)
}

#[test]
fn an_actor_changes_hands_over_the_wire_without_losing_or_repeating_a_message() {
    // Turmoil ends a simulation after ten simulated seconds unless told otherwise,
    // and this schedule runs to t = 70.
    let mut sim = turmoil::Builder::new()
        .simulation_duration(Duration::from_secs(120))
        .build();

    let slot: Arc<OnceLock<Host>> = Arc::new(OnceLock::new());
    let hosted = slot.clone();
    sim.host("actor", move || {
        let hosted = hosted.clone();
        async move {
            let host = hosted
                .get_or_init(|| {
                    Host::new(roster(), A, Arc::new(MemoryFloor::new()))
                        .expect("A is on the roster")
                })
                .clone();
            let listener = TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let host = host.clone();
                tokio::spawn(async move {
                    let session = SingleLaneSession::<ActorChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<ActorChannel>::accept_lane(&session).await else {
                        return;
                    };
                    let mut service = ActorService { inner: host };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        }
    });

    // `C` sends two messages, and a third once the handover is under way.
    sim.client("c", async move {
        at(10).await;
        {
            connect!(_s, ch);
            assert_eq!(ch.send(Context::default(), vec![7]).await.unwrap(), 0);
            assert_eq!(ch.send(Context::default(), vec![9]).await.unwrap(), 1);
        }
        at(35).await;
        connect!(_s, ch);
        assert_eq!(ch.send(Context::default(), vec![11]).await.unwrap(), 2);
        Ok(())
    });

    // `A` hosts the actor, accepts two messages, and hands it over.
    sim.client("a", async move {
        at(20).await;
        {
            connect!(_s, ch);
            assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(1));
            ch.acquire(Context::default(), 1).await.unwrap();
            let r0 = ch.accept(Context::default(), 1, C, 0).await.unwrap();
            assert_eq!(
                r0,
                Receipt {
                    index: 0,
                    state: 7
                }
            );
            let r1 = ch.accept(Context::default(), 1, C, 1).await.unwrap();
            assert_eq!(
                r1,
                Receipt {
                    index: 1,
                    state: 226
                }
            );
        }
        at(30).await;
        {
            connect!(_s, ch);
            ch.begin_transfer(Context::default(), B).await.unwrap();
        }
        at(40).await;
        {
            connect!(_s, ch);
            // Its epoch was burned the moment the transfer began.
            let fenced = ch.accept(Context::default(), 1, C, 2).await.unwrap_err();
            assert_eq!(code(fenced), Some("FENCED".into()));
            assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Revoke(2));
            ch.release(Context::default(), 2).await.unwrap();
        }
        at(60).await;
        // Still believing it hosts the actor at epoch 1.
        connect!(_s, ch);
        let stale = ch.accept(Context::default(), 1, C, 2).await.unwrap_err();
        assert_eq!(code(stale), Some("FENCED".into()));
        Ok(())
    });

    // `B` takes the actor, catches up from the journal, and continues.
    sim.client("b", async move {
        at(50).await;
        {
            connect!(_s, ch);
            assert_eq!(ch.poll(Context::default()).await.unwrap(), Offer::Grant(2));
            ch.acquire(Context::default(), 2).await.unwrap();
            // It does not receive the state; it reads the journal.
            assert_eq!(
                ch.state(Context::default()).await.unwrap(),
                Snapshot { len: 2, state: 226 }
            );
            assert_eq!(
                ch.journal(Context::default(), 0, 100).await.unwrap().len(),
                2
            );
            let r = ch.accept(Context::default(), 2, C, 2).await.unwrap();
            assert_eq!(r.index, 2);
        }
        at(70).await;
        // A redelivery of the first message.
        connect!(_s, ch);
        let dup = ch.accept(Context::default(), 2, C, 0).await.unwrap_err();
        assert_eq!(code(dup), Some("NO".into()));
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");

    let host = slot.get().expect("the actor was built");
    let recs = host.records();
    assert_eq!(
        recs.iter()
            .map(|r| (r.host, r.epoch, r.seq))
            .collect::<Vec<_>>(),
        vec![(A, 1, 0), (A, 1, 1), (B, 2, 2)]
    );
    assert_eq!(host.snapshot().len, 3);
}

/// A caller whose address is not on the roster is refused over the wire.
#[test]
fn a_stranger_is_refused_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    let slot: Arc<OnceLock<Host>> = Arc::new(OnceLock::new());
    let hosted = slot.clone();
    sim.host("actor", move || {
        let hosted = hosted.clone();
        async move {
            let host = hosted
                .get_or_init(|| {
                    Host::new(roster(), A, Arc::new(MemoryFloor::new()))
                        .expect("A is on the roster")
                })
                .clone();
            let listener = TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let host = host.clone();
                tokio::spawn(async move {
                    let session = SingleLaneSession::<ActorChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<ActorChannel>::accept_lane(&session).await else {
                        return;
                    };
                    let mut service = ActorService { inner: host };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        }
    });

    // "a", "b" and "c" exist so the roster can resolve; "x" is not on it.
    for name in ["a", "b", "c"] {
        sim.client(name, async { Ok(()) });
    }
    sim.client("x", async move {
        connect!(_s, ch);
        let err = ch.send(Context::default(), vec![1]).await.unwrap_err();
        assert_eq!(err.code(), Some("NO"));
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    assert!(
        slot.get().expect("built").log().is_empty(),
        "and nothing was recorded"
    );
}
