//! The SWIM service over Jetstream RPC, on a simulated network.
//!
//! `tests/swim_membership.rs` drives the `Node` directly, which tests the merge
//! rule and the refutation and leaves the generated `#[service]` client and
//! server compiled and never run. This runs SWIM's own story across hosts: a
//! node that cannot reach a peer suspects it, the partition heals, the
//! suspicion reaches the suspected node, and the suspected node — being alive —
//! answers it, and the answer travels back.
//!
//! Every reply here is read off the wire and handed to the node that asked, the
//! only path by which what a peer knows becomes what this node knows.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::{Arc, OnceLock};

use jetstream::prelude::*;
use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{
    Liveness, Membership, Node, Update,
    membership_protocol::{MembershipChannel, MembershipService},
};
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9100;

/// Who is which member, by address. Built inside a host or a client:
/// `turmoil::lookup` panics outside a live simulation.
fn roster() -> HashMap<IpAddr, Id> {
    HashMap::from([
        (turmoil::lookup("a"), Id(0)),
        (turmoil::lookup("b"), Id(1)),
        (turmoil::lookup("c"), Id(2)),
    ])
}

fn u(node: u128, incarnation: u64, status: Liveness) -> Update {
    Update {
        node: Id(node),
        incarnation,
        status,
    }
}

// The `Session` owns the lane's I/O, so it has to outlive every request made on
// the channel -- hence a macro rather than a function. The same lesson the
// ownership and Raft suites record.
macro_rules! connect {
    ($host:expr, $session:ident, $channel:ident) => {
        let stream = TcpStream::connect(($host, PORT))
            .await
            .expect("the peer is listening");
        let $session = SingleLaneSession::<MembershipChannel, _, _>::client_io(stream);
        let lane = Session::<MembershipChannel>::open_lane(&$session)
            .await
            .expect("the one lane is available");
        let $channel = MembershipChannel::new(64, Box::new(lane));
        $channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the peer speaks this protocol version");
    };
}

/// Run `$id` as a Jetstream server for the whole simulation, publishing its
/// node into `$slot` so the assertions can read it once the run is over.
macro_rules! serve {
    ($sim:expr, $name:expr, $id:expr, $slot:expr) => {
        let slot: Arc<OnceLock<Node>> = $slot.clone();
        $sim.host($name, move || {
            let slot = slot.clone();
            async move {
                let node = slot
                    .get_or_init(|| Node::new(roster(), Id($id)).expect("on its own roster"))
                    .clone();
                let listener =
                    TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
                loop {
                    let (stream, _) = listener.accept().await?;
                    let node = node.clone();
                    tokio::spawn(async move {
                        let session =
                            SingleLaneSession::<MembershipChannel, _, _>::service_io(stream);
                        let Ok(lane) = Session::<MembershipChannel>::accept_lane(&session).await
                        else {
                            return;
                        };
                        let mut service = MembershipService { inner: node };
                        let _ = jetstream_rpc::server::run(&mut service, lane).await;
                    });
                }
            }
        });
    };
}

/// A ping carries a rumour and brings back the receiver's own standing.
#[test]
fn a_ping_carries_a_rumour_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    let b_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());
    serve!(sim, "b", 1, b_slot);

    sim.client("a", async move {
        connect!("b", _s, ch);
        let ack = ch
            .ping(Context::default(), vec![u(2, 0, Liveness::Suspect)])
            .await
            .unwrap();
        assert_eq!(
            ack,
            vec![u(1, 0, Liveness::Alive), u(2, 0, Liveness::Suspect)],
            "the receiver answers about itself and about the member it was told of"
        );
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let b = b_slot.get().expect("b built its node");
    assert_eq!(
        b.record(Id(2)),
        Some(u(2, 0, Liveness::Suspect)),
        "and it learned the rumour"
    );
}

/// **SWIM's story, end to end.**
///
/// `a` cannot reach `b`, so it suspects it. The partition heals and `a` syncs
/// with `b`, pushing its table — which says `b` is suspect. `b` is alive, so it
/// refutes at incarnation 1 and tells `a` so in the reply; `a` reads that reply
/// and clears its suspicion. Nothing else could have: at incarnation 0 the
/// suspicion out-ranks `Alive`, and only the suspected node can raise its own
/// incarnation.
#[test]
fn a_suspected_node_that_is_alive_refutes_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    let b_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());
    serve!(sim, "b", 1, b_slot);

    let a_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());
    let built = a_slot.clone();
    sim.client("a", async move {
        let a = built
            .get_or_init(|| Node::new(roster(), Id(0)).expect("on the roster"))
            .clone();

        turmoil::partition("a", "b");
        assert!(
            TcpStream::connect(("b", PORT)).await.is_err(),
            "the partition must actually cut b off"
        );
        assert!(a.suspect(Id(1), 0).unwrap(), "a probe failed, so a suspects");
        assert_eq!(a.record(Id(1)), Some(u(1, 0, Liveness::Suspect)));

        turmoil::repair("a", "b");
        connect!("b", _s, ch);
        let theirs = ch.sync(Context::default(), a.view()).await.unwrap();
        a.apply(&theirs).unwrap();
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let a = a_slot.get().expect("the client built its node");
    let b = b_slot.get().expect("b built its node");

    assert_eq!(
        b.record(Id(1)),
        Some(u(1, 1, Liveness::Alive)),
        "b refuted its own suspicion"
    );
    assert_eq!(
        a.record(Id(1)),
        Some(u(1, 1, Liveness::Alive)),
        "and a read the refutation off the reply, which out-ranked its suspicion"
    );
}

/// A stranger on the network is refused by the service, over the wire.
#[test]
fn a_caller_off_the_roster_is_refused_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    let b_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());
    serve!(sim, "b", 1, b_slot);

    // "x" is a host the roster has never heard of.
    sim.client("x", async move {
        connect!("b", _s, ch);
        let err = ch
            .ping(Context::default(), vec![u(2, 0, Liveness::Dead)])
            .await
            .unwrap_err();
        assert_eq!(err.code(), Some("NO"));
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let b = b_slot.get().expect("b built its node");
    assert_eq!(
        b.record(Id(2)),
        Some(u(2, 0, Liveness::Alive)),
        "and nothing it said was applied"
    );
}
