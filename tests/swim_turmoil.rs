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
                let node = slot.get_or_init(|| Node::new(Id($id))).clone();
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
            .ping(Context::default(), Id(0), vec![u(2, 0, Liveness::Suspect)])
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
        let a = built.get_or_init(|| Node::new(Id(0))).clone();
        a.apply(&[u(1, 0, Liveness::Alive)])
            .expect("a has heard of b");

        turmoil::partition("a", "b");
        assert!(
            TcpStream::connect(("b", PORT)).await.is_err(),
            "the partition must actually cut b off"
        );
        assert!(a.suspect(Id(1), 0).unwrap(), "a probe failed, so a suspects");
        assert_eq!(a.record(Id(1)), Some(u(1, 0, Liveness::Suspect)));

        turmoil::repair("a", "b");
        connect!("b", _s, ch);
        let theirs = ch.sync(Context::default(), a.id(), a.view()).await.unwrap();
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

/// The sender is whoever the message says. A host nobody has heard of joins by
/// calling, as itself, over the wire, and is a member from then on: there is no
/// roster to be missing from.
#[test]
fn a_caller_is_a_member_from_its_first_call_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    let b_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());
    serve!(sim, "b", 1, b_slot);

    sim.client("x", async move {
        connect!("b", _s, ch);
        let reply = ch.sync(Context::default(), Id(9), vec![]).await.unwrap();
        assert_eq!(
            reply,
            vec![u(1, 0, Liveness::Alive), u(9, 0, Liveness::Alive)],
            "the newcomer is told everyone, itself included"
        );
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let b = b_slot.get().expect("b built its node");
    assert_eq!(b.record(Id(9)), Some(u(9, 0, Liveness::Alive)));
}

/// A node that listens and also makes calls, as a real member does: a turmoil
/// client that spawns its own server.
macro_rules! listen {
    ($node:expr) => {
        let node: Node = $node.clone();
        tokio::spawn(async move {
            let listener = TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT))
                .await
                .expect("bind");
            loop {
                let (stream, _) = listener.accept().await.expect("accept");
                let node = node.clone();
                tokio::spawn(async move {
                    let session = SingleLaneSession::<MembershipChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<MembershipChannel>::accept_lane(&session).await else {
                        return;
                    };
                    let mut service = MembershipService { inner: node };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        });
    };
}

/// A node that knows only itself, as every one starts.
fn open_node(id: u128) -> Node {
    Node::new(Id(id))
}

/// **Joining over the wire, through a member that is not the first, and leaving.**
///
/// `b` starts alone. `c` joins by syncing with `b`. `a` then joins by syncing with
/// `c`, not `b`: it learns `b` from `c`'s reply, and `b` learns of `a` only when
/// `c` next pings it, because membership spreads by gossip like everything else.
/// Then `c` leaves and says so, and `b` records a departure, not a failure, which
/// the suspicion timer `b` had running for `c` cannot undo.
#[test]
fn a_node_joins_through_any_member_and_a_departure_spreads() {
    let mut sim = turmoil::Builder::new().build();
    let b_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());
    let a_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());
    let c_slot: Arc<OnceLock<Node>> = Arc::new(OnceLock::new());

    let b_in = b_slot.clone();
    sim.host("b", move || {
        let b_in = b_in.clone();
        async move {
            let node = b_in.get_or_init(|| open_node(1)).clone();
            listen!(node);
            std::future::pending::<()>().await;
            Ok(())
        }
    });

    let c_in = c_slot.clone();
    sim.client("c", async move {
        let c = c_in.get_or_init(|| open_node(2)).clone();
        listen!(c);
        // Join b: the call is the join, the reply is b's whole table.
        {
            connect!("b", _s, ch);
            let reply = ch.sync(Context::default(), c.id(), c.view()).await.unwrap();
            c.apply(&reply).unwrap();
        }
        // Wait for a to join c, then gossip to b, as a probe would.
        tokio::time::sleep(std::time::Duration::from_secs(2)).await;
        assert_eq!(
            c.record(Id(0)),
            Some(u(0, 0, Liveness::Alive)),
            "c admitted a"
        );
        {
            connect!("b", _s, ch);
            let ack = ch.ping(Context::default(), c.id(), c.view()).await.unwrap();
            c.apply(&ack).unwrap();
        }
        // Leave, and tell b.
        tokio::time::sleep(std::time::Duration::from_secs(1)).await;
        let said = c.leave();
        {
            connect!("b", _s, ch);
            ch.ping(Context::default(), c.id(), vec![said]).await.unwrap();
        }
        Ok(())
    });

    let a_in = a_slot.clone();
    sim.client("a", async move {
        let a = a_in.get_or_init(|| open_node(0)).clone();
        tokio::time::sleep(std::time::Duration::from_secs(1)).await;
        connect!("c", _s, ch);
        let reply = ch.sync(Context::default(), a.id(), a.view()).await.unwrap();
        a.apply(&reply).unwrap();
        assert_eq!(
            a.record(Id(1)),
            Some(u(1, 0, Liveness::Alive)),
            "a learned b from c, which is the only one it called"
        );
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let b = b_slot.get().expect("b built its node");
    assert_eq!(
        b.record(Id(0)),
        Some(u(0, 0, Liveness::Alive)),
        "b heard of a by gossip, having never been called by it"
    );
    assert_eq!(
        b.record(Id(2)),
        Some(u(2, 0, Liveness::Left)),
        "and c's departure arrived as one"
    );
    assert!(
        !b.suspect(Id(2), 0).unwrap() && !b.declare_dead(Id(2), 0).unwrap(),
        "a suspicion timer already running for c cannot turn it into a failure"
    );
}
