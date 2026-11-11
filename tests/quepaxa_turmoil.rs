//! QuePaxa's recorders and proposers over Jetstream RPC, on a simulated network.
//!
//! `tests/consensus_contract.rs` runs the protocol in-process, with injected faults,
//! which tests the protocol and leaves the generated `Recorder` client and server
//! compiled and never run. This runs them: three recorders serve the real wire protocol,
//! proposers reach them through generated channels, and the network is cut.
//!
//! Identity is the connection's: each recorder's roster maps a host's address to a
//! proposer index, and the proposers pass no node number in any request.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::{Arc, OnceLock};

use jetstream::prelude::*;
use jetstream_distributed::quepaxa::service::proposer::Config;
use jetstream_distributed::quepaxa::service::{
    Proposer, RecorderNode,
    recorder_protocol::{RecorderChannel, RecorderService},
};
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9200;

/// Who is which proposer, by address. Built inside a host or a client:
/// `turmoil::lookup` panics outside a live simulation.
fn roster() -> HashMap<IpAddr, u32> {
    HashMap::from([
        (turmoil::lookup("p0"), 0),
        (turmoil::lookup("p1"), 1),
        (turmoil::lookup("a"), 2),
        (turmoil::lookup("b"), 3),
        (turmoil::lookup("c"), 4),
    ])
}

// The `Session` owns the lane's I/O, so it has to outlive every request made on the
// channel, hence a macro rather than a function.
macro_rules! connect {
    ($host:expr, $session:ident, $channel:ident) => {
        let stream = TcpStream::connect(($host, PORT))
            .await
            .expect("the recorder is listening");
        let $session = SingleLaneSession::<RecorderChannel, _, _>::client_io(stream);
        let lane = Session::<RecorderChannel>::open_lane(&$session)
            .await
            .expect("the one lane is available");
        let $channel = RecorderChannel::new(64, Box::new(lane));
        $channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the recorder speaks this version");
    };
}

/// Serve a recorder on `$name` for the whole simulation, publishing its node into `$slot`.
macro_rules! serve {
    ($sim:expr, $name:expr, $slot:expr) => {
        let slot: Arc<OnceLock<RecorderNode>> = $slot.clone();
        $sim.host($name, move || {
            let slot = slot.clone();
            async move {
                let node = slot.get_or_init(|| RecorderNode::new(roster())).clone();
                let listener =
                    TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
                loop {
                    let (stream, _) = listener.accept().await?;
                    let node = node.clone();
                    tokio::spawn(async move {
                        let session =
                            SingleLaneSession::<RecorderChannel, _, _>::service_io(stream);
                        let Ok(lane) = Session::<RecorderChannel>::accept_lane(&session).await
                        else {
                            return;
                        };
                        let mut service = RecorderService { inner: node };
                        let _ = jetstream_rpc::server::run(&mut service, lane).await;
                    });
                }
            }
        });
    };
}

fn config(index: u32, leader: bool, seed: u64) -> Config {
    Config {
        index,
        leader,
        hedge: std::time::Duration::ZERO,
        seed: Some(seed),
    }
}

/// Two proposers race for the same slot over the wire, one of them the designated
/// leader. Both are told the same value, and every recorder that learns it learns that.
#[test]
fn two_proposers_decide_the_same_value_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    let slots: Vec<Arc<OnceLock<RecorderNode>>> =
        (0..3).map(|_| Arc::new(OnceLock::new())).collect();
    serve!(sim, "a", slots[0]);
    serve!(sim, "b", slots[1]);
    serve!(sim, "c", slots[2]);

    let decided: Arc<std::sync::Mutex<Vec<u64>>> = Arc::default();
    for (name, index, leader, value) in [("p0", 0u32, true, 100u64), ("p1", 1, false, 200)] {
        let decided = decided.clone();
        sim.client(name, async move {
            connect!("a", sa, ca);
            connect!("b", sb, cb);
            connect!("c", sc, cc);
            let _keep = (&sa, &sb, &sc);
            let proposer = Proposer::new(
                config(index, leader, 11 + u64::from(index)),
                vec![ca, cb, cc],
            );
            let value = proposer.propose(0, value).await.expect("a quorum answers");
            proposer.announce(0, value).await;
            decided.lock().unwrap().push(value);
            Ok(())
        });
    }
    sim.run().expect("the simulation runs to completion");

    let decided = decided.lock().unwrap().clone();
    assert_eq!(decided.len(), 2);
    assert_eq!(
        decided[0], decided[1],
        "both proposers were told the same value"
    );
    assert!(
        [100, 200].contains(&decided[0]),
        "and it was one of the two proposed"
    );
    for slot in &slots {
        let node = slot.get().expect("built");
        if let Some(v) = node.decided(0) {
            assert_eq!(
                v, decided[0],
                "a recorder that learned it learned that value"
            );
        }
    }
}

/// With one recorder cut off from both proposers, the other two are a majority and the
/// slot is still decided. Nothing waits on the one that cannot be reached.
#[test]
fn a_cut_off_recorder_does_not_stop_a_decision() {
    let mut sim = turmoil::Builder::new().build();
    let slots: Vec<Arc<OnceLock<RecorderNode>>> =
        (0..3).map(|_| Arc::new(OnceLock::new())).collect();
    serve!(sim, "a", slots[0]);
    serve!(sim, "b", slots[1]);
    serve!(sim, "c", slots[2]);

    sim.client("p0", async move {
        // Connected to all three first, so that `c` is a recorder the proposer holds a
        // channel to and then cannot reach: its calls never answer.
        connect!("a", sa, ca);
        connect!("b", sb, cb);
        connect!("c", sc, cc);
        let _keep = (&sa, &sb, &sc);
        turmoil::partition("p0", "c");
        let proposer = Proposer::new(config(0, true, 3), vec![ca, cb, cc]);
        let value = proposer
            .propose(0, 7)
            .await
            .expect("a quorum of two still answers");
        assert_eq!(value, 7, "alone, the leader's proposal is what is decided");
        proposer.announce(0, value).await;
        Ok(())
    });
    sim.run().expect("the simulation runs to completion");

    assert_eq!(slots[0].get().unwrap().decided(0), Some(7));
    assert_eq!(slots[1].get().unwrap().decided(0), Some(7));
    assert_eq!(
        slots[2].get().unwrap().decided(0),
        None,
        "the recorder that was cut off never heard, and nothing waited for it"
    );
}
