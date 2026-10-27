//! A SWIM node you can run as a process, and the same nodes checked in one.
//!
//! [`Node`] is a table that obeys the merge rule and answers its peers; it has no
//! clock and no socket. What turns it into a member of a cluster is the part this
//! file writes, in plain Rust that Verus never sees and that nothing here proves:
//!
//! * **serve**: accept a connection, hand it to the generated `MembershipService`;
//! * **probe**: every period, `ping` one peer, piggybacking this node's whole view;
//! * **suspect**: a ping that fails or times out makes the node believe the peer
//!   suspect, at the incarnation it had recorded *when the probe began*;
//! * **declare dead**: a suspicion that is not refuted within its timeout becomes
//!   death, but only if the peer is still suspect at that incarnation.
//!
//! The merge rule, the refutation and the refusal of strangers are the verified
//! and tested parts. *When* to probe, whom, and how long to wait are this file's
//! choices, and `crate::swim::model` says nothing about timing. There is no
//! indirect ping (`ping_req`): a peer that this node alone cannot reach is
//! suspected on this node's word.
//!
//! Members are addressed by loopback address, `127.0.0.<id>`, because a node knows
//! its caller by address and a roster is a map from addresses to members. Every
//! member listens on port 9100 of its own address and connects from it. That works
//! on Linux, where all of `127.0.0.0/8` is loopback; elsewhere, give each member
//! its own host instead.
//!
//! Run a cluster of three in three terminals:
//!
//! ```text
//! cargo run --example swim_node -- run 1 3
//! cargo run --example swim_node -- run 2 3
//! cargo run --example swim_node -- run 3 3
//! ```
//!
//! then stop one and watch the others suspect it and declare it dead, start it
//! again and watch it be told what it was and outrank that. With no arguments it
//! does the same thing inside one process and asserts it:
//! `cargo run --example swim_node`.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::time::{Duration, Instant};

use jetstream::prelude::jetstream_rpc::session::{Session, SingleLaneSession};
use jetstream::prelude::*;
use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{
    Liveness, Membership, Node,
    membership_protocol::{MembershipChannel, MembershipService},
};
use tokio::net::{TcpListener, TcpSocket};
use tokio::task::JoinHandle;

const PORT: u16 = 9100;

/// The timings. Nothing proved depends on them.
#[derive(Clone, Copy)]
struct Timing {
    /// How often this node pings one peer.
    probe_every: Duration,
    /// How long a ping may take before the peer is suspected.
    probe_timeout: Duration,
    /// How long a suspicion stands before it becomes death.
    suspicion: Duration,
}

const LIVE: Timing = Timing {
    probe_every: Duration::from_secs(1),
    probe_timeout: Duration::from_millis(500),
    suspicion: Duration::from_secs(5),
};

const FAST: Timing = Timing {
    probe_every: Duration::from_millis(40),
    probe_timeout: Duration::from_millis(100),
    suspicion: Duration::from_millis(200),
};

fn addr_of(member: u128) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(127, 0, 0, member as u8))
}

/// Members `1..=n`, each known by its own loopback address.
fn roster(n: u128) -> HashMap<IpAddr, Id> {
    (1..=n).map(|m| (addr_of(m), Id(m))).collect()
}

/// Answer pings and syncs on `127.0.0.<me>:9100` for as long as the task lives.
async fn serve(node: Node, me: u128) -> std::io::Result<()> {
    let listener = TcpListener::bind(SocketAddr::new(addr_of(me), PORT)).await?;
    loop {
        let (stream, _) = listener.accept().await?;
        let node = node.clone();
        tokio::spawn(async move {
            // The session reads the peer's address off the stream, and `Node`
            // looks it up in the roster: that is where "who is calling" comes from.
            let session = SingleLaneSession::<MembershipChannel, _, _>::service_io(stream);
            let Ok(lane) = Session::<MembershipChannel>::accept_lane(&session).await else {
                return;
            };
            let mut service = MembershipService { inner: node };
            let _ = jetstream_rpc::server::run(&mut service, lane).await;
        });
    }
}

/// One ping to `peer`, made from this member's own address, carrying `view`.
async fn ping(
    me: u128,
    peer: u128,
    view: Vec<jetstream_distributed::swim::service::Update>,
    within: Duration,
) -> Result<Vec<jetstream_distributed::swim::service::Update>> {
    let call = async {
        // Bind the source so the peer sees `127.0.0.<me>` and finds us on its roster.
        let socket = TcpSocket::new_v4()?;
        socket.bind(SocketAddr::new(addr_of(me), 0))?;
        let stream = socket.connect(SocketAddr::new(addr_of(peer), PORT)).await?;
        // The session owns the lane's I/O, so it outlives the channel.
        let session = SingleLaneSession::<MembershipChannel, _, _>::client_io(stream);
        let lane = Session::<MembershipChannel>::open_lane(&session).await?;
        let channel = MembershipChannel::new(64, Box::new(lane));
        channel.negotiate_version(u32::MAX).await?;
        channel.ping(Context::default(), view).await
    };
    match tokio::time::timeout(within, call).await {
        Ok(reply) => reply,
        Err(_) => Err(std::io::Error::new(std::io::ErrorKind::TimedOut, "ping timed out").into()),
    }
}

/// Probe the other members in turn, forever.
async fn probe(node: Node, me: u128, members: u128, timing: Timing, verbose: bool) {
    let peers: Vec<u128> = (1..=members).filter(|&m| m != me).collect();
    let mut seen = node.log().len();
    for peer in peers.iter().cycle() {
        tokio::time::sleep(timing.probe_every).await;
        let peer = *peer;
        // The incarnation this node holds *now*, before the ping: a refutation
        // may land while the ping is in flight, and the accusation must not
        // outlive it.
        let held = node.record(Id(peer)).expect("a member").incarnation;
        match ping(me, peer, node.view(), timing.probe_timeout).await {
            // The ack is the peer's own word about everyone the ping mentioned,
            // including itself: the evidence that it is up.
            Ok(ack) => {
                if let Err(e) = node.apply(&ack) {
                    eprintln!("[{me}] refused a reply from {peer}: {e}");
                }
            }
            Err(e) => {
                if node.suspect(Id(peer), held).unwrap_or(false) && verbose {
                    eprintln!("[{me}] ping to {peer} failed ({e}); suspecting it");
                }
                let node = node.clone();
                tokio::spawn(async move {
                    tokio::time::sleep(timing.suspicion).await;
                    // A no-op unless the peer is still suspect at `held`.
                    let _ = node.declare_dead(Id(peer), held);
                });
            }
        }
        if verbose {
            let log = node.log();
            for event in &log[seen..] {
                eprintln!("[{me}] {event:?}");
            }
            seen = log.len();
        }
    }
}

/// Start member `me` of `members`: a fresh node, serving and probing.
fn start(me: u128, members: u128, timing: Timing, verbose: bool) -> (Node, Vec<JoinHandle<()>>) {
    // A node starts at incarnation 0 and keeps nothing on disk. A restart is
    // corrected by the first peer that tells it what the cluster thinks of it.
    let node = Node::new(roster(members), Id(me)).expect("on its own roster");
    let server = {
        let node = node.clone();
        tokio::spawn(async move {
            if let Err(e) = serve(node, me).await {
                eprintln!("[{me}] cannot serve on 127.0.0.{me}:{PORT}: {e}");
            }
        })
    };
    let prober = tokio::spawn(probe(node.clone(), me, members, timing, verbose));
    (node, vec![server, prober])
}

fn status(node: &Node, of: u128) -> Liveness {
    node.record(Id(of)).expect("a member").status
}

async fn until(what: &str, mut ready: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while !ready() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
}

/// Three members in one process: let them find each other, kill one, watch the
/// others declare it dead, bring it back.
async fn demonstrate() {
    let (n1, _t1) = start(1, 3, FAST, false);
    let (n2, _t2) = start(2, 3, FAST, false);
    let (_n3, t3) = start(3, 3, FAST, false);

    // Everyone alive, and the probes have run long enough to have heard from all.
    tokio::time::sleep(Duration::from_millis(400)).await;
    assert_eq!(status(&n1, 3), Liveness::Alive);
    assert_eq!(status(&n2, 3), Liveness::Alive);
    println!("three members, all alive");

    // Member 3 stops answering. Its listener goes with its task.
    for task in &t3 {
        task.abort();
    }
    until("both survivors to declare 3 dead", || {
        status(&n1, 3) == Liveness::Dead && status(&n2, 3) == Liveness::Dead
    })
    .await;
    println!("member 3 stopped: members 1 and 2 declared it dead");
    assert_eq!(status(&n1, 2), Liveness::Alive, "and nobody else with it");

    // Member 3 starts again as a new process would: incarnation 0, no memory.
    // Its first caller tells it the cluster has it dead at 0; that out-ranks its
    // own record, so it answers with incarnation 1, and the ack carries that back.
    let (n3, _t3) = start(3, 3, FAST, false);
    until("both survivors to see 3 alive again", || {
        status(&n1, 3) == Liveness::Alive && status(&n2, 3) == Liveness::Alive
    })
    .await;
    let again = n1.record(Id(3)).unwrap();
    assert!(
        again.incarnation >= 1,
        "alive again only at a higher incarnation"
    );
    assert!(n3.record(Id(3)).unwrap().incarnation >= 1);
    println!(
        "member 3 restarted: alive again at incarnation {}",
        again.incarnation
    );
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        [] => demonstrate().await,
        ["run", me, members] => {
            let me: u128 = me.parse().expect("a member number");
            let members: u128 = members.parse().expect("a member count");
            assert!(
                (1..=members).contains(&me) && members <= 250,
                "1 <= id <= n <= 250"
            );
            let (node, tasks) = start(me, members, LIVE, true);
            eprintln!("[{me}] member {me} of {members}, on 127.0.0.{me}:{PORT}");
            let mut shown = Vec::new();
            loop {
                tokio::time::sleep(LIVE.probe_every * 5).await;
                let view = node.view();
                if view != shown {
                    let line: Vec<String> = view
                        .iter()
                        .map(|u| format!("{}:{:?}@{}", u.node.0, u.status, u.incarnation))
                        .collect();
                    println!("[{me}] view: {}", line.join(" "));
                    shown = view;
                }
                if tasks.iter().any(|t| t.is_finished()) {
                    std::process::exit(1);
                }
            }
        }
        _ => {
            eprintln!("usage: swim_node [run <id> <members>]");
            std::process::exit(2);
        }
    }
}
