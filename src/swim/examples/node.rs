//! A SWIM node you can run as a process, in a cluster that members join and leave.
//!
//! [`Node`] is a table that obeys the merge rule and answers its peers; it has no
//! clock and no socket. What turns it into a member of a cluster is the part this
//! file writes, in plain Rust that Verus never sees and that nothing here proves:
//!
//! * **join**: start knowing only yourself, and `sync` with a seed, naming yourself
//!   as the sender. The seed takes you in as a member, and its reply is the whole
//!   cluster. The seed tells the others by gossip; you never call them to join;
//! * **serve**: accept a connection and hand it to the generated
//!   `SwimService`;
//! * **probe**: every period, `ping` one peer, piggybacking this node's whole view;
//! * **suspect**: a ping that fails or times out makes the node believe the peer
//!   suspect, at the incarnation it had recorded *when the probe began*;
//! * **declare dead**: a suspicion that is not refuted within its timeout becomes
//!   death, but only if the peer is still suspect at that incarnation;
//! * **leave**: record yourself `Left` and tell every peer. A node that is stopped
//!   without doing so is, to the cluster, a node that died.
//!
//! The merge rule, the departure's precedence over a failure verdict, the
//! refutation and the refusal of strangers are the verified and tested parts.
//! *When* to probe, whom, and how long to wait are this file's choices, and
//! `crate::swim::model` says nothing about timing. There is no indirect ping
//! (`ping_req`): a peer that this node alone cannot reach is suspected on this
//! node's word.
//!
//! **Nothing here checks who is calling**: each message says who sent it, and the
//! node believes it, so anyone who can reach a seed is in. Keeping outsiders out is
//! a job for something in front of the service, not for SWIM. Members are addressed
//! by loopback address, `127.0.0.<k>` for member `k`; each listens on port 9100 of
//! its own address. That works on Linux, where all of `127.0.0.0/8` is loopback;
//! elsewhere, give each member its own host instead.
//!
//! Run a cluster in three terminals; the second and third join through a seed:
//!
//! ```text
//! cargo run --example swim_node -- run 1
//! cargo run --example swim_node -- run 2 1
//! cargo run --example swim_node -- run 3 2
//! ```
//!
//! Type `leave` in one to see the others record a departure. Press Ctrl-C in
//! another to see them suspect it and declare it dead. Start it again and watch it
//! be told what it was and outrank that. With no arguments the example does all of
//! that inside one process and asserts it: `cargo run --example swim_node`.

use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::time::{Duration, Instant};

use jetstream::prelude::jetstream_rpc::session::{Session, SingleLaneSession};
use jetstream::prelude::*;
use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{
    Liveness, Swim, Node, Update,
    swim_protocol::{SwimChannel, SwimService},
};
use tokio::net::{TcpListener, TcpStream};
use tokio::task::JoinHandle;

const PORT: u16 = 9100;

/// The timings. Nothing proved depends on them.
#[derive(Clone, Copy)]
struct Timing {
    /// How often this node pings one peer.
    probe_every: Duration,
    /// How long a call may take before the peer is suspected.
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

/// Answer pings and syncs on `127.0.0.<me>:9100` for as long as the task lives.
async fn serve(node: Node, me: u128) -> std::io::Result<()> {
    let listener = TcpListener::bind(SocketAddr::new(addr_of(me), PORT)).await?;
    loop {
        let (stream, _) = listener.accept().await?;
        let node = node.clone();
        tokio::spawn(async move {
            // Who is calling is in each message. Nothing here checks it.
            let session = SingleLaneSession::<SwimChannel, _, _>::service_io(stream);
            let Ok(lane) = Session::<SwimChannel>::accept_lane(&session).await else {
                return;
            };
            let mut service = SwimService { inner: node };
            let _ = jetstream_rpc::server::run(&mut service, lane).await;
        });
    }
}

#[derive(Clone, Copy)]
enum Call {
    /// SWIM's ping, with the view piggybacked.
    Ping,
    /// Push/pull: send the view, get the peer's whole table back. How a node joins.
    Sync,
}

/// One call to `peer`, made from this member's own address, carrying `view`.
async fn call(
    me: u128,
    peer: u128,
    kind: Call,
    view: Vec<Update>,
    within: Duration,
) -> Result<Vec<Update>> {
    let call = async {
        let stream = TcpStream::connect(SocketAddr::new(addr_of(peer), PORT)).await?;
        // The session owns the lane's I/O, so it outlives the channel.
        let session = SingleLaneSession::<SwimChannel, _, _>::client_io(stream);
        let lane = Session::<SwimChannel>::open_lane(&session).await?;
        let channel = SwimChannel::new(64, Box::new(lane));
        channel.negotiate_version(u32::MAX).await?;
        match kind {
            Call::Ping => channel.ping(Context::default(), Id(me), view).await,
            Call::Sync => channel.sync(Context::default(), Id(me), view).await,
        }
    };
    match tokio::time::timeout(within, call).await {
        Ok(reply) => reply,
        Err(_) => Err(std::io::Error::new(std::io::ErrorKind::TimedOut, "call timed out").into()),
    }
}

/// The members this node would probe: everyone it has heard of except itself and
/// those that left. A member declared dead is still probed, because it may come back.
fn peers(node: &Node, me: u128) -> Vec<u128> {
    node.view()
        .into_iter()
        .filter(|u| u.node.0 != me && u.status != Liveness::Left)
        .map(|u| u.node.0)
        .collect()
}

/// Join through `seed`, then probe whoever the cluster turns out to hold, forever.
async fn probe(node: Node, me: u128, seed: Option<u128>, timing: Timing, verbose: bool) {
    // A join is a sync with the seed; its reply is the cluster. The seed may not be
    // up yet, so keep asking.
    if let Some(seed) = seed {
        loop {
            match call(me, seed, Call::Sync, node.view(), timing.probe_timeout).await {
                Ok(table) => {
                    if let Err(e) = node.apply(&table) {
                        eprintln!("[{me}] refused the seed's table: {e}");
                    }
                    break;
                }
                Err(e) => {
                    if verbose {
                        eprintln!("[{me}] cannot reach seed {seed} yet ({e})");
                    }
                    tokio::time::sleep(timing.probe_every).await;
                }
            }
        }
    }
    let mut seen = node.log().len();
    let mut turn = 0usize;
    loop {
        tokio::time::sleep(timing.probe_every).await;
        let peers = peers(&node, me);
        if peers.is_empty() {
            continue;
        }
        let peer = peers[turn % peers.len()];
        turn += 1;
        // The incarnation this node holds *now*, before the ping: a refutation
        // may land while the ping is in flight, and the accusation must not
        // outlive it.
        let held = node.record(Id(peer)).expect("a member").incarnation;
        match call(me, peer, Call::Ping, node.view(), timing.probe_timeout).await {
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

/// Start member `me`: a fresh node that knows only itself, serving and probing,
/// and joining through `seed` if there is one.
fn start(
    me: u128,
    seed: Option<u128>,
    timing: Timing,
    verbose: bool,
) -> (Node, Vec<JoinHandle<()>>) {
    // A node starts at incarnation 0 and keeps nothing on disk. A restart is
    // corrected by the first peer that tells it what the cluster thinks of it.
    let node = Node::new(Id(me));
    let server = {
        let node = node.clone();
        tokio::spawn(async move {
            if let Err(e) = serve(node, me).await {
                eprintln!("[{me}] cannot serve on 127.0.0.{me}:{PORT}: {e}");
            }
        })
    };
    let prober = tokio::spawn(probe(node.clone(), me, seed, timing, verbose));
    (node, vec![server, prober])
}

/// Leave: record the departure and tell every peer this node knows of.
async fn leave(node: &Node, me: u128, timing: Timing) {
    let said = node.leave();
    for peer in peers(node, me) {
        // A peer that cannot be reached is told by gossip from one that can.
        let _ = call(me, peer, Call::Ping, vec![said], timing.probe_timeout).await;
    }
}

fn status(node: &Node, of: u128) -> Option<Liveness> {
    node.record(Id(of)).map(|u| u.status)
}

async fn until(what: &str, mut ready: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while !ready() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
}

fn stop(tasks: &[JoinHandle<()>]) {
    for task in tasks {
        task.abort();
    }
}

/// Members join through different seeds, one leaves, one is stopped, and the
/// one that left comes back.
async fn demonstrate() {
    // 1 starts alone; 2 joins through 1; 3 joins through 2, whose reply is how 3
    // learns of 1. 1 learns of 3 by gossip from 2.
    let (n1, _t1) = start(1, None, FAST, false);
    let (n2, t2) = start(2, Some(1), FAST, false);
    let (n3, t3) = start(3, Some(2), FAST, false);
    until("every member to know every other, alive", || {
        [(&n1, 2), (&n1, 3), (&n2, 3), (&n3, 1)]
            .iter()
            .all(|(n, of)| status(n, *of) == Some(Liveness::Alive))
    })
    .await;
    println!("three members joined through two seeds, and all know each other");

    // 3 leaves, and says so. The others record a departure, not a failure.
    leave(&n3, 3, FAST).await;
    until("1 and 2 to record 3 as having left", || {
        status(&n1, 3) == Some(Liveness::Left) && status(&n2, 3) == Some(Liveness::Left)
    })
    .await;
    stop(&t3);
    // A suspicion that was already running for 3 would have no effect: wait it out.
    tokio::time::sleep(FAST.suspicion * 2).await;
    assert_eq!(status(&n1, 3), Some(Liveness::Left), "left, and not dead");
    println!("member 3 left: members 1 and 2 recorded a departure, not a failure");

    // 2 is stopped without leaving. To the cluster that is a failure.
    stop(&t2);
    until("1 to declare 2 dead", || {
        status(&n1, 2) == Some(Liveness::Dead)
    })
    .await;
    println!("member 2 stopped without leaving: member 1 declared it dead");

    // 3 starts again, as a new process would: incarnation 0, no memory. It joins
    // through 1, which holds it as having left, and says so in its reply; that
    // out-ranks 3's own record, so 3 answers with a higher incarnation.
    let (n3, _t3) = start(3, Some(1), FAST, false);
    until("1 to see 3 alive again", || {
        status(&n1, 3) == Some(Liveness::Alive)
    })
    .await;
    let back = n1.record(Id(3)).unwrap();
    assert!(back.incarnation >= 1, "back only at a higher incarnation");
    assert!(n3.record(Id(3)).unwrap().incarnation >= 1);
    println!(
        "member 3 rejoined: alive again at incarnation {}",
        back.incarnation
    );
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let (me, seed) = match args[..] {
        [] => return demonstrate().await,
        ["run", me] => (me, None),
        ["run", me, seed] => (me, Some(seed)),
        _ => {
            eprintln!("usage: swim_node [run <id> [<seed id>]]");
            std::process::exit(2);
        }
    };
    let me: u128 = me.parse().expect("a member number");
    let seed: Option<u128> = seed.map(|s| s.parse().expect("a member number"));
    assert!((1..=250).contains(&me), "1 <= id <= 250");

    let (node, tasks) = start(me, seed, LIVE, true);
    eprintln!("[{me}] member {me} on 127.0.0.{me}:{PORT}; type `leave` to leave");

    // Typing `leave` leaves. A closed stdin does nothing: only a person saying so
    // is a departure.
    let (told, mut leaving) = tokio::sync::oneshot::channel::<()>();
    std::thread::spawn(move || {
        let mut line = String::new();
        while std::io::stdin().read_line(&mut line).is_ok_and(|n| n > 0) {
            if line.trim() == "leave" {
                let _ = told.send(());
                return;
            }
            line.clear();
        }
    });

    let mut shown = Vec::new();
    loop {
        tokio::select! {
            _ = tokio::time::sleep(LIVE.probe_every * 2) => {}
            Ok(()) = &mut leaving => {
                leave(&node, me, LIVE).await;
                eprintln!("[{me}] left, and told the cluster");
                return;
            }
        }
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
