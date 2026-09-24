//! The Raft service over Jetstream RPC, on a simulated network.
//!
//! `tests/raft_election.rs` drives the `Peer` directly, which tests the election
//! logic and leaves the generated `#[service]` client and server **compiled but
//! never run** — the same shape of gap as a fuzz target that is only ever built,
//! which this repository calls out elsewhere and should not have here.
//!
//! So this runs a real candidacy across three hosts, and then the case the
//! quorum threshold exists for: a candidate that cannot reach a majority does
//! not get to lead, however sure of itself it is.
//!
//! The replies get the same treatment. A `Ballot`, a `Standing` and an
//! `Appended` are protocol steps in their own right — Raft's term rule is about
//! responses as much as requests — so the last two tests read real ones off the
//! wire and hand them to the `Peer` that asked, which is the only path into its
//! tally and out of a term it has lost.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::{Arc, OnceLock};

use distributed_ownership::raft::service::{
    consensus_protocol::{ConsensusChannel, ConsensusService},
    Acceptance, Appended, Ballot, Consensus, LogEntry, MemoryLog, MemoryLogStore, Peer, Standing,
};
use jetstream::prelude::*;
use jetstream_rpc::session::{Session, SingleLaneSession};
use turmoil::net::{TcpListener, TcpStream};

const PORT: u16 = 9000;

/// Who is which server, by address.
///
/// `turmoil::lookup` resolves a name only inside a live simulation and panics
/// outside one, so every roster here is built inside a host or a client.
fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([
        (turmoil::lookup("a"), 0u64),
        (turmoil::lookup("b"), 1u64),
        (turmoil::lookup("c"), 2u64),
    ])
}

/// The reply a follower gives when it accepts at `term` with `len` entries.
///
/// The term is on the wire now rather than supplied by the caller, so an
/// assertion about a reply checks *when* it was accepted as well as what it
/// says — and `observe_appended` can no longer be handed the wrong term.
fn accepted(term: u64, len: u64) -> Appended {
    Appended::Accepted(Acceptance { term, len })
}

// The `Session` owns the lane's I/O, so a helper that builds one and returns
// only the channel drops it on the way out and the next call fails with
// "session is closed". It has to outlive every request made on the channel,
// which means living in the caller's scope — hence a macro rather than a
// function. Learned the hard way on the ownership service.
macro_rules! connect {
    ($host:expr, $session:ident, $channel:ident) => {
        let stream = TcpStream::connect(($host, PORT))
            .await
            .expect("the peer is listening");
        let $session = SingleLaneSession::<ConsensusChannel, _, _>::client_io(stream);
        let lane = Session::<ConsensusChannel>::open_lane(&$session)
            .await
            .expect("the one lane is available");
        let $channel = ConsensusChannel::new(64, Box::new(lane));
        // "Must be called after `new()` and before any RPC calls", per the
        // generated client.
        $channel
            .negotiate_version(u32::MAX)
            .await
            .expect("the peer speaks this protocol version");
    };
}

/// Run `me` as a Jetstream server for the whole simulation.
macro_rules! serve {
    ($sim:expr, $name:expr, $id:expr) => {
        $sim.host($name, move || async move {
            let peer = Peer::new(
                roster(),
                $id,
                Arc::new(MemoryLog::new()),
                Arc::new(MemoryLogStore::new()),
            )
            .expect("the server is on its own roster");
            let listener =
                TcpListener::bind((IpAddr::from(Ipv4Addr::UNSPECIFIED), PORT)).await?;
            loop {
                let (stream, _) = listener.accept().await?;
                let peer = peer.clone();
                tokio::spawn(async move {
                    let session =
                        SingleLaneSession::<ConsensusChannel, _, _>::service_io(stream);
                    let Ok(lane) = Session::<ConsensusChannel>::accept_lane(&session).await
                    else {
                        return;
                    };
                    let mut service = ConsensusService { inner: peer };
                    let _ = jetstream_rpc::server::run(&mut service, lane).await;
                });
            }
        });
    };
}

/// A candidate that reaches a majority leads, and it does so over the wire.
#[test]
fn a_candidate_wins_an_election_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    serve!(sim, "b", 1);
    serve!(sim, "c", 2);

    // `a` is the candidate: it keeps its own record locally and asks the other
    // two over Jetstream RPC. Shared out so the assertions can read it once the
    // run is over.
    let shared: Arc<OnceLock<Peer>> = Arc::new(OnceLock::new());
    let built = shared.clone();

    sim.client("a", async move {
        let me = built
            .get_or_init(|| {
                Peer::new(
                    roster(),
                    0,
                    Arc::new(MemoryLog::new()),
                    Arc::new(MemoryLogStore::new()),
                )
                .expect("on the roster")
            })
            .clone();

        let term = me.stand_for_election().expect("a fresh server may stand");
        assert_eq!(term, 1);
        assert!(!me.standing_now().leading, "one vote of three is not a majority");

        {
            connect!("b", _sb, chb);
            assert_eq!(
                chb.request_vote(Context::default(), term, 0, 0).await.unwrap(),
                Ballot::Granted(1)
            );
        }
        let leads = me
            .count_ballot(1, term, Ballot::Granted(term))
            .expect("node 1 is on the roster");
        assert!(leads, "two of three is a majority");

        // The third vote is not needed, which is the whole point of a majority —
        // but asking for it must still be answered, and answered the same way.
        {
            connect!("c", _sc, chc);
            assert_eq!(
                chc.request_vote(Context::default(), term, 0, 0).await.unwrap(),
                Ballot::Granted(1)
            );
        }
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let me = shared.get().expect("the client built its peer");
    assert!(me.standing_now().leading);
    assert_eq!(me.standing_now().term, 1);
}

/// **A candidate that cannot reach a majority does not lead.**
///
/// `a` is cut off from both peers before it stands. It votes for itself, cannot
/// collect another, and stays a candidate — which is the behaviour the quorum
/// threshold exists to produce, and the reason a partitioned minority cannot
/// elect a leader that a healthy majority would then have to argue with.
#[test]
fn a_partitioned_minority_does_not_elect_a_leader() {
    let mut sim = turmoil::Builder::new().build();
    serve!(sim, "b", 1);
    serve!(sim, "c", 2);

    let shared: Arc<OnceLock<Peer>> = Arc::new(OnceLock::new());
    let built = shared.clone();

    sim.client("a", async move {
        let me = built
            .get_or_init(|| {
                Peer::new(
                    roster(),
                    0,
                    Arc::new(MemoryLog::new()),
                    Arc::new(MemoryLogStore::new()),
                )
                .expect("on the roster")
            })
            .clone();

        turmoil::partition("a", "b");
        turmoil::partition("a", "c");

        let term = me.stand_for_election().expect("a fresh server may stand");
        assert_eq!(term, 1);

        // Both requests fail at the transport. A candidate that cannot be heard
        // collects nothing, and the failure is the network's rather than the
        // protocol's — which is exactly why the protocol must not treat silence
        // as assent.
        for host in ["b", "c"] {
            let reached = TcpStream::connect((host, PORT)).await;
            assert!(reached.is_err(), "the partition must actually cut {host} off");
        }

        assert!(
            !me.standing_now().leading,
            "a candidate with one vote of three must not lead, however long it waits"
        );
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let me = shared.get().expect("the client built its peer");
    assert!(!me.standing_now().leading);
}

/// **A leader's heartbeats, appends and their replies, over the wire.**
///
/// `request_vote` was the only method a simulated network had ever carried, so
/// `heartbeat`, `standing` and `append_entries` were generated, compiled and
/// never spoken. This elects `a` and then has it lead: a heartbeat, an entry,
/// and the replies fed back through the methods that read them.
#[test]
fn a_leader_leads_over_the_wire() {
    let mut sim = turmoil::Builder::new().build();
    serve!(sim, "b", 1);
    serve!(sim, "c", 2);

    let shared: Arc<OnceLock<Peer>> = Arc::new(OnceLock::new());
    let built = shared.clone();

    sim.client("a", async move {
        let me = built
            .get_or_init(|| {
                Peer::new(
                    roster(),
                    0,
                    Arc::new(MemoryLog::new()),
                    Arc::new(MemoryLogStore::new()),
                )
                .expect("on the roster")
            })
            .clone();

        let term = me.stand_for_election().expect("a fresh server may stand");
        connect!("b", _sb, chb);
        let ballot = chb.request_vote(Context::default(), term, 0, 0).await.unwrap();
        assert_eq!(ballot, Ballot::Granted(1));
        assert!(me.count_ballot(1, term, ballot).unwrap(), "two of three is a majority");

        // A heartbeat, and the reply read back. B is behind nobody, so this
        // tells the leader nothing — which is the case that has to be silent.
        let seen = chb.heartbeat(Context::default(), term, 0).await.unwrap();
        assert_eq!(seen, Standing { term: 1, leading: false });
        assert!(me.observe_standing(seen).unwrap(), "still the leader of term 1");

        // An entry, replicated to B and then acknowledged back to the leader.
        assert_eq!(me.append_command(7).unwrap(), 0, "the first entry lands at index 0");
        let reply = chb
            .append_entries(Context::default(), term, 0, 0, LogEntry { term, value: 7 }, 0)
            .await
            .unwrap();
        assert_eq!(reply, accepted(term, 1));
        assert_eq!(
            me.observe_appended(1, reply).unwrap(),
            Some(1),
            "the leader and one follower are a majority of three, and the entry is \
             of the leader's own term"
        );

        // And `standing` answers the same question without changing anything.
        assert_eq!(
            chb.standing(Context::default()).await.unwrap(),
            Standing { term: 1, leading: false }
        );
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let me = shared.get().expect("the client built its peer");
    assert_eq!(me.standing_now(), Standing { term: 1, leading: true });
    assert_eq!(me.commit(), 1, "one entry committed by a majority of three");
}

/// **A leader that has been overtaken finds out from a reply.**
///
/// The partition case, after the partition heals. `a` leads term 1; while it
/// was away `c` moved to term 5, which `a` can only learn from the answer to
/// something it sent. Without a path for that answer a stale leader goes on
/// leading a term the cluster has left, and the fact that the news is *on the
/// wire* is precisely what makes a reply-reading method necessary rather than
/// tidy.
#[test]
fn a_reply_from_the_wire_deposes_a_stale_leader() {
    let mut sim = turmoil::Builder::new().build();
    serve!(sim, "b", 1);
    serve!(sim, "c", 2);

    let shared: Arc<OnceLock<Peer>> = Arc::new(OnceLock::new());
    let built = shared.clone();

    sim.client("a", async move {
        let me = built
            .get_or_init(|| {
                Peer::new(
                    roster(),
                    0,
                    Arc::new(MemoryLog::new()),
                    Arc::new(MemoryLogStore::new()),
                )
                .expect("on the roster")
            })
            .clone();

        let term = me.stand_for_election().expect("a fresh server may stand");
        connect!("b", _sb, chb);
        let ballot = chb.request_vote(Context::default(), term, 0, 0).await.unwrap();
        assert!(me.count_ballot(1, term, ballot).unwrap());
        assert!(me.standing_now().leading);

        // C is moved to term 5 by a request that is not this leader's business:
        // it stands in for the election `a` slept through.
        connect!("c", _sc, chc);
        assert_eq!(
            chc.request_vote(Context::default(), 5, 0, 0).await.unwrap(),
            Ballot::Granted(5)
        );

        // The leader heartbeats at its own stale term and reads the answer.
        let seen = chc.heartbeat(Context::default(), term, 0).await.unwrap();
        assert_eq!(seen, Standing { term: 5, leading: false });
        assert!(!me.observe_standing(seen).unwrap(), "term 5 has already happened");
        Ok(())
    });

    sim.run().expect("the simulation runs to completion");
    let me = shared.get().expect("the client built its peer");
    assert_eq!(
        me.standing_now(),
        Standing { term: 5, leading: false },
        "a leader deposed by a reply, not by a request"
    );
}
