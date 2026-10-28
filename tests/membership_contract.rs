//! The membership contract, checked against SWIM's `Node`.
//!
//! `membership::PeerSampling` and `membership::FailureDetector` are plain Rust:
//! Verus checks SWIM's merge rule and steps, not the layer a consumer reads. What
//! each method promises is in its doc, and this file is the check on it.
//!
//! The checks are written against the traits and not against `Node`
//! ([`obeys_the_contract`]), so a second implementation is held to the same ones by
//! calling the same function. The scenarios put a real node in each state a
//! consumer can see it in. The last test is SWIM's own, stronger promise, which a
//! partial-view protocol would not make.

use std::collections::BTreeSet;

use jetstream_distributed::id::Id;
use jetstream_distributed::membership::{FailureDetector, Liveness, PeerSampling};
use jetstream_distributed::swim::service::{Node, Update};

const ME: u128 = 1;

fn say(node: u128, incarnation: u64, status: Liveness) -> Update {
    Update {
        node: Id(node),
        incarnation,
        status,
    }
}

/// A node that has heard of members 2, 3 and 4, all alive.
fn cluster() -> Node {
    let n = Node::new(Id(ME));
    n.apply(&[
        say(2, 0, Liveness::Alive),
        say(3, 0, Liveness::Alive),
        say(4, 0, Liveness::Alive),
    ])
    .unwrap();
    n
}

/// Everything the traits promise, for any implementation.
fn obeys_the_contract<D: FailureDetector>(d: &D) {
    let me = d.local();
    let peers = d.peers();
    let standings = d.standings();

    let peer_set: BTreeSet<Id> = peers.iter().copied().collect();
    assert_eq!(peer_set.len(), peers.len(), "a peer is listed once: {peers:?}");
    assert!(!peer_set.contains(&me), "a node is not its own peer");

    let known: BTreeSet<Id> = standings.iter().map(|&(n, _)| n).collect();
    assert_eq!(
        known.len(),
        standings.len(),
        "a member has one standing: {standings:?}"
    );
    assert!(
        peer_set.is_subset(&known),
        "every peer has a standing: peers {peers:?}, standings {standings:?}"
    );
    assert!(known.contains(&me), "a node has a standing for itself");

    for &(node, standing) in &standings {
        assert_eq!(
            d.standing(node),
            Some(standing),
            "`standing` agrees with `standings` about {node:?}"
        );
    }
    assert_eq!(d.standing(Id(9999)), None, "a stranger has no standing");
}

#[test]
fn a_node_that_has_heard_of_nobody_obeys_the_contract() {
    let n = Node::new(Id(ME));
    obeys_the_contract(&n);
    assert!(n.peers().is_empty());
    assert_eq!(n.standing(Id(ME)), Some(Liveness::Alive));
}

#[test]
fn a_node_with_live_peers_obeys_the_contract() {
    let n = cluster();
    obeys_the_contract(&n);
    assert_eq!(n.peers(), vec![Id(2), Id(3), Id(4)]);
}

#[test]
fn a_node_that_suspects_and_condemns_obeys_the_contract() {
    let n = cluster();
    n.suspect(Id(3), 0).unwrap();
    obeys_the_contract(&n);
    n.declare_dead(Id(3), 0).unwrap();
    obeys_the_contract(&n);
    assert_eq!(n.standing(Id(3)), Some(Liveness::Dead));
}

#[test]
fn a_node_that_has_left_obeys_the_contract() {
    let n = cluster();
    n.leave();
    obeys_the_contract(&n);
    assert_eq!(n.standing(Id(ME)), Some(Liveness::Left));
}

/// SWIM's promise, beyond the contract: it still gossips with a member it
/// suspects (that is how a wrong suspicion is refuted) and stops gossiping with
/// one it has declared dead or that has left. Both stay in `standings`, because a
/// consumer that acts on a departure has to hear that it happened.
#[test]
fn swim_probes_the_suspect_and_drops_the_dead_and_the_departed() {
    let n = cluster();
    n.suspect(Id(2), 0).unwrap();
    n.suspect(Id(3), 0).unwrap();
    n.declare_dead(Id(3), 0).unwrap();
    n.apply(&[say(4, 0, Liveness::Left)]).unwrap();

    assert_eq!(n.peers(), vec![Id(2)], "suspect stays, dead and left go");
    let standings: Vec<_> = n.standings();
    for (node, standing) in [
        (Id(2), Liveness::Suspect),
        (Id(3), Liveness::Dead),
        (Id(4), Liveness::Left),
    ] {
        assert!(
            standings.contains(&(node, standing)),
            "{node:?} is still reported as {standing:?}: {standings:?}"
        );
    }
}
