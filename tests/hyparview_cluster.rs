//! A simulated cluster of HyParView nodes.
//!
//! The model and the verified handlers are about **one** node. What makes a cluster
//! of them an overlay is a property of how they are connected: the paper's central
//! one is that active views are symmetric, `a` in `b`'s view exactly when `b` is in
//! `a`'s. Nothing proves that. This file runs the nodes against a queue standing in
//! for the network and checks it on what comes out, so it is a **tested** property
//! of these runs, not a theorem.
//!
//! Each message is delivered once, in the order sent. The model allows replay and
//! reordering; this does not exercise them.

use std::collections::{BTreeMap, VecDeque};

use jetstream_distributed::hyparview::service::{ExecParams, Message, Node, Outgoing};
use jetstream_distributed::id::Id;
use jetstream_distributed::membership::PeerSampling;

const PARAMS: ExecParams = ExecParams {
    active_cap: 4,
    passive_cap: 8,
    arwl: 6,
    prwl: 3,
};

struct Cluster {
    nodes: BTreeMap<Id, Node>,
    /// `(from, to, message)`, oldest first.
    network: VecDeque<(Id, Id, Message)>,
}

impl Cluster {
    fn new() -> Self {
        Cluster {
            nodes: BTreeMap::new(),
            network: VecDeque::new(),
        }
    }

    fn send(&mut self, from: Id, out: Vec<Outgoing>) {
        for Outgoing { to, message } in out {
            self.network.push_back((from, to, message));
        }
    }

    /// Add node `id`, joining through `contact` (the first node has none).
    fn add(&mut self, id: u128, contact: Option<u128>) {
        let node = Node::new(Id(id), PARAMS, id as u64);
        let out = contact.map_or_else(Vec::new, |c| node.join_via(Id(c)));
        self.nodes.insert(Id(id), node);
        self.send(Id(id), out);
    }

    /// Deliver until nothing is in flight.
    fn settle(&mut self) {
        let mut delivered = 0;
        while let Some((from, to, message)) = self.network.pop_front() {
            delivered += 1;
            assert!(delivered < 100_000, "the network did not go quiet");
            let out = self.nodes[&to].handle(from, message);
            self.send(to, out);
        }
    }

    /// Every `(a, b)` with `b` in `a`'s active view and `a` not in `b`'s.
    fn asymmetric(&self) -> Vec<(Id, Id)> {
        let mut bad = Vec::new();
        for (&a, node) in &self.nodes {
            for b in node.peers() {
                if !self.nodes[&b].peers().contains(&a) {
                    bad.push((a, b));
                }
            }
        }
        bad
    }
}

#[test]
fn a_cluster_that_joined_through_one_contact_has_symmetric_active_views() {
    let mut c = Cluster::new();
    c.add(1, None);
    for id in 2..=20 {
        c.add(id, Some(1));
        c.settle();
    }
    assert_eq!(c.asymmetric(), vec![], "active views are symmetric");
}

#[test]
fn views_stay_within_their_bounds_and_hold_no_one_twice() {
    let mut c = Cluster::new();
    c.add(1, None);
    for id in 2..=20 {
        c.add(id, Some(1));
        c.settle();
    }
    for (&id, node) in &c.nodes {
        let (active, passive) = (node.peers(), node.passive());
        assert!(active.len() <= PARAMS.active_cap, "{id:?} active {active:?}");
        assert!(passive.len() <= PARAMS.passive_cap, "{id:?} passive {passive:?}");
        assert!(!active.contains(&id) && !passive.contains(&id), "{id:?} lists itself");
        assert!(
            active.iter().all(|p| !passive.contains(p)),
            "{id:?} holds a peer in both views"
        );
    }
}

#[test]
fn a_cluster_that_joined_all_at_once_has_symmetric_active_views() {
    let mut c = Cluster::new();
    c.add(1, None);
    for id in 2..=20 {
        c.add(id, Some(1));
    }
    c.settle();
    assert_eq!(c.asymmetric(), vec![], "active views are symmetric");
}

/// Everyone is reachable from everyone over active links: the overlay did not
/// split. The paper's connectivity claim is probabilistic; this is one run.
#[test]
fn the_overlay_of_one_run_is_connected() {
    let mut c = Cluster::new();
    c.add(1, None);
    for id in 2..=20 {
        c.add(id, Some(1));
        c.settle();
    }
    let mut seen = vec![Id(1)];
    let mut frontier = vec![Id(1)];
    while let Some(n) = frontier.pop() {
        for p in c.nodes[&n].peers() {
            if !seen.contains(&p) {
                seen.push(p);
                frontier.push(p);
            }
        }
    }
    assert_eq!(seen.len(), c.nodes.len(), "reached {seen:?}");
}
