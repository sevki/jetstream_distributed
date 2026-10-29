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

/// **A known gap, pinned.** A `Neighbor` is always granted, so one that is still in
/// flight when its sender is evicted restores a link the other end is about to drop.
///
/// With one active slot each: `A` and `B` hold each other, each with a redundant
/// `Neighbor` to the other in flight (the pair a terminal `ForwardJoin` queues at
/// both ends). Then a newcomer `C` joins at `A`, which evicts `B` and tells it to
/// disconnect. Delivered in the order sent, `B` hears `Disconnect` and drops `A`,
/// while `A` hears `B`'s old `Neighbor` and takes `B` back: `A` lists `B`, `B` does
/// not list `A`, and nothing is left in flight to repair it.
///
/// The model has no handshake to tell a stale `Neighbor` from a fresh one, so this
/// is the model's behaviour and not a bug in the node; the test exists so that
/// closing the gap is a visible change (it will then need to assert symmetry).
#[test]
fn an_overlapping_neighbor_and_disconnect_leave_a_one_sided_link() {
    let one_slot = ExecParams {
        active_cap: 1,
        passive_cap: 4,
        arwl: 3,
        prwl: 1,
    };
    let (a, b, cc) = (Id(1), Id(2), Id(3));
    let mut c = Cluster::new();
    for id in [a, b, cc] {
        c.nodes.insert(id, Node::new(id, one_slot, id.0 as u64));
    }
    // A and B hold each other.
    let out = c.nodes[&a].handle(b, Message::Neighbor);
    c.send(a, out);
    let out = c.nodes[&b].handle(a, Message::Neighbor);
    c.send(b, out);
    assert_eq!(c.nodes[&a].peers(), vec![b]);
    assert_eq!(c.nodes[&b].peers(), vec![a]);
    // Each still has a `Neighbor` for the other in flight, sent before C arrives.
    c.network.push_back((a, b, Message::Neighbor));
    c.network.push_back((b, a, Message::Neighbor));
    // C joins at A: A evicts B and says so.
    let out = c.nodes[&a].handle(cc, Message::Join);
    c.send(a, out);
    c.settle();

    let a_lists_b = c.nodes[&a].peers().contains(&b);
    let b_lists_a = c.nodes[&b].peers().contains(&a);
    assert!(
        a_lists_b && !b_lists_a,
        "expected the one-sided link this test pins; A->B {a_lists_b}, B->A {b_lists_a}"
    );
}
