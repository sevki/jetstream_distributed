//! A SWIM node's view of a failure, and of being wrongly accused.
//!
//! A [`Node`] keeps one record per member: an incarnation number and a status. Two
//! records are compared by a key, a higher incarnation always winning and, at equal
//! incarnations, the more-dead status winning. Everything below is that one rule
//! applied to whichever record arrived.
//!
//! Suspecting a peer and declaring it dead are things a node does about *its own* view,
//! because its own probe failed, so they are methods on the node and not on the wire.
//! What does arrive from outside is a batch of [`Update`]s, merged by [`Node::apply`].
//!
//! Run it with `cargo run --example swim_membership`.

use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{Liveness, Node, Update};

const ME: Id = Id(1);
const PEER: Id = Id(2);

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // A node knows only itself. There is no roster: the peer becomes a member when
    // this node hears of it, here from a message that mentions it.
    let node = Node::new(ME);
    node.apply(&[Update {
        node: PEER,
        incarnation: 0,
        status: Liveness::Alive,
    }])?;

    // A member starts alive at incarnation 0. Nothing is read from disk.
    assert_eq!(
        node.record(PEER),
        Some(Update {
            node: PEER,
            incarnation: 0,
            status: Liveness::Alive
        })
    );

    // A probe of the peer failed: believe it suspect, at the incarnation the node had
    // recorded when the probe began. That is an argument and not re-read, because a
    // probe is slow and a refutation can land while it is in flight.
    assert!(node.suspect(PEER, 0)?);
    println!("peer is suspect: {:?}", node.record(PEER).unwrap().status);

    // The suspicion timed out. This only takes effect if the peer is still suspect at
    // the incarnation the timer was started for.
    assert!(node.declare_dead(PEER, 0)?);
    println!("peer is dead:    {:?}", node.record(PEER).unwrap().status);

    // A weaker report does not undo a death: alive at the same incarnation loses.
    node.apply(&[Update {
        node: PEER,
        incarnation: 0,
        status: Liveness::Alive,
    }])?;
    assert_eq!(node.record(PEER).unwrap().status, Liveness::Dead);

    // Only a higher incarnation does. This is the refutation the peer makes when it
    // hears it is accused: alive at one incarnation above the accusation.
    node.apply(&[Update {
        node: PEER,
        incarnation: 1,
        status: Liveness::Alive,
    }])?;
    let record = node.record(PEER).unwrap();
    assert_eq!((record.incarnation, record.status), (1, Liveness::Alive));
    println!(
        "peer refuted:    incarnation {} {:?}",
        record.incarnation, record.status
    );

    // Applying the same message twice changes nothing the second time, which is what
    // lets gossip survive being delivered at least once and in any order.
    let again = [Update {
        node: PEER,
        incarnation: 1,
        status: Liveness::Alive,
    }];
    node.apply(&again)?;
    node.apply(&again)?;
    assert_eq!(node.record(PEER).unwrap().incarnation, 1);
    Ok(())
}
