//! A cluster that grows and shrinks: nodes join through an admission policy, and
//! leave by saying so.
//!
//! `tests/swim_membership.rs` is the closed cluster, whose members are fixed when
//! a node is built. These are the other kind, [`Node::admitting`], and the claims
//! that go with it:
//!
//! * a join is the first call from an address the policy lets in, and the identity
//!   it is given comes from the policy and the connection, never from the request;
//! * a member learns of the others by hearing about them, and a closed node still
//!   refuses to;
//! * a departure is `Left`, which a late failure verdict cannot undo, which is
//!   different from `Dead`, and which only the departed node, coming back at a
//!   higher incarnation, can reverse;
//! * the cluster is bounded, and an address already speaking as one member cannot
//!   be given a second identity.
//!
//! `swim::proofs::merge` proves the departure's precedence for the model's
//! `merge`; what is exercised here is the service's glue around it: the roster,
//! the policy and the write that must not be refuted.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;
use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{
    Admission, Event, Liveness, MAX_UPDATES, Membership, Node, Update,
};

fn addr(last: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(10, 0, 0, last))
}

fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

fn u(node: u128, incarnation: u64, status: Liveness) -> Update {
    Update {
        node: Id(node),
        incarnation,
        status,
    }
}

/// Addresses `10.0.0.1` to `10.0.0.9` are members `1` to `9`; nothing else is.
fn nine() -> Admission {
    Arc::new(|a| match a {
        IpAddr::V4(v4) if v4.octets()[..3] == [10, 0, 0] && (1..=9).contains(&v4.octets()[3]) => {
            Some(Id(v4.octets()[3] as u128))
        }
        _ => None,
    })
}

/// Member `me`, knowing only itself, in a cluster anyone `nine` admits may join.
fn lone(me: u8) -> Node {
    Node::admitting(
        HashMap::from([(addr(me), Id(me as u128))]),
        Id(me as u128),
        nine(),
    )
    .expect("on its own roster")
}

/// A new address is admitted by its first call, as the member the policy says,
/// and the `sync` reply is how it learns who is there.
#[tokio::test]
async fn a_join_is_the_first_call_and_the_reply_is_the_cluster() {
    let seed = lone(1);
    assert_eq!(
        seed.view(),
        vec![u(1, 0, Liveness::Alive)],
        "alone at first"
    );

    let reply = seed
        .sync(from(addr(2)), vec![u(2, 0, Liveness::Alive)])
        .await
        .unwrap();
    assert_eq!(
        reply,
        vec![u(1, 0, Liveness::Alive), u(2, 0, Liveness::Alive)],
        "the newcomer is told everyone, itself included"
    );
    assert_eq!(seed.record(Id(2)), Some(u(2, 0, Liveness::Alive)));

    // The newcomer, built knowing only itself, learns the seed from that reply.
    let joiner = lone(2);
    assert_eq!(joiner.record(Id(1)), None, "it has not heard of the seed");
    joiner.apply(&reply).unwrap();
    assert_eq!(joiner.record(Id(1)), Some(u(1, 0, Liveness::Alive)));
}

/// The identity a joiner gets is what the policy says about its address. It
/// cannot claim another by what it puts in the message.
#[tokio::test]
async fn a_joiner_cannot_claim_to_be_someone_else() {
    let seed = lone(1);
    // Address 3 is member 3. It says, in its updates, whatever it likes about 5...
    seed.ping(from(addr(3)), vec![u(5, 0, Liveness::Dead)])
        .await
        .unwrap();
    // ...which is gossip about 5, not a claim to be 5.
    assert_eq!(seed.record(Id(5)), Some(u(5, 0, Liveness::Dead)));

    // 5 itself, when it calls, is admitted as 5 by its own address, and hears it.
    let reply = seed
        .ping(from(addr(5)), vec![u(5, 0, Liveness::Alive)])
        .await
        .unwrap();
    assert_eq!(
        reply,
        vec![u(1, 0, Liveness::Alive), u(5, 0, Liveness::Dead)],
        "Dead at 0 out-ranks Alive at 0, and is what the cluster holds"
    );
}

/// An address the policy does not admit is a stranger, as in a closed cluster, and
/// nothing it said was applied.
#[tokio::test]
async fn an_address_the_policy_refuses_is_still_a_stranger() {
    let seed = lone(1);
    let off = addr(77);
    for r in [
        seed.ping(from(off), vec![u(2, 0, Liveness::Dead)]).await,
        seed.sync(from(off), vec![u(2, 0, Liveness::Dead)]).await,
    ] {
        assert_eq!(r.unwrap_err().code(), Some("NO"));
    }
    assert_eq!(seed.record(Id(2)), None, "and nothing it said was applied");
    assert_eq!(seed.view(), vec![u(1, 0, Liveness::Alive)]);
}

/// A closed node still refuses a batch naming a member it was not built with:
/// growth is a property of `admitting`, not of every node.
#[tokio::test]
async fn a_closed_node_still_refuses_to_learn_of_strangers() {
    let closed = Node::new(HashMap::from([(addr(1), Id(1)), (addr(2), Id(2))]), Id(1)).unwrap();
    let err = closed
        .ping(from(addr(2)), vec![u(9, 0, Liveness::Alive)])
        .await
        .unwrap_err();
    assert_eq!(err.code(), Some("ERR"));
    assert_eq!(closed.record(Id(9)), None);
}

/// A second address cannot take over a member number that already has one.
#[tokio::test]
async fn a_second_address_cannot_speak_as_an_existing_member() {
    // A policy that admits two addresses as the same member.
    let both: Admission = Arc::new(|a| (a == addr(2) || a == addr(3)).then_some(Id(2)));
    let seed = Node::admitting(HashMap::from([(addr(1), Id(1))]), Id(1), both).unwrap();
    seed.ping(from(addr(2)), vec![]).await.unwrap();
    let err = seed.ping(from(addr(3)), vec![]).await.unwrap_err();
    assert_eq!(err.code(), Some("NO"));
    seed.ping(from(addr(2)), vec![])
        .await
        .expect("and the first address is unaffected");
}

/// The cluster is bounded by what one message can carry, so a sync reply always
/// fits.
#[tokio::test]
async fn the_cluster_is_bounded_by_the_message_limit() {
    let open: Admission = Arc::new(|_| None);
    let n = Node::admitting(HashMap::from([(addr(1), Id(1))]), Id(1), open).unwrap();
    // Members only heard about count against the bound too.
    let crowd: Vec<Update> = (2..=(MAX_UPDATES as u128))
        .map(|i| u(i, 0, Liveness::Alive))
        .collect();
    n.apply(&crowd).unwrap();
    assert_eq!(n.view().len(), MAX_UPDATES);
    let err = n.apply(&[u(1_000_000, 0, Liveness::Alive)]).unwrap_err();
    assert_eq!(err.code(), Some("ERR"));
    assert_eq!(n.record(Id(1_000_000)), None, "refused whole");
}

/// A node that leaves is `Left`, at the incarnation it held, and says so.
#[test]
fn leaving_records_left_at_the_held_incarnation() {
    let n = lone(1);
    let said = n.leave();
    assert_eq!(said, u(1, 0, Liveness::Left));
    assert_eq!(n.record(Id(1)), Some(u(1, 0, Liveness::Left)));
    assert_eq!(n.log(), vec![Event::Departed { incarnation: 0 }]);
    // Leaving twice says the same and logs once.
    assert_eq!(n.leave(), said);
    assert_eq!(n.log().len(), 1);
}

/// **The departure is not refuted.** A node that hears something about itself
/// that out-ranks its record answers with a higher incarnation; a node that has
/// just announced its departure must not answer its own announcement that way.
#[test]
fn a_node_does_not_refute_its_own_departure() {
    let n = lone(1);
    n.leave();
    n.apply(&[u(1, 0, Liveness::Left)]).unwrap();
    assert_eq!(n.record(Id(1)), Some(u(1, 0, Liveness::Left)));
    assert!(
        !n.log().iter().any(|e| matches!(e, Event::Refuted { .. })),
        "a departure is not an accusation"
    );
}

/// What is already in flight when a member leaves cannot turn the departure into
/// a failure or a recovery: a late suspicion, a late `Dead`, an old `Alive`.
#[tokio::test]
async fn a_late_failure_report_does_not_undo_a_departure() {
    let b = lone(2);
    b.apply(&[u(3, 0, Liveness::Alive)]).unwrap();
    b.apply(&[u(3, 0, Liveness::Left)]).unwrap();
    assert_eq!(b.record(Id(3)), Some(u(3, 0, Liveness::Left)));

    // Its own probe timer, started before the departure arrived, fires:
    assert!(
        !b.suspect(Id(3), 0).unwrap(),
        "a suspicion at 0 changes nothing"
    );
    assert!(!b.declare_dead(Id(3), 0).unwrap(), "nor does a death at 0");
    // Late gossip from a peer that never heard:
    b.ping(
        from(addr(1)),
        vec![u(3, 0, Liveness::Dead), u(3, 0, Liveness::Alive)],
    )
    .await
    .unwrap();
    assert_eq!(b.record(Id(3)), Some(u(3, 0, Liveness::Left)));
}

/// `Left` and `Dead` are different records: a node declared dead and one that
/// left are not the same to a consumer, and a departure outranks a death at the
/// same incarnation.
#[test]
fn a_departure_is_not_a_death_and_outranks_one() {
    let b = lone(2);
    b.apply(&[u(3, 0, Liveness::Dead)]).unwrap();
    assert_eq!(b.record(Id(3)), Some(u(3, 0, Liveness::Dead)));
    b.apply(&[u(3, 0, Liveness::Left)]).unwrap();
    assert_eq!(
        b.record(Id(3)),
        Some(u(3, 0, Liveness::Left)),
        "it left, on its own account, after being written off"
    );
}

/// **Rejoining.** A member that left and comes back is a new process at
/// incarnation 0. The cluster holds `Left` at the old incarnation, so it hears
/// that, outranks it with a higher one, and the cluster takes it back.
#[tokio::test]
async fn a_departed_member_can_return_at_a_higher_incarnation() {
    let b = lone(2);
    b.apply(&[u(3, 4, Liveness::Left)]).unwrap();

    // Member 3 restarts, knowing nothing, and calls b. Its own claim, Alive at 0,
    // is below what b holds, so b's reply says what it is believed to be.
    let three = lone(3);
    let reply = b.sync(from(addr(3)), three.view()).await.unwrap();
    assert!(reply.contains(&u(3, 4, Liveness::Left)));
    three.apply(&reply).unwrap();
    assert_eq!(
        three.record(Id(3)),
        Some(u(3, 5, Liveness::Alive)),
        "it refuted with the incarnation above the departure"
    );

    // Its next message carries that, and b takes it back.
    b.sync(from(addr(3)), three.view()).await.unwrap();
    assert_eq!(b.record(Id(3)), Some(u(3, 5, Liveness::Alive)));
}

/// A node told it has left, by someone else, while it is running, is being
/// misreported, and refutes exactly as it would a `Dead` verdict.
#[test]
fn a_running_node_refutes_a_departure_it_did_not_announce() {
    let n = lone(1);
    n.apply(&[u(1, 0, Liveness::Left)]).unwrap();
    assert_eq!(n.record(Id(1)), Some(u(1, 1, Liveness::Alive)));
    assert!(n.log().contains(&Event::Refuted { incarnation: 1 }));
}
