//! A cluster that grows and shrinks: nodes join by calling, and leave by saying so.
//!
//! `tests/swim_membership.rs` is the merge rule and the bound. These are the claims
//! about membership changing:
//!
//! * a join is the first call from a caller, and the reply is the cluster;
//! * a member learns of the others by hearing about them;
//! * a departure is `Left`, which a late failure verdict cannot undo, which is
//!   different from `Dead`, and which only the departed node, coming back at a
//!   higher incarnation, can reverse.
//!
//! `swim::proofs::merge` proves the departure's precedence for the model's
//! `merge`; what is exercised here is the service's glue around it: the write that
//! must not be refuted, and a caller becoming a member.
//!
//! Who a caller is, and who may join, is `tests/swim_endpoint.rs`: the node is
//! handed an `Id` and believes it.

use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{Event, Liveness, MAX_UPDATES, Node, Update};

fn u(node: u128, incarnation: u64, status: Liveness) -> Update {
    Update {
        node: Id(node),
        incarnation,
        status,
    }
}

/// Member `me`, knowing only itself.
fn lone(me: u128) -> Node {
    Node::new(Id(me))
}

/// A new caller is admitted by its first call, and the `sync` reply is how it
/// learns who is there.
#[test]
fn a_join_is_the_first_call_and_the_reply_is_the_cluster() {
    let seed = lone(1);
    assert_eq!(
        seed.view(),
        vec![u(1, 0, Liveness::Alive)],
        "alone at first"
    );

    let reply = seed.sync(Id(2), &[u(2, 0, Liveness::Alive)]).unwrap();
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

/// What a caller says about someone else is gossip about them. It is not a claim
/// to be them: the caller is who it was identified as.
#[test]
fn what_a_caller_says_about_a_third_party_is_not_a_claim_to_be_them() {
    let seed = lone(1);
    // Member 3 says, in its updates, whatever it likes about 5...
    seed.ping(Id(3), &[u(5, 0, Liveness::Dead)]).unwrap();
    // ...which is gossip about 5, not a claim to be 5.
    assert_eq!(seed.record(Id(5)), Some(u(5, 0, Liveness::Dead)));

    // 5 itself, when it calls, is 5, and hears it.
    let reply = seed.ping(Id(5), &[u(5, 0, Liveness::Alive)]).unwrap();
    assert_eq!(
        reply,
        vec![u(1, 0, Liveness::Alive), u(5, 0, Liveness::Dead)],
        "Dead at 0 out-ranks Alive at 0, and is what the cluster holds"
    );
}

/// A request that is refused admits nobody: no new member is left behind.
#[test]
fn a_refused_request_leaves_no_new_member_behind() {
    let seed = lone(1);
    // Member 5 is calling, but its message is over the limit.
    let too_many: Vec<Update> = (0..=MAX_UPDATES)
        .map(|_| u(1, 0, Liveness::Alive))
        .collect();
    let err = seed.ping(Id(5), &too_many).unwrap_err();
    assert_eq!(err.code(), Some("ERR"));
    assert_eq!(seed.record(Id(5)), None, "refused, so not admitted");
    assert_eq!(seed.view(), vec![u(1, 0, Liveness::Alive)]);

    // Admitted by an ordinary call afterwards, as if the refused one never was.
    seed.ping(Id(5), &[]).unwrap();
    assert_eq!(seed.record(Id(5)), Some(u(5, 0, Liveness::Alive)));
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
#[test]
fn a_late_failure_report_does_not_undo_a_departure() {
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
        Id(1),
        &[u(3, 0, Liveness::Dead), u(3, 0, Liveness::Alive)],
    )
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
#[test]
fn a_departed_member_can_return_at_a_higher_incarnation() {
    let b = lone(2);
    b.apply(&[u(3, 4, Liveness::Left)]).unwrap();

    // Member 3 restarts, knowing nothing, and calls b. Its own claim, Alive at 0,
    // is below what b holds, so b's reply says what it is believed to be.
    let three = lone(3);
    let reply = b.sync(Id(3), &three.view()).unwrap();
    assert!(reply.contains(&u(3, 4, Liveness::Left)));
    three.apply(&reply).unwrap();
    assert_eq!(
        three.record(Id(3)),
        Some(u(3, 5, Liveness::Alive)),
        "it refuted with the incarnation above the departure"
    );

    // Its next message carries that, and b takes it back.
    b.sync(Id(3), &three.view()).unwrap();
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
