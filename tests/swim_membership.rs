//! The SWIM service: the merge rule's algebra at the machine, and the one thing
//! a node does that the model leaves to it — answering an accusation about
//! itself.
//!
//! `swim::proofs::merge` proves, for the model's `merge`, that it is idempotent,
//! absorbs a repeat, never regresses, and is commutative and associative; and
//! `swim::proofs::refinement` proves the executable `merge_step` is that
//! function. These tests are those claims *exercised through the service* —
//! delivered in every order, with every duplicate, through the door a peer's
//! message uses — because a service that lost the property in its own glue (a
//! table that was written outside `merge_step`, say) would leave every theorem
//! true and the system wrong.
//!
//! These drive the `Node` directly, with the sender's `Id` as an argument: the node
//! does not look at a connection, so there is none here. The wire is
//! `tests/swim_turmoil.rs`.

use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{Event, Liveness, MAX_UPDATES, Node, Update};

/// Member `me`, in a cluster of members `0`, `1` and `2` that it has heard of,
/// all alive at incarnation zero.
fn node(me: u128) -> Node {
    let n = Node::new(Id(me));
    n.apply(&[
        u(0, 0, Liveness::Alive),
        u(1, 0, Liveness::Alive),
        u(2, 0, Liveness::Alive),
    ])
    .expect("three members are well within the bound");
    n
}

fn u(node: u128, incarnation: u64, status: Liveness) -> Update {
    Update {
        node: Id(node),
        incarnation,
        status,
    }
}

/// There is no roster to start from: a node knows itself, and the rest is learned.
#[test]
fn a_new_node_knows_only_itself() {
    let n = Node::new(Id(7));
    assert_eq!(n.view(), vec![u(7, 0, Liveness::Alive)]);
    assert_eq!(n.record(Id(0)), None, "it has not heard of anyone else");
}

#[test]
fn a_new_node_believes_everyone_alive_at_incarnation_zero() {
    let n = node(0);
    assert_eq!(
        n.view(),
        vec![
            u(0, 0, Liveness::Alive),
            u(1, 0, Liveness::Alive),
            u(2, 0, Liveness::Alive)
        ]
    );
    assert_eq!(n.record(Id(9)), None, "a non-member has no record");
}

/// A failed probe suspects; a timed-out suspicion buries — and neither goes
/// backwards.
#[test]
fn suspicion_then_death_and_neither_is_undone_by_a_weaker_report() {
    let n = node(0);
    assert!(n.suspect(Id(1),0).unwrap());
    assert_eq!(n.record(Id(1)), Some(u(1, 0, Liveness::Suspect)));

    assert!(
        !n.suspect(Id(1),0).unwrap(),
        "suspecting the suspect changes nothing"
    );

    assert!(n.declare_dead(Id(1),0).unwrap());
    assert_eq!(n.record(Id(1)), Some(u(1, 0, Liveness::Dead)));

    // `theorem_merge_never_regresses`: a Suspect at the same incarnation does
    // not out-rank Dead, and is accepted nowhere.
    n.apply(&[u(1, 0, Liveness::Suspect)]).unwrap();
    n.apply(&[u(1, 0, Liveness::Alive)]).unwrap();
    assert_eq!(n.record(Id(1)), Some(u(1, 0, Liveness::Dead)));
}

/// The only thing that undoes a death is the dead node saying so, at a higher
/// incarnation.
#[test]
fn only_a_higher_incarnation_undoes_a_death() {
    let n = node(0);
    n.suspect(Id(1),0).unwrap();
    n.declare_dead(Id(1),0).unwrap();
    n.apply(&[u(1, 1, Liveness::Alive)]).unwrap();
    assert_eq!(n.record(Id(1)), Some(u(1, 1, Liveness::Alive)));
}

/// **Accused, a node answers with an incarnation above the accusation.**
#[test]
fn an_accused_node_refutes_with_a_higher_incarnation() {
    let n = node(0);
    n.apply(&[u(0, 0, Liveness::Suspect)]).unwrap();
    assert_eq!(n.record(Id(0)), Some(u(0, 1, Liveness::Alive)));
    assert_eq!(
        n.log(),
        vec![
            Event::Learned {
                about: Id(0),
                incarnation: 0,
                status: Liveness::Suspect
            },
            Event::Refuted { incarnation: 1 },
        ]
    );

    // The accusation, replayed, no longer reaches anything: it is below what
    // the node now holds.
    n.apply(&[u(0, 0, Liveness::Suspect)]).unwrap();
    n.apply(&[u(0, 0, Liveness::Dead)]).unwrap();
    assert_eq!(n.record(Id(0)), Some(u(0, 1, Liveness::Alive)));
    assert_eq!(n.log().len(), 2, "a replay is not a second refutation");

    // A fresh accusation at the new incarnation is answered with the next.
    n.apply(&[u(0, 1, Liveness::Dead)]).unwrap();
    assert_eq!(n.record(Id(0)), Some(u(0, 2, Liveness::Alive)));
}

/// Being told you are fine is not an accusation.
#[test]
fn hearing_ones_own_current_record_is_not_a_reason_to_refute() {
    let n = node(0);
    n.apply(&[u(0, 0, Liveness::Alive)]).unwrap();
    assert!(n.log().is_empty());
}

/// A node does not accuse itself, and nobody can make it.
#[test]
fn a_node_does_not_suspect_itself() {
    let n = node(0);
    assert_eq!(n.suspect(Id(0),0).unwrap_err().code(), Some("NO"));
    assert_eq!(n.declare_dead(Id(0),0).unwrap_err().code(), Some("NO"));
    assert_eq!(n.suspect(Id(9),0).unwrap_err().code(), Some("ERR"));
}

/// The incarnation space is `u64`, and an accusation at the top of it has no
/// refutation that fits. Wrapping would take the node's record backwards, so
/// the node refuses, and the accusation stays on its record.
#[test]
fn the_incarnation_space_does_not_wrap() {
    let n = node(0);
    let err = n.apply(&[u(0, u64::MAX, Liveness::Dead)]).unwrap_err();
    assert_eq!(err.code(), Some("NO"));
    assert_eq!(n.record(Id(0)), Some(u(0, u64::MAX, Liveness::Dead)));
}

/// **A restart costs a round trip, not correctness.**
///
/// The node keeps nothing on disk. Restarted, it is at incarnation 0 and its
/// peers remember it dead at 3; the first message that says so out-ranks it,
/// and it answers with 4.
#[test]
fn a_restarted_node_is_told_what_it_was_and_outranks_it() {
    let before = node(0);
    for inc in 0..=3 {
        before.apply(&[u(0, inc, Liveness::Dead)]).unwrap();
    }

    let peer = node(1);
    peer.apply(&[u(0, 3, Liveness::Dead)]).unwrap();

    let after = node(0);
    assert_eq!(after.record(Id(0)), Some(u(0, 0, Liveness::Alive)), "it forgot");

    let told = peer.view();
    after.apply(&told).unwrap();
    assert_eq!(after.record(Id(0)), Some(u(0, 4, Liveness::Alive)));
}

/// **Every order and every duplicate, one answer.**
///
/// The executable form of S2, S4 and S6 together: a node's table is the fold of
/// `merge` over what it was told, so the fold must not care how the messages
/// were ordered or how often they were repeated.
#[test]
fn delivery_order_and_duplication_do_not_change_the_table() {
    let msgs = [
        u(1, 0, Liveness::Suspect),
        u(1, 0, Liveness::Dead),
        u(1, 1, Liveness::Alive),
        u(2, 2, Liveness::Suspect),
        u(2, 0, Liveness::Dead),
    ];

    let reference = node(0);
    reference.apply(&msgs).unwrap();
    let want = reference.view();
    assert_eq!(want[1], u(1, 1, Liveness::Alive));
    assert_eq!(want[2], u(2, 2, Liveness::Suspect));

    // All 120 orders.
    let mut idx: Vec<usize> = (0..msgs.len()).collect();
    let mut seen = 0;
    permute(&mut idx, 0, &mut |order| {
        let n = node(0);
        for &i in order {
            n.apply(&[msgs[i]]).unwrap();
        }
        assert_eq!(n.view(), want, "order {order:?}");

        // And again, with every message delivered a second time, interleaved.
        for &i in order.iter().rev() {
            n.apply(&[msgs[i]]).unwrap();
        }
        assert_eq!(n.view(), want, "order {order:?}, replayed");
        seen += 1;
    });
    assert_eq!(seen, 120);

    // And all at once, in a single message, however it is cut.
    let n = node(0);
    n.apply(&msgs[3..]).unwrap();
    n.apply(&msgs[..3]).unwrap();
    assert_eq!(n.view(), want);
}

fn permute(a: &mut Vec<usize>, k: usize, f: &mut impl FnMut(&[usize])) {
    if k == a.len() {
        f(a);
        return;
    }
    for i in k..a.len() {
        a.swap(k, i);
        permute(a, k + 1, f);
        a.swap(k, i);
    }
}

/// **A message that would take the node past its bound is refused whole.**
#[test]
fn a_batch_is_applied_entirely_or_not_at_all() {
    let n = node(0);
    // A report about a member it knows, and enough new members to overflow.
    let mut batch = vec![u(1, 0, Liveness::Dead)];
    batch.extend((100..100 + (MAX_UPDATES as u128 - 2)).map(|i| u(i, 0, Liveness::Alive)));
    assert!(batch.len() <= MAX_UPDATES, "the message itself is not too big");
    let err = n.apply(&batch).unwrap_err();
    assert_eq!(err.code(), Some("ERR"));
    assert_eq!(
        n.record(Id(1)),
        Some(u(1, 0, Liveness::Alive)),
        "the half that would have fitted was not applied"
    );
    assert_eq!(n.view().len(), 3, "and nobody was admitted");
}

#[test]
fn an_oversized_message_is_refused() {
    let n = node(0);
    let big = vec![u(1, 0, Liveness::Suspect); MAX_UPDATES + 1];
    assert_eq!(n.apply(&big).unwrap_err().code(), Some("ERR"));
    assert_eq!(
        n.apply(&big[..MAX_UPDATES])
            .map_err(|e| e.code().map(String::from)),
        Ok(())
    );
}

/// Calling is how a node joins: the caller is a member from then on, however the
/// receiver heard of it.
#[test]
fn a_caller_is_a_member_from_its_first_call() {
    let n = node(0);
    assert_eq!(n.record(Id(5)), None);
    n.ping(Id(5), &[]).unwrap();
    assert_eq!(n.record(Id(5)), Some(u(5, 0, Liveness::Alive)));

    n.sync(Id(6), &[]).unwrap();
    assert_eq!(n.record(Id(6)), Some(u(6, 0, Liveness::Alive)));
}

/// The service takes the sender from the message and reads nothing else: the
/// `Context` is empty here, and the caller is still a member.
#[tokio::test]
async fn the_service_takes_the_sender_from_the_message() {
    use jetstream::prelude::Context;
    use jetstream_distributed::swim::service::Membership;

    let n = node(0);
    let ack = Membership::ping(&n, Context::default(), Id(5), vec![u(5, 0, Liveness::Alive)])
        .await
        .unwrap();
    assert_eq!(
        ack,
        vec![u(0, 0, Liveness::Alive), u(5, 0, Liveness::Alive)]
    );
    assert_eq!(n.record(Id(5)), Some(u(5, 0, Liveness::Alive)));

    let all = Membership::sync(&n, Context::default(), Id(6), vec![])
        .await
        .unwrap();
    assert_eq!(all, n.view());
    assert!(all.contains(&u(6, 0, Liveness::Alive)), "and 6 joined by it");
}

/// A request refused for being over the bound admits nobody, its caller included.
#[test]
fn a_request_refused_over_the_bound_admits_no_one() {
    let n = node(0);
    let batch: Vec<Update> = (100..100 + (MAX_UPDATES as u128 - 2))
        .map(|i| u(i, 0, Liveness::Alive))
        .collect();
    assert_eq!(n.ping(Id(5), &batch).unwrap_err().code(), Some("ERR"));
    assert_eq!(n.record(Id(5)), None, "the caller was not admitted");
    assert_eq!(n.view().len(), 3);
}

/// The bound is on members, and it is exactly `MAX_UPDATES`: a `sync` reply is the
/// whole table, and the node that asked feeds it through `apply`, which would
/// refuse more.
#[test]
fn a_node_holds_exactly_as_many_members_as_one_message_can_carry() {
    let n = Node::new(Id(0));
    let rest: Vec<Update> = (1..MAX_UPDATES as u128)
        .map(|i| u(i, 0, Liveness::Alive))
        .collect();
    n.apply(&rest).unwrap();
    assert_eq!(n.view().len(), MAX_UPDATES);

    assert_eq!(
        n.apply(&[u(MAX_UPDATES as u128, 0, Liveness::Alive)])
            .unwrap_err()
            .code(),
        Some("ERR"),
        "one more is too many"
    );
    // The whole table fits in one message, which is the point of the bound.
    let table = n.sync(Id(1), &[]).unwrap();
    assert_eq!(table.len(), MAX_UPDATES);
    Node::new(Id(1)).apply(&table).unwrap();
}

/// `ping` answers about the members the message mentioned, and about the
/// receiver; `sync` answers about everyone.
#[test]
fn ping_answers_with_what_it_was_asked_about_and_sync_with_everything() {
    let b = node(1);
    b.suspect(Id(2),0).unwrap();
    b.declare_dead(Id(2),0).unwrap();

    let ack = b.ping(Id(0), &[u(2, 0, Liveness::Suspect)]).unwrap();
    assert_eq!(
        ack,
        vec![u(1, 0, Liveness::Alive), u(2, 0, Liveness::Dead)],
        "the sender learns the receiver knew something stronger"
    );

    let ack = b.ping(Id(0), &[]).unwrap();
    assert_eq!(
        ack,
        vec![u(1, 0, Liveness::Alive)],
        "nothing mentioned: only itself"
    );

    let all = b.sync(Id(0), &[]).unwrap();
    assert_eq!(all, b.view());
    assert_eq!(all.len(), 3);
}

/// **Three nodes that disagree converge by exchanging tables.**
#[test]
fn nodes_that_drifted_apart_converge_by_syncing() {
    let (a, b, c) = (node(0), node(1), node(2));
    a.suspect(Id(2),0).unwrap();
    b.suspect(Id(0),0).unwrap();
    b.declare_dead(Id(0),0).unwrap();
    c.apply(&[u(1, 5, Liveness::Alive)]).unwrap();

    // A round of pushes in a ring, twice, so everything has gone all the way
    // round.
    for _ in 0..2 {
        for (src, dst) in [(&a, &b), (&b, &c), (&c, &a)] {
            let theirs = dst.sync(src.id(), &src.view()).unwrap();
            src.apply(&theirs).unwrap();
        }
    }

    assert_eq!(a.view(), b.view());
    assert_eq!(b.view(), c.view());
    // Node 0 was declared dead by node 1 and has, being alive, refuted it.
    assert_eq!(a.record(Id(0)), Some(u(0, 1, Liveness::Alive)));
    assert_eq!(c.record(Id(0)), Some(u(0, 1, Liveness::Alive)));
    // Node 1 was told it was alive at 5 -- a record about itself that out-ranks
    // its own, which is the same situation as a restart -- and went one higher.
    assert_eq!(c.record(Id(1)), Some(u(1, 6, Liveness::Alive)));
}

/// **A suspicion timer that outlives its suspicion does nothing.**
///
/// A suspicion at incarnation 0 starts a timer. Before it fires the suspected
/// node refutes, and this node learns `Alive` at 1. The timer then fires for
/// incarnation 0: it must not kill incarnation 1, which nobody suspected.
#[test]
fn a_stale_suspicion_timer_cannot_kill_a_refuted_node() {
    let n = node(0);
    assert!(n.suspect(Id(1),0).unwrap());

    // The refutation lands while the timer is running.
    n.apply(&[u(1, 1, Liveness::Alive)]).unwrap();

    assert!(
        !n.declare_dead(Id(1),0).unwrap(),
        "the timer was for incarnation 0"
    );
    assert_eq!(n.record(Id(1)), Some(u(1, 1, Liveness::Alive)));
}

/// The same race on the way in: a probe that began at incarnation 0 and failed
/// after the refutation arrived suspects nothing, because the suspicion it
/// carries is already out-ranked.
#[test]
fn a_stale_probe_cannot_suspect_a_refuted_node() {
    let n = node(0);
    n.apply(&[u(1, 1, Liveness::Alive)]).unwrap();
    assert!(!n.suspect(Id(1),0).unwrap());
    assert_eq!(n.record(Id(1)), Some(u(1, 1, Liveness::Alive)));
}

/// Death needs a suspicion first: a timer cannot declare dead a node this node
/// never suspected at that incarnation.
#[test]
fn death_needs_a_suspicion_at_that_incarnation() {
    let n = node(0);
    assert!(!n.declare_dead(Id(1),0).unwrap(), "never suspected");
    n.suspect(Id(1),0).unwrap();
    assert!(!n.declare_dead(Id(1),7).unwrap(), "suspected at 0, not 7");
    assert!(n.declare_dead(Id(1),0).unwrap());
    assert_eq!(n.record(Id(1)), Some(u(1, 0, Liveness::Dead)));
}
