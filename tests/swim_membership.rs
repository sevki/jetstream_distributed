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
//! These drive the `Node` directly. Identity still arrives the way the service
//! insists on, a `Context` carrying the caller's address and never an argument
//! naming a sender; the wire is `tests/swim_turmoil.rs`.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};

use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;
use jetstream_distributed::host::HostId;
use jetstream_distributed::swim::service::{
    Event, Liveness, MAX_UPDATES, Membership, Node, Update,
};

const A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));
const STRANGER: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 9, 9, 9));

fn roster() -> HashMap<IpAddr, HostId> {
    HashMap::from([(A, 0u128), (B, 1u128), (C, 2u128)])
}

fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

fn node(me: u128) -> Node {
    Node::new(roster(), me).expect("on the roster")
}

fn u(node: HostId, incarnation: u64, status: Liveness) -> Update {
    Update {
        node,
        incarnation,
        status,
    }
}

#[test]
fn a_node_off_the_roster_cannot_be_built() {
    assert!(Node::new(roster(), 7).is_err());
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
    assert_eq!(n.record(9), None, "a non-member has no record");
}

/// A failed probe suspects; a timed-out suspicion buries — and neither goes
/// backwards.
#[test]
fn suspicion_then_death_and_neither_is_undone_by_a_weaker_report() {
    let n = node(0);
    assert!(n.suspect(1, 0).unwrap());
    assert_eq!(n.record(1), Some(u(1, 0, Liveness::Suspect)));

    assert!(
        !n.suspect(1, 0).unwrap(),
        "suspecting the suspect changes nothing"
    );

    assert!(n.declare_dead(1, 0).unwrap());
    assert_eq!(n.record(1), Some(u(1, 0, Liveness::Dead)));

    // `theorem_merge_never_regresses`: a Suspect at the same incarnation does
    // not out-rank Dead, and is accepted nowhere.
    n.apply(&[u(1, 0, Liveness::Suspect)]).unwrap();
    n.apply(&[u(1, 0, Liveness::Alive)]).unwrap();
    assert_eq!(n.record(1), Some(u(1, 0, Liveness::Dead)));
}

/// The only thing that undoes a death is the dead node saying so, at a higher
/// incarnation.
#[test]
fn only_a_higher_incarnation_undoes_a_death() {
    let n = node(0);
    n.suspect(1, 0).unwrap();
    n.declare_dead(1, 0).unwrap();
    n.apply(&[u(1, 1, Liveness::Alive)]).unwrap();
    assert_eq!(n.record(1), Some(u(1, 1, Liveness::Alive)));
}

/// **Accused, a node answers with an incarnation above the accusation.**
#[test]
fn an_accused_node_refutes_with_a_higher_incarnation() {
    let n = node(0);
    n.apply(&[u(0, 0, Liveness::Suspect)]).unwrap();
    assert_eq!(n.record(0), Some(u(0, 1, Liveness::Alive)));
    assert_eq!(
        n.log(),
        vec![
            Event::Learned {
                about: 0,
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
    assert_eq!(n.record(0), Some(u(0, 1, Liveness::Alive)));
    assert_eq!(n.log().len(), 2, "a replay is not a second refutation");

    // A fresh accusation at the new incarnation is answered with the next.
    n.apply(&[u(0, 1, Liveness::Dead)]).unwrap();
    assert_eq!(n.record(0), Some(u(0, 2, Liveness::Alive)));
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
    assert_eq!(n.suspect(0, 0).unwrap_err().code(), Some("NO"));
    assert_eq!(n.declare_dead(0, 0).unwrap_err().code(), Some("NO"));
    assert_eq!(n.suspect(9, 0).unwrap_err().code(), Some("ERR"));
}

/// The incarnation space is `u64`, and an accusation at the top of it has no
/// refutation that fits. Wrapping would take the node's record backwards, so
/// the node refuses, and the accusation stays on its record.
#[test]
fn the_incarnation_space_does_not_wrap() {
    let n = node(0);
    let err = n.apply(&[u(0, u64::MAX, Liveness::Dead)]).unwrap_err();
    assert_eq!(err.code(), Some("NO"));
    assert_eq!(n.record(0), Some(u(0, u64::MAX, Liveness::Dead)));
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
    assert_eq!(after.record(0), Some(u(0, 0, Liveness::Alive)), "it forgot");

    let told = peer.view();
    after.apply(&told).unwrap();
    assert_eq!(after.record(0), Some(u(0, 4, Liveness::Alive)));
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

/// **A message naming a non-member is refused whole.**
#[test]
fn a_batch_is_applied_entirely_or_not_at_all() {
    let n = node(0);
    let err = n
        .apply(&[u(1, 0, Liveness::Dead), u(9, 0, Liveness::Dead)])
        .unwrap_err();
    assert_eq!(err.code(), Some("ERR"));
    assert_eq!(
        n.record(1),
        Some(u(1, 0, Liveness::Alive)),
        "the valid half was not applied"
    );
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

#[tokio::test]
async fn a_stranger_is_refused_before_anything_is_read() {
    let n = node(0);
    for r in [
        n.ping(from(STRANGER), vec![u(1, 0, Liveness::Dead)]).await,
        n.sync(from(STRANGER), vec![u(1, 0, Liveness::Dead)]).await,
        n.ping(Context::default(), vec![]).await,
    ] {
        assert_eq!(r.unwrap_err().code(), Some("NO"));
    }
    assert_eq!(
        n.record(1),
        Some(u(1, 0, Liveness::Alive)),
        "and nothing was applied"
    );
}

/// `ping` answers about the members the message mentioned, and about the
/// receiver; `sync` answers about everyone.
#[tokio::test]
async fn ping_answers_with_what_it_was_asked_about_and_sync_with_everything() {
    let b = node(1);
    b.suspect(2, 0).unwrap();
    b.declare_dead(2, 0).unwrap();

    let ack = b
        .ping(from(A), vec![u(2, 0, Liveness::Suspect)])
        .await
        .unwrap();
    assert_eq!(
        ack,
        vec![u(1, 0, Liveness::Alive), u(2, 0, Liveness::Dead)],
        "the sender learns the receiver knew something stronger"
    );

    let ack = b.ping(from(A), vec![]).await.unwrap();
    assert_eq!(
        ack,
        vec![u(1, 0, Liveness::Alive)],
        "nothing mentioned: only itself"
    );

    let all = b.sync(from(A), vec![]).await.unwrap();
    assert_eq!(all, b.view());
    assert_eq!(all.len(), 3);
}

/// **Three nodes that disagree converge by exchanging tables.**
#[tokio::test]
async fn nodes_that_drifted_apart_converge_by_syncing() {
    let (a, b, c) = (node(0), node(1), node(2));
    a.suspect(2, 0).unwrap();
    b.suspect(0, 0).unwrap();
    b.declare_dead(0, 0).unwrap();
    c.apply(&[u(1, 5, Liveness::Alive)]).unwrap();

    // A round of pushes in a ring, twice, so everything has gone all the way
    // round.
    for _ in 0..2 {
        for (from_addr, src, dst) in [(A, &a, &b), (B, &b, &c), (C, &c, &a)] {
            let theirs = dst.sync(from(from_addr), src.view()).await.unwrap();
            src.apply(&theirs).unwrap();
        }
    }

    assert_eq!(a.view(), b.view());
    assert_eq!(b.view(), c.view());
    // Node 0 was declared dead by node 1 and has, being alive, refuted it.
    assert_eq!(a.record(0), Some(u(0, 1, Liveness::Alive)));
    assert_eq!(c.record(0), Some(u(0, 1, Liveness::Alive)));
    // Node 1 was told it was alive at 5 -- a record about itself that out-ranks
    // its own, which is the same situation as a restart -- and went one higher.
    assert_eq!(c.record(1), Some(u(1, 6, Liveness::Alive)));
}

/// **A suspicion timer that outlives its suspicion does nothing.**
///
/// A suspicion at incarnation 0 starts a timer. Before it fires the suspected
/// node refutes, and this node learns `Alive` at 1. The timer then fires for
/// incarnation 0: it must not kill incarnation 1, which nobody suspected.
#[test]
fn a_stale_suspicion_timer_cannot_kill_a_refuted_node() {
    let n = node(0);
    assert!(n.suspect(1, 0).unwrap());

    // The refutation lands while the timer is running.
    n.apply(&[u(1, 1, Liveness::Alive)]).unwrap();

    assert!(
        !n.declare_dead(1, 0).unwrap(),
        "the timer was for incarnation 0"
    );
    assert_eq!(n.record(1), Some(u(1, 1, Liveness::Alive)));
}

/// The same race on the way in: a probe that began at incarnation 0 and failed
/// after the refutation arrived suspects nothing, because the suspicion it
/// carries is already out-ranked.
#[test]
fn a_stale_probe_cannot_suspect_a_refuted_node() {
    let n = node(0);
    n.apply(&[u(1, 1, Liveness::Alive)]).unwrap();
    assert!(!n.suspect(1, 0).unwrap());
    assert_eq!(n.record(1), Some(u(1, 1, Liveness::Alive)));
}

/// Death needs a suspicion first: a timer cannot declare dead a node this node
/// never suspected at that incarnation.
#[test]
fn death_needs_a_suspicion_at_that_incarnation() {
    let n = node(0);
    assert!(!n.declare_dead(1, 0).unwrap(), "never suspected");
    n.suspect(1, 0).unwrap();
    assert!(!n.declare_dead(1, 7).unwrap(), "suspected at 0, not 7");
    assert!(n.declare_dead(1, 0).unwrap());
    assert_eq!(n.record(1), Some(u(1, 0, Liveness::Dead)));
}

/// A roster too big for one message could never complete its own push/pull: the
/// whole-table reply would exceed what `apply` accepts.
#[test]
fn a_roster_too_big_for_one_message_is_refused() {
    let big = |n: usize| -> HashMap<IpAddr, HostId> {
        (0..n as u128)
            .map(|i| (IpAddr::V4(Ipv4Addr::from(0x0a00_0000 + i as u32)), i))
            .collect()
    };
    assert!(Node::new(big(MAX_UPDATES), 0).is_ok());
    assert!(Node::new(big(MAX_UPDATES + 1), 0).is_err());
}
