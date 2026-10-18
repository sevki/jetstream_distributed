//! The actor service: its guarantees, exercised through the service.
//!
//! `actor::proofs` proves, for the model, that one host at a time appends, that
//! each message is accepted once and in order, and that a handover keeps the
//! state; `actor::proofs::refinement` proves the executable steps are the model's.
//! These are those claims *exercised through the service* — and the refusals
//! especially, because a service that delegated everything and enforced nothing
//! would pass every test of the happy path.
//!
//! They drive the `Host` directly. Identity still arrives the way the service
//! insists on: a `Context` carrying the caller's address, never an argument
//! naming the acting node.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use distributed_ownership::actor::service::{Actor, Event, Host, Receipt, Record, Snapshot};
use distributed_ownership::ownership::service::{MemoryFloor, Offer};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

const ADDR_A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const ADDR_B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const ADDR_C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));
const ADDR_D: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 4));
const STRANGER: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 9, 9, 9));

/// `A` and `B` can host the actor; `C` and `D` only send to it.
const A: u64 = 1;
const B: u64 = 2;
const C: u64 = 3;
const D: u64 = 4;

fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([(ADDR_A, A), (ADDR_B, B), (ADDR_C, C), (ADDR_D, D)])
}

fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

fn code(e: Error) -> Option<String> {
    e.code().map(String::from)
}

/// The actor is offered to `A` at epoch 1.
fn actor() -> Host {
    Host::new(roster(), A, Arc::new(MemoryFloor::new())).expect("A is on the roster")
}

/// `A` takes the actor.
async fn a_hosts(h: &Host) {
    assert_eq!(h.poll(from(ADDR_A)).await.unwrap(), Offer::Grant(1));
    h.acquire(from(ADDR_A), 1).await.unwrap();
}

/// The behaviour, written out here independently of the service.
fn apply(state: u64, body: u64) -> u64 {
    (((state as u128) * 31 + body as u128) % (1u128 << 64)) as u64
}

fn fold(records: &[Record]) -> u64 {
    records.iter().fold(0, |s, r| apply(s, r.body))
}

#[tokio::test]
async fn a_host_accepts_messages_in_the_order_sent_and_the_state_is_their_fold() {
    let h = actor();
    a_hosts(&h).await;
    assert_eq!(h.send(from(ADDR_C), 7).await.unwrap(), 0);
    assert_eq!(h.send(from(ADDR_C), 9).await.unwrap(), 1);

    let r0 = h.accept(from(ADDR_A), 1, C, 0).await.unwrap();
    assert_eq!(
        r0,
        Receipt {
            index: 0,
            body: 7,
            state: 7
        }
    );
    let r1 = h.accept(from(ADDR_A), 1, C, 1).await.unwrap();
    assert_eq!(
        r1,
        Receipt {
            index: 1,
            body: 9,
            state: 7 * 31 + 9
        }
    );

    assert_eq!(
        h.state(from(ADDR_B)).await.unwrap(),
        Snapshot { len: 2, state: 226 }
    );
    assert_eq!(h.snapshot().state, fold(&h.records()));
}

/// **A redelivered message is accepted once.**
#[tokio::test]
async fn a_redelivered_message_is_refused() {
    let h = actor();
    a_hosts(&h).await;
    h.send(from(ADDR_C), 7).await.unwrap();
    h.accept(from(ADDR_A), 1, C, 0).await.unwrap();
    let before = h.snapshot();

    for _ in 0..3 {
        assert_eq!(
            code(h.accept(from(ADDR_A), 1, C, 0).await.unwrap_err()),
            Some("NO".into())
        );
    }
    assert_eq!(h.snapshot(), before, "and nothing moved");
    assert_eq!(h.records().len(), 1);
}

/// **A message ahead of its turn waits for the ones before it.**
#[tokio::test]
async fn a_message_ahead_of_its_turn_is_refused_until_its_turn() {
    let h = actor();
    a_hosts(&h).await;
    h.send(from(ADDR_C), 1).await.unwrap();
    h.send(from(ADDR_C), 2).await.unwrap();

    assert_eq!(
        code(h.accept(from(ADDR_A), 1, C, 1).await.unwrap_err()),
        Some("NO".into())
    );
    h.accept(from(ADDR_A), 1, C, 0).await.unwrap();
    h.accept(from(ADDR_A), 1, C, 1).await.unwrap();
    assert_eq!(
        h.records().iter().map(|r| r.seq).collect::<Vec<_>>(),
        vec![0, 1]
    );
}

/// Senders are counted separately: one sender's backlog does not hold up
/// another's messages.
#[tokio::test]
async fn senders_are_ordered_independently() {
    let h = actor();
    a_hosts(&h).await;
    h.send(from(ADDR_C), 10).await.unwrap();
    h.send(from(ADDR_D), 20).await.unwrap();
    h.accept(from(ADDR_A), 1, D, 0).await.unwrap();
    h.accept(from(ADDR_A), 1, C, 0).await.unwrap();
    assert_eq!(
        h.records()
            .iter()
            .map(|r| (r.sender, r.seq))
            .collect::<Vec<_>>(),
        vec![(D, 0), (C, 0)]
    );
}

#[tokio::test]
async fn a_message_nobody_sent_is_refused() {
    let h = actor();
    a_hosts(&h).await;
    assert_eq!(
        code(h.accept(from(ADDR_A), 1, C, 0).await.unwrap_err()),
        Some("ERR".into())
    );
    h.send(from(ADDR_C), 1).await.unwrap();
    assert_eq!(
        code(h.accept(from(ADDR_A), 1, D, 0).await.unwrap_err()),
        Some("ERR".into())
    );
    assert!(h.records().is_empty());
}

/// **Only the owner, at the current epoch, appends.**
#[tokio::test]
async fn only_the_owner_at_its_epoch_may_append() {
    let h = actor();
    a_hosts(&h).await;
    h.send(from(ADDR_C), 5).await.unwrap();

    // `B` does not own the actor.
    assert_eq!(
        code(h.accept(from(ADDR_B), 1, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
    // `A` owns it, but not at epoch 2.
    assert_eq!(
        code(h.accept(from(ADDR_A), 2, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert_eq!(
        code(h.accept(from(ADDR_A), 0, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert!(h.records().is_empty());

    h.accept(from(ADDR_A), 1, C, 0).await.unwrap();
}

/// A fenced host learns nothing about the journal: the fence is asked before
/// whether the message exists or whose turn it is.
#[tokio::test]
async fn the_fence_is_asked_first() {
    let h = actor();
    a_hosts(&h).await;
    // Nothing was sent, and `B` is not the owner: the answer is the fence's.
    assert_eq!(
        code(h.accept(from(ADDR_B), 1, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
}

/// **A handover moves the actor and its state — and fences the old host.**
#[tokio::test]
async fn a_handover_keeps_the_journal_and_fences_the_old_host() {
    let h = actor();
    a_hosts(&h).await;
    h.send(from(ADDR_C), 7).await.unwrap();
    h.send(from(ADDR_C), 9).await.unwrap();
    h.send(from(ADDR_C), 11).await.unwrap();
    h.accept(from(ADDR_A), 1, C, 0).await.unwrap();
    h.accept(from(ADDR_A), 1, C, 1).await.unwrap();
    let before = h.snapshot();

    // `A` agrees to hand the actor to `B`. Its epoch is burned from this moment.
    h.begin_transfer(from(ADDR_A), B).await.unwrap();
    assert_eq!(
        code(h.accept(from(ADDR_A), 1, C, 2).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert_eq!(
        code(h.accept(from(ADDR_A), 2, C, 2).await.unwrap_err()),
        Some("FENCED".into())
    );

    // `A` acknowledges and `B` takes the actor at epoch 2.
    assert_eq!(h.poll(from(ADDR_A)).await.unwrap(), Offer::Revoke(2));
    h.release(from(ADDR_A), 2).await.unwrap();
    assert_eq!(h.poll(from(ADDR_B)).await.unwrap(), Offer::Grant(2));
    h.acquire(from(ADDR_B), 2).await.unwrap();

    // `B` did not receive the state; it reads the same journal and gets the same
    // state.
    assert_eq!(h.state(from(ADDR_B)).await.unwrap(), before);
    let caught_up = h.journal(from(ADDR_B), 0, 100).await.unwrap();
    assert_eq!(caught_up.len(), 2);
    assert_eq!(fold(&caught_up), before.state);

    // `B` continues where `A` stopped.
    let r = h.accept(from(ADDR_B), 2, C, 2).await.unwrap();
    assert_eq!(r.index, 2);
    assert_eq!(r.state, apply(before.state, 11));

    // `A`, still believing, is refused — and so is a redelivery to `B`.
    assert_eq!(
        code(h.accept(from(ADDR_A), 1, C, 2).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert_eq!(
        code(h.accept(from(ADDR_B), 2, C, 0).await.unwrap_err()),
        Some("NO".into())
    );

    // Two hosts, two epochs, one journal, in order.
    let recs = h.records();
    assert_eq!(
        recs.iter().map(|r| (r.host, r.epoch)).collect::<Vec<_>>(),
        vec![(A, 1), (A, 1), (B, 2)]
    );
    assert_eq!(
        recs.iter().map(|r| r.seq).collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
}

/// **A forced revocation fences the host too**, and the journal is what the next
/// host recovers from — the old host's memory is never consulted.
#[tokio::test]
async fn a_forced_revocation_leaves_the_journal_for_the_next_host() {
    let h = actor();
    a_hosts(&h).await;
    h.send(from(ADDR_C), 3).await.unwrap();
    h.send(from(ADDR_C), 4).await.unwrap();
    h.accept(from(ADDR_A), 1, C, 0).await.unwrap();

    // `A` is unreachable. The coordinator burns its epoch and offers the actor to
    // `B`.
    assert_eq!(h.force(B).await.unwrap(), B);
    assert_eq!(
        code(h.accept(from(ADDR_A), 1, C, 1).await.unwrap_err()),
        Some("FENCED".into())
    );

    assert_eq!(h.poll(from(ADDR_B)).await.unwrap(), Offer::Grant(2));
    h.acquire(from(ADDR_B), 2).await.unwrap();
    assert_eq!(h.state(from(ADDR_B)).await.unwrap().len, 1);
    h.accept(from(ADDR_B), 2, C, 1).await.unwrap();
    assert_eq!(h.snapshot().state, fold(&h.records()));
}

/// **Every order of arrival, with every retry, gives a well-formed journal.**
///
/// Four messages from two senders, delivered in each of the 24 orders, each
/// attempted twice. Which interleaving the journal records depends on the order;
/// what must not depend on it is that each sender's messages appear once and in
/// sequence, and that the state is the fold of whatever the journal holds.
#[tokio::test]
async fn delivery_order_and_redelivery_cannot_corrupt_the_journal() {
    let msgs: [(u64, u64, IpAddr); 4] = [
        (C, 0, ADDR_C),
        (C, 1, ADDR_C),
        (D, 0, ADDR_D),
        (D, 1, ADDR_D),
    ];
    let mut orders = Vec::new();
    permute(&mut vec![0usize, 1, 2, 3], 0, &mut |o| {
        orders.push(o.to_vec())
    });
    assert_eq!(orders.len(), 24);

    for order in orders {
        let h = actor();
        a_hosts(&h).await;
        for (i, (_, _, addr)) in msgs.iter().enumerate() {
            h.send(from(*addr), 100 + i as u64).await.unwrap();
        }
        // Two passes: a message that arrives ahead of its turn is picked up the
        // second time round.
        for _ in 0..2 {
            for &i in &order {
                let (sender, seq, _) = msgs[i];
                let _ = h.accept(from(ADDR_A), 1, sender, seq).await;
            }
        }

        let recs = h.records();
        assert_eq!(recs.len(), 4, "order {order:?}: all four, once each");
        for sender in [C, D] {
            let seqs: Vec<u64> = recs
                .iter()
                .filter(|r| r.sender == sender)
                .map(|r| r.seq)
                .collect();
            assert_eq!(
                seqs,
                vec![0, 1],
                "order {order:?}: {sender}'s messages in sequence"
            );
        }
        assert_eq!(h.snapshot().state, fold(&recs), "order {order:?}");
    }
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

#[tokio::test]
async fn the_journal_is_read_in_pages() {
    let h = actor();
    a_hosts(&h).await;
    for i in 0..5 {
        h.send(from(ADDR_C), i).await.unwrap();
        h.accept(from(ADDR_A), 1, C, i).await.unwrap();
    }
    let page = h.journal(from(ADDR_B), 1, 2).await.unwrap();
    assert_eq!(page.iter().map(|r| r.seq).collect::<Vec<_>>(), vec![1, 2]);
    assert!(h.journal(from(ADDR_B), 9, 2).await.unwrap().is_empty());
    assert_eq!(
        code(h.journal(from(ADDR_B), 0, 100_000).await.unwrap_err()),
        Some("ERR".into())
    );
}

#[tokio::test]
async fn a_stranger_is_refused_by_every_door() {
    let h = actor();
    assert_eq!(
        code(h.poll(from(STRANGER)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.send(from(STRANGER), 1).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.accept(from(STRANGER), 1, C, 0).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.state(from(STRANGER)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.journal(from(STRANGER), 0, 1).await.unwrap_err()),
        Some("NO".into())
    );
    assert!(h.log().is_empty());
}

#[tokio::test]
async fn what_the_host_did_is_logged_in_order() {
    let h = actor();
    a_hosts(&h).await;
    h.send(from(ADDR_C), 1).await.unwrap();
    h.accept(from(ADDR_A), 1, C, 0).await.unwrap();
    assert_eq!(
        h.log(),
        vec![
            Event::Sent { sender: C, seq: 0 },
            Event::Accepted {
                host: A,
                epoch: 1,
                sender: C,
                seq: 0,
                index: 0
            },
        ]
    );
}
