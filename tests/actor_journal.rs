//! The actor service: its guarantees, exercised through the service.
//!
//! `actor::proofs` proves, for the model, that one host at a time appends, that
//! each message is accepted once and in order, and that a handover keeps the
//! state; `actor::proofs::refinement` proves the executable steps are the model's.
//! These are those claims *exercised through the service* — and the refusals
//! especially, because a service that delegated everything and enforced nothing
//! would pass every test of the happy path.
//!
//! Every call goes through Jetstream: a generated client channel, a session over
//! a byte stream, and the generated server in front of the `Host`
//! (`Host::connect`). Identity arrives the way the service insists on — from the
//! connection a call came in on, never from an argument naming the acting node —
//! so a test is a node only by holding that node's connection. The `Host` is
//! touched directly for two things only: the coordinator's `force`, which no node
//! may cause, and its audit log.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use jetstream_distributed::id::Id;
use jetstream_distributed::actor::service::{
    Actor, Connection, Event, Host, Receipt, Record, Snapshot,
};
use jetstream_distributed::ownership::service::{MemoryFloor, Offer};
use jetstream::prelude::*;
use jetstream_rpc::context::RemoteAddr;

const ADDR_A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const ADDR_B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const ADDR_C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));
const ADDR_D: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 4));
const STRANGER: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 9, 9, 9));

/// `A` and `B` can host the actor; `C` and `D` only send to it.
const A: Id = Id(1);
const B: Id = Id(2);
const C: Id = Id(3);
const D: Id = Id(4);

fn roster() -> HashMap<IpAddr, Id> {
    HashMap::from([(ADDR_A, A), (ADDR_B, B), (ADDR_C, C), (ADDR_D, D)])
}

fn code(e: Error) -> Option<String> {
    e.code().map(String::from)
}

/// The actor and one connection per node. `x` belongs to nobody on the roster.
struct Cluster {
    host: Host,
    a: Connection,
    b: Connection,
    c: Connection,
    d: Connection,
    x: Connection,
}

impl Cluster {
    /// The whole journal, read over the wire by a node.
    async fn records(&self) -> Vec<Record> {
        self.b.journal(Context::default(), 0, 1024).await.unwrap()
    }

    async fn snapshot(&self) -> Snapshot {
        self.b.state(Context::default()).await.unwrap()
    }
}

/// The actor is offered to `A` at epoch 1.
async fn actor() -> Cluster {
    let host = Host::new(roster(), A, Arc::new(MemoryFloor::new())).expect("A is on the roster");
    Cluster {
        a: host.pipe(RemoteAddr::IpAddr(ADDR_A)).await,
        b: host.pipe(RemoteAddr::IpAddr(ADDR_B)).await,
        c: host.pipe(RemoteAddr::IpAddr(ADDR_C)).await,
        d: host.pipe(RemoteAddr::IpAddr(ADDR_D)).await,
        x: host.pipe(RemoteAddr::IpAddr(STRANGER)).await,
        host,
    }
}

/// `A` takes the actor.
async fn a_hosts(h: &Cluster) {
    assert_eq!(h.a.poll(Context::default()).await.unwrap(), Offer::Grant(1));
    h.a.acquire(Context::default(), 1).await.unwrap();
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
    let h = actor().await;
    a_hosts(&h).await;
    assert_eq!(h.c.send(Context::default(), 7).await.unwrap(), 0);
    assert_eq!(h.c.send(Context::default(), 9).await.unwrap(), 1);

    let r0 = h.a.accept(Context::default(), 1, C, 0).await.unwrap();
    assert_eq!(
        r0,
        Receipt {
            index: 0,
            body: 7,
            state: 7
        }
    );
    let r1 = h.a.accept(Context::default(), 1, C, 1).await.unwrap();
    assert_eq!(
        r1,
        Receipt {
            index: 1,
            body: 9,
            state: 7 * 31 + 9
        }
    );

    assert_eq!(
        h.b.state(Context::default()).await.unwrap(),
        Snapshot { len: 2, state: 226 }
    );
    assert_eq!(h.snapshot().await.state, fold(&h.records().await));
}

/// **A redelivered message is accepted once.**
#[tokio::test]
async fn a_redelivered_message_is_refused() {
    let h = actor().await;
    a_hosts(&h).await;
    h.c.send(Context::default(), 7).await.unwrap();
    h.a.accept(Context::default(), 1, C, 0).await.unwrap();
    let before = h.snapshot().await;

    for _ in 0..3 {
        assert_eq!(
            code(h.a.accept(Context::default(), 1, C, 0).await.unwrap_err()),
            Some("NO".into())
        );
    }
    assert_eq!(h.snapshot().await, before, "and nothing moved");
    assert_eq!(h.records().await.len(), 1);
}

/// **A message ahead of its turn waits for the ones before it.**
#[tokio::test]
async fn a_message_ahead_of_its_turn_is_refused_until_its_turn() {
    let h = actor().await;
    a_hosts(&h).await;
    h.c.send(Context::default(), 1).await.unwrap();
    h.c.send(Context::default(), 2).await.unwrap();

    assert_eq!(
        code(h.a.accept(Context::default(), 1, C, 1).await.unwrap_err()),
        Some("NO".into())
    );
    h.a.accept(Context::default(), 1, C, 0).await.unwrap();
    h.a.accept(Context::default(), 1, C, 1).await.unwrap();
    assert_eq!(
        h.records().await.iter().map(|r| r.seq).collect::<Vec<_>>(),
        vec![0, 1]
    );
}

/// Senders are counted separately: one sender's backlog does not hold up
/// another's messages.
#[tokio::test]
async fn senders_are_ordered_independently() {
    let h = actor().await;
    a_hosts(&h).await;
    h.c.send(Context::default(), 10).await.unwrap();
    h.d.send(Context::default(), 20).await.unwrap();
    h.a.accept(Context::default(), 1, D, 0).await.unwrap();
    h.a.accept(Context::default(), 1, C, 0).await.unwrap();
    assert_eq!(
        h.records()
            .await
            .iter()
            .map(|r| (r.sender, r.seq))
            .collect::<Vec<_>>(),
        vec![(D, 0), (C, 0)]
    );
}

#[tokio::test]
async fn a_message_nobody_sent_is_refused() {
    let h = actor().await;
    a_hosts(&h).await;
    assert_eq!(
        code(h.a.accept(Context::default(), 1, C, 0).await.unwrap_err()),
        Some("ERR".into())
    );
    h.c.send(Context::default(), 1).await.unwrap();
    assert_eq!(
        code(h.a.accept(Context::default(), 1, D, 0).await.unwrap_err()),
        Some("ERR".into())
    );
    assert!(h.records().await.is_empty());
}

/// **Only the owner, at the current epoch, appends.**
#[tokio::test]
async fn only_the_owner_at_its_epoch_may_append() {
    let h = actor().await;
    a_hosts(&h).await;
    h.c.send(Context::default(), 5).await.unwrap();

    // `B` does not own the actor.
    assert_eq!(
        code(h.b.accept(Context::default(), 1, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
    // `A` owns it, but not at epoch 2.
    assert_eq!(
        code(h.a.accept(Context::default(), 2, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert_eq!(
        code(h.a.accept(Context::default(), 0, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert!(h.records().await.is_empty());

    h.a.accept(Context::default(), 1, C, 0).await.unwrap();
}

/// A fenced host learns nothing about the journal: the fence is asked before
/// whether the message exists or whose turn it is.
#[tokio::test]
async fn the_fence_is_asked_first() {
    let h = actor().await;
    a_hosts(&h).await;
    // Nothing was sent, and `B` is not the owner: the answer is the fence's.
    assert_eq!(
        code(h.b.accept(Context::default(), 1, C, 0).await.unwrap_err()),
        Some("FENCED".into())
    );
}

/// **A handover moves the actor and its state — and fences the old host.**
#[tokio::test]
async fn a_handover_keeps_the_journal_and_fences_the_old_host() {
    let h = actor().await;
    a_hosts(&h).await;
    h.c.send(Context::default(), 7).await.unwrap();
    h.c.send(Context::default(), 9).await.unwrap();
    h.c.send(Context::default(), 11).await.unwrap();
    h.a.accept(Context::default(), 1, C, 0).await.unwrap();
    h.a.accept(Context::default(), 1, C, 1).await.unwrap();
    let before = h.snapshot().await;

    // `A` agrees to hand the actor to `B`. Its epoch is burned from this moment.
    h.a.begin_transfer(Context::default(), B).await.unwrap();
    assert_eq!(
        code(h.a.accept(Context::default(), 1, C, 2).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert_eq!(
        code(h.a.accept(Context::default(), 2, C, 2).await.unwrap_err()),
        Some("FENCED".into())
    );

    // `A` acknowledges and `B` takes the actor at epoch 2.
    assert_eq!(
        h.a.poll(Context::default()).await.unwrap(),
        Offer::Revoke(2)
    );
    h.a.release(Context::default(), 2).await.unwrap();
    assert_eq!(h.b.poll(Context::default()).await.unwrap(), Offer::Grant(2));
    h.b.acquire(Context::default(), 2).await.unwrap();

    // `B` did not receive the state; it reads the same journal and gets the same
    // state.
    assert_eq!(h.b.state(Context::default()).await.unwrap(), before);
    let caught_up = h.b.journal(Context::default(), 0, 100).await.unwrap();
    assert_eq!(caught_up.len(), 2);
    assert_eq!(fold(&caught_up), before.state);

    // `B` continues where `A` stopped.
    let r = h.b.accept(Context::default(), 2, C, 2).await.unwrap();
    assert_eq!(r.index, 2);
    assert_eq!(r.state, apply(before.state, 11));

    // `A`, still believing, is refused — and so is a redelivery to `B`.
    assert_eq!(
        code(h.a.accept(Context::default(), 1, C, 2).await.unwrap_err()),
        Some("FENCED".into())
    );
    assert_eq!(
        code(h.b.accept(Context::default(), 2, C, 0).await.unwrap_err()),
        Some("NO".into())
    );

    // Two hosts, two epochs, one journal, in order.
    let recs = h.records().await;
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
    let h = actor().await;
    a_hosts(&h).await;
    h.c.send(Context::default(), 3).await.unwrap();
    h.c.send(Context::default(), 4).await.unwrap();
    h.a.accept(Context::default(), 1, C, 0).await.unwrap();

    // `A` is unreachable. The coordinator burns its epoch and offers the actor to
    // `B`.
    assert_eq!(h.host.force(B).await.unwrap(), B);
    assert_eq!(
        code(h.a.accept(Context::default(), 1, C, 1).await.unwrap_err()),
        Some("FENCED".into())
    );

    assert_eq!(h.b.poll(Context::default()).await.unwrap(), Offer::Grant(2));
    h.b.acquire(Context::default(), 2).await.unwrap();
    assert_eq!(h.b.state(Context::default()).await.unwrap().len, 1);
    h.b.accept(Context::default(), 2, C, 1).await.unwrap();
    assert_eq!(h.snapshot().await.state, fold(&h.records().await));
}

/// **Every order of arrival, with every retry, gives a well-formed journal.**
///
/// Four messages from two senders, delivered in each of the 24 orders, each
/// attempted twice. Which interleaving the journal records depends on the order;
/// what must not depend on it is that each sender's messages appear once and in
/// sequence, and that the state is the fold of whatever the journal holds.
#[tokio::test]
async fn delivery_order_and_redelivery_cannot_corrupt_the_journal() {
    let msgs: [(Id, u64, IpAddr); 4] = [
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
        let h = actor().await;
        a_hosts(&h).await;
        for (i, (_, _, addr)) in msgs.iter().enumerate() {
            conn(&h, *addr)
                .send(Context::default(), 100 + i as u64)
                .await
                .unwrap();
        }
        // Two passes: a message that arrives ahead of its turn is picked up the
        // second time round.
        for _ in 0..2 {
            for &i in &order {
                let (sender, seq, _) = msgs[i];
                let _ = h.a.accept(Context::default(), 1, sender, seq).await;
            }
        }

        let recs = h.records().await;
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
        assert_eq!(h.snapshot().await.state, fold(&recs), "order {order:?}");
    }
}

fn conn(h: &Cluster, addr: IpAddr) -> &Connection {
    match addr {
        ADDR_C => &h.c,
        ADDR_D => &h.d,
        _ => unreachable!("only senders are looked up"),
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
    let h = actor().await;
    a_hosts(&h).await;
    for i in 0..5 {
        h.c.send(Context::default(), i).await.unwrap();
        h.a.accept(Context::default(), 1, C, i).await.unwrap();
    }
    let page = h.b.journal(Context::default(), 1, 2).await.unwrap();
    assert_eq!(page.iter().map(|r| r.seq).collect::<Vec<_>>(), vec![1, 2]);
    assert!(h
        .b
        .journal(Context::default(), 9, 2)
        .await
        .unwrap()
        .is_empty());
    assert_eq!(
        code(
            h.b.journal(Context::default(), 0, 100_000)
                .await
                .unwrap_err()
        ),
        Some("ERR".into())
    );
}

#[tokio::test]
async fn a_stranger_is_refused_by_every_door() {
    let h = actor().await;
    assert_eq!(
        code(h.x.poll(Context::default()).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.x.send(Context::default(), 1).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.x.accept(Context::default(), 1, C, 0).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.x.state(Context::default()).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(h.x.journal(Context::default(), 0, 1).await.unwrap_err()),
        Some("NO".into())
    );
    assert!(h.host.log().is_empty());
}

#[tokio::test]
async fn what_the_host_did_is_logged_in_order() {
    let h = actor().await;
    a_hosts(&h).await;
    h.c.send(Context::default(), 1).await.unwrap();
    h.a.accept(Context::default(), 1, C, 0).await.unwrap();
    assert_eq!(
        h.host.log(),
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
