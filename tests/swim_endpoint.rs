//! Who is calling: the one place a connection becomes a member.
//!
//! `Node` takes an `Id` and believes it (`tests/swim_membership.rs`,
//! `tests/swim_dynamic.rs`). `Endpoint` is the part that gets the `Id` from a
//! `Context`, by asking an `Authenticate`, and these tests are about that seam and
//! nothing else: a refused caller reaches nothing, an accepted one reaches the node
//! as exactly the member the authenticator said, and the authenticator is asked
//! every time.
//!
//! Every authenticator here is a few lines written for the test. That is the
//! point of the seam: no transport, no certificate and no address table is needed
//! to say who is calling.

use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;
use jetstream_distributed::id::Id;
use jetstream_distributed::swim::service::{
    Authenticate, ByAddress, Endpoint, Liveness, Membership, Node, Update,
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

fn served<A: Authenticate>(me: u128, auth: A) -> Endpoint<A> {
    Endpoint::new(Node::new(Id(me)), auth)
}

/// An authenticator that identifies nobody: a cluster nobody can join.
#[tokio::test]
async fn a_caller_who_cannot_be_identified_reaches_nothing() {
    let e = served(1, |_: &Context| None);
    for r in [
        e.ping(from(addr(2)), vec![u(2, 0, Liveness::Dead)]).await,
        e.sync(from(addr(2)), vec![u(2, 0, Liveness::Dead)]).await,
        e.ping(Context::default(), vec![]).await,
    ] {
        assert_eq!(r.unwrap_err().code(), Some("NO"));
    }
    assert_eq!(e.node().record(Id(2)), None, "and nothing it said was applied");
    assert_eq!(e.node().view(), vec![u(1, 0, Liveness::Alive)]);
}

/// The member is whoever the authenticator says. The message cannot name it.
#[tokio::test]
async fn the_member_is_the_one_the_authenticator_named() {
    // Reads the last octet of the address as the member number: anything at all
    // that can be computed from a `Context` will do.
    let by_last_octet = |ctx: &Context| match ctx.remote() {
        Some(RemoteAddr::IpAddr(IpAddr::V4(v4))) => Some(Id(v4.octets()[3] as u128)),
        _ => None,
    };
    let e = served(1, by_last_octet);

    // The caller at .3 says whatever it likes about 5: gossip about 5.
    e.ping(from(addr(3)), vec![u(5, 0, Liveness::Dead)])
        .await
        .unwrap();
    assert_eq!(e.node().record(Id(3)), Some(u(3, 0, Liveness::Alive)), "it joined as 3");
    assert_eq!(e.node().record(Id(5)), Some(u(5, 0, Liveness::Dead)));

    // 5 itself, calling from .5, is admitted as 5 and is told what is said of it.
    let reply = e
        .ping(from(addr(5)), vec![u(5, 0, Liveness::Alive)])
        .await
        .unwrap();
    assert_eq!(
        reply,
        vec![u(1, 0, Liveness::Alive), u(5, 0, Liveness::Dead)]
    );
}

/// The authenticator is asked on every request, so what it forgets or revokes
/// takes effect on the next one.
#[tokio::test]
async fn the_authenticator_is_asked_every_time() {
    struct Revocable {
        revoked: AtomicBool,
        asked: AtomicUsize,
    }
    impl Authenticate for Revocable {
        fn identify(&self, _: &Context) -> Option<Id> {
            self.asked.fetch_add(1, Ordering::SeqCst);
            (!self.revoked.load(Ordering::SeqCst)).then_some(Id(2))
        }
    }

    let auth = Arc::new(Revocable {
        revoked: AtomicBool::new(false),
        asked: AtomicUsize::new(0),
    });
    let e = served(1, auth.clone());

    e.ping(from(addr(2)), vec![]).await.unwrap();
    e.sync(from(addr(2)), vec![]).await.unwrap();
    assert_eq!(auth.asked.load(Ordering::SeqCst), 2);

    auth.revoked.store(true, Ordering::SeqCst);
    let err = e.ping(from(addr(2)), vec![]).await.unwrap_err();
    assert_eq!(err.code(), Some("NO"), "revoked: the same connection is refused");
    assert_eq!(auth.asked.load(Ordering::SeqCst), 3);
    assert_eq!(
        e.node().record(Id(2)),
        Some(u(2, 0, Liveness::Alive)),
        "it stays a member: leaving is the node's business, not the connection's"
    );
}

/// The simulation authenticator: a fixed table from address to member.
#[tokio::test]
async fn by_address_knows_the_addresses_it_was_given_and_no_others() {
    let e = served(1, ByAddress::new([(addr(1), Id(1)), (addr(2), Id(2))]));

    e.ping(from(addr(2)), vec![]).await.unwrap();
    assert_eq!(e.node().record(Id(2)), Some(u(2, 0, Liveness::Alive)));

    let off = from(addr(77));
    assert_eq!(e.ping(off.clone(), vec![]).await.unwrap_err().code(), Some("NO"));
    assert_eq!(e.sync(off, vec![]).await.unwrap_err().code(), Some("NO"));
    assert_eq!(
        e.ping(Context::default(), vec![]).await.unwrap_err().code(),
        Some("NO"),
        "a connection with no address at all is not on the table"
    );
}

/// An `Arc` of an authenticator is one, so a test can keep a handle to it, and a
/// closure is one, so a test needs no type at all.
#[tokio::test]
async fn closures_and_shared_handles_are_authenticators() {
    let always_two = served(1, |_: &Context| Some(Id(2)));
    always_two.ping(Context::default(), vec![]).await.unwrap();
    assert!(always_two.node().record(Id(2)).is_some());

    let shared = served(1, Arc::new(ByAddress::new([(addr(4), Id(4))])));
    shared.sync(from(addr(4)), vec![]).await.unwrap();
    assert!(shared.node().record(Id(4)).is_some());
}
