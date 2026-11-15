//! The services ask an `Identity` who is calling; none of them owns a table of its own.
//!
//! The refusal tests in each service's own file run with a table from address to node,
//! which is one `Identity`. These use others, so that what the services depend on is the
//! trait: a different way of saying who is calling changes who is let in and nothing
//! else, and a composition gives both of its layers the one it was handed.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;
use jetstream_distributed::composed::service::{Composed, Coordinator};
use jetstream_distributed::id::Id;
use jetstream_distributed::identity::{Identity, Roster};
use jetstream_distributed::ownership::service::{MemoryFloor, Offer, Ownership, Registry};

const A: Id = Id(0);
const B: Id = Id(1);
const SOMEWHERE: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 7, 7, 7));

fn from_anywhere() -> Context {
    Context::new(Some(RemoteAddr::IpAddr(SOMEWHERE)), None)
}

/// Every connection is `who`, wherever it comes from, and `A` and `B` exist.
/// Counts how often it is asked.
struct Everyone {
    who: Id,
    asked: AtomicUsize,
}

impl Identity for Everyone {
    fn caller(&self, _: &Context) -> Option<Id> {
        self.asked.fetch_add(1, Ordering::SeqCst);
        Some(self.who)
    }
    fn nodes(&self) -> Vec<Id> {
        vec![A, B]
    }
}

/// Nobody is anybody, though both nodes exist.
struct Nobody;

impl Identity for Nobody {
    fn caller(&self, _: &Context) -> Option<Id> {
        None
    }
    fn nodes(&self) -> Vec<Id> {
        vec![A, B]
    }
}

fn is_unknown(e: Error) -> bool {
    e.code().map(String::from).as_deref() == Some("NO")
}

#[tokio::test]
async fn a_registry_takes_its_callers_from_whatever_identity_it_is_given() {
    // The address is a stranger to any table; this identity says it is `A`.
    let who = Arc::new(Everyone { who: A, asked: AtomicUsize::new(0) });
    let registry = Registry::new(who.clone() as Arc<dyn Identity>, A, Arc::new(MemoryFloor::new())).unwrap();
    assert_eq!(registry.poll(from_anywhere()).await.unwrap(), Offer::Grant(1));
    assert_eq!(who.asked.load(Ordering::SeqCst), 1, "the registry asked it");

    // The same registry with an identity that names nobody refuses the same call.
    let registry = Registry::new(Arc::new(Nobody) as Arc<dyn Identity>, A, Arc::new(MemoryFloor::new())).unwrap();
    assert!(is_unknown(registry.poll(from_anywhere()).await.unwrap_err()));
}

#[tokio::test]
async fn a_node_the_identity_does_not_know_cannot_be_the_first_owner() {
    let err = Registry::new(Arc::new(Nobody) as Arc<dyn Identity>, Id(99), Arc::new(MemoryFloor::new()))
        .err()
        .expect("99 is not a node");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput);
}

#[tokio::test]
async fn a_coordinator_hands_the_one_identity_to_both_layers() {
    let who = Arc::new(Everyone { who: A, asked: AtomicUsize::new(0) });
    let c = Coordinator::star(who.clone() as Arc<dyn Identity>, A, Arc::new(MemoryFloor::new()), A).unwrap();
    // One call into the ownership layer and one into the routing layer, both through it.
    assert_eq!(c.poll(from_anywhere()).await.unwrap(), Offer::Grant(1));
    let after_ownership = who.asked.load(Ordering::SeqCst);
    c.standing(from_anywhere()).await.unwrap();
    let after_routing = who.asked.load(Ordering::SeqCst);
    assert!(after_ownership >= 1, "the ownership layer asked it");
    assert!(after_routing > after_ownership, "the routing layer asked the same one");

    // And with an identity that names nobody, both layers refuse.
    let c = Coordinator::star(Arc::new(Nobody) as Arc<dyn Identity>, A, Arc::new(MemoryFloor::new()), A).unwrap();
    assert!(is_unknown(c.poll(from_anywhere()).await.unwrap_err()));
    assert!(is_unknown(c.standing(from_anywhere()).await.unwrap_err()));
}

#[tokio::test]
async fn a_table_is_still_an_identity() {
    let table = HashMap::from([(SOMEWHERE, A), (IpAddr::V4(Ipv4Addr::new(10, 7, 7, 8)), B)]);
    let c = Coordinator::star(Roster::new(table.clone()), A, Arc::new(MemoryFloor::new()), A).unwrap();
    assert_eq!(c.poll(from_anywhere()).await.unwrap(), Offer::Grant(1));
    // The bare table works too, as it always has.
    let c = Coordinator::star(table, A, Arc::new(MemoryFloor::new()), A).unwrap();
    assert_eq!(c.poll(from_anywhere()).await.unwrap(), Offer::Grant(1));
}
