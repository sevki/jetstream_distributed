//! The composed service: ownership and Raymond behind one coordinator, and the
//! coupling that is the only thing the composition adds.
//!
//! `composed::proofs::refinement` proves each coupling guard fires exactly when
//! the composed model's transition is enabled, and `composed::proofs::coupling`
//! proves `couples` is an invariant of that model. These are the guards
//! *exercised through the service* — the refusals especially, because a
//! coordinator that delegated everything and enforced nothing would pass every
//! test of the happy path.
//!
//! They drive the `Coordinator` directly. Identity still arrives the way the
//! service insists on: a `Context` carrying the caller's address, never an
//! argument naming the acting node.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;

use jetstream_distributed::composed::service::{Composed, Coordinator, Event};
use jetstream_distributed::id::Id;
use jetstream_distributed::ownership::service::{MemoryFloor, Offer};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

const ADDR_A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const ADDR_B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const ADDR_C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));
const STRANGER: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 9, 9, 9));

const A: Id = Id(0);
const B: Id = Id(1);
const C: Id = Id(2);

fn roster() -> HashMap<IpAddr, Id> {
    HashMap::from([(ADDR_A, A), (ADDR_B, B), (ADDR_C, C)])
}

fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

fn code(e: Error) -> Option<String> {
    e.code().map(String::from)
}

/// The actor starts offered to `A`, and the privilege starts at `A`: the two
/// layers agree about who is first.
fn system() -> Coordinator {
    Coordinator::star(roster(), A, Arc::new(MemoryFloor::new()), A).expect("a star rooted at A")
}

/// `A` takes the actor at epoch 1 and writes once.
async fn a_owns(c: &Coordinator) {
    assert_eq!(c.poll(from(ADDR_A)).await.unwrap(), Offer::Grant(1));
    c.acquire(from(ADDR_A), 1).await.unwrap();
    assert_eq!(c.write(from(ADDR_A), 1).await.unwrap(), 1);
}

/// **A cooperative handover across both layers.**
///
/// `B` asks for the privilege; `A` agrees to hand the actor over; the privilege
/// moves only once `A` has released, and `B` takes authority only once it holds
/// the privilege.
#[tokio::test]
async fn the_privilege_moves_only_after_the_actor_has_been_released() {
    let c = system();
    a_owns(&c).await;

    // B wants it, and asks A, which holds the privilege.
    c.request_cs(from(ADDR_B)).await.unwrap();
    assert_eq!(c.make_request(from(ADDR_B)).await.unwrap(), A);
    c.receive_request(from(ADDR_A), B).await.unwrap();

    // A agrees to hand the actor over. Authority is fenced from this moment.
    c.begin_transfer(from(ADDR_A), B).await.unwrap();

    // The routing layer would pass the privilege now: A holds it, is not using
    // it, and B is waiting. **The coupling refuses**, because the outgoing owner
    // has not acknowledged the revoke.
    assert_eq!(
        code(c.assign_privilege(from(ADDR_A)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(c.privilege(), A, "and nothing moved");

    // A acknowledges. Now the actor is Unowned, offered to B...
    assert_eq!(c.poll(from(ADDR_A)).await.unwrap(), Offer::Revoke(2));
    c.release(from(ADDR_A), 2).await.unwrap();

    // ...but B cannot take it: it is offered to B and B does not yet hold the
    // privilege. **Authority cannot be taken by a node the routing layer has
    // not elected.**
    assert_eq!(
        code(c.acquire(from(ADDR_B), 2).await.unwrap_err()),
        Some("NO".into())
    );

    // The privilege moves.
    assert_eq!(c.assign_privilege(from(ADDR_A)).await.unwrap(), B);
    assert_eq!(c.privilege(), B);

    // And now B may take the actor.
    c.acquire(from(ADDR_B), 2).await.unwrap();
    assert_eq!(c.write(from(ADDR_B), 2).await.unwrap(), 2);

    // A, still believing it owns at epoch 1, is fenced.
    assert_eq!(
        code(c.write(from(ADDR_A), 1).await.unwrap_err()),
        Some("FENCED".into())
    );

    assert!(c.well_formed());
    assert!(c.stale_holders().is_empty());
    assert!(c.seized().is_empty());
}

/// **A node that merely has the actor offered to it, without the privilege,
/// cannot take it** — even though the ownership layer alone would let it.
#[tokio::test]
async fn an_offer_without_the_privilege_is_not_enough() {
    let c = system();
    a_owns(&c).await;
    c.begin_transfer(from(ADDR_A), C).await.unwrap();
    c.release(from(ADDR_A), 2).await.unwrap();

    // Offered to C. C does not hold the privilege; A still does.
    assert_eq!(c.poll(from(ADDR_C)).await.unwrap(), Offer::Grant(2));
    assert_eq!(
        code(c.acquire(from(ADDR_C), 2).await.unwrap_err()),
        Some("NO".into())
    );
}

/// **Seizure: the privilege is taken from a holder that does not act.**
///
/// `A` owns the actor and is unreachable. The coordinator revokes (burning the
/// epoch, which fences `A`), then seizes the privilege for `B`. Nothing
/// belonging to `A` is touched, so `A` is a stale holder: it believes it holds
/// the privilege and does not. Ownership is safe regardless — the epoch fences
/// it — and `A` owes a reconciliation.
#[tokio::test]
async fn the_privilege_can_be_seized_from_a_holder_that_does_not_cooperate() {
    let c = system();
    a_owns(&c).await;

    // The privilege cannot be seized while the actor is owned: someone has
    // authority and it would be stranded.
    assert_eq!(code(c.seize_token(B).await.unwrap_err()), Some("NO".into()));
    assert_eq!(c.privilege(), A);

    // Revoke. The epoch is burned; the actor is Unowned at 2, offered to B.
    assert_eq!(c.force(B).await.unwrap(), B);
    assert_eq!(c.seize_token(B).await.unwrap(), A);

    assert_eq!(c.privilege(), B);
    assert_eq!(c.stale_holders(), vec![A], "A still believes");
    assert_eq!(c.seized(), vec![A], "and owes a reconciliation");
    assert!(
        c.well_formed(),
        "a stale holder is a state the routing layer admits"
    );
    assert_eq!(c.log(), vec![Event::Seized { from: A, to: B }]);

    // A's belief is stale and inert: it still thinks it holds the privilege...
    let a = c.standing(from(ADDR_A)).await.unwrap();
    assert_eq!(a.holder, A);
    assert!(!a.privileged);
    // ...but cannot mutate: the epoch fenced it before the seizure.
    assert_eq!(
        code(c.write(from(ADDR_A), 1).await.unwrap_err()),
        Some("FENCED".into())
    );

    // B holds the privilege, so B may take the actor.
    assert_eq!(c.poll(from(ADDR_B)).await.unwrap(), Offer::Grant(2));
    c.acquire(from(ADDR_B), 2).await.unwrap();

    // A reconciles: it learns the truth, drops the belief, and the debt is paid.
    c.reconcile(from(ADDR_A)).await.unwrap();
    let a = c.standing(from(ADDR_A)).await.unwrap();
    assert_eq!(a.holder, B, "A now points at the real holder");
    assert!(c.stale_holders().is_empty());
    assert!(c.seized().is_empty());
    assert!(c.well_formed());
    assert_eq!(
        c.log(),
        vec![
            Event::Seized { from: A, to: B },
            Event::Reconciled { node: A }
        ]
    );
}

/// A stale holder that was inside its critical section is taken out of it by
/// reconciling — Raymond's critical section has no epoch, so the belief has to
/// be repaired by the node that holds it.
#[tokio::test]
async fn reconciling_takes_a_stale_holder_out_of_its_critical_section() {
    let c = system();
    c.request_cs(from(ADDR_A)).await.unwrap();
    c.enter_cs(from(ADDR_A)).await.unwrap();
    assert!(c.standing_of(A).unwrap().using);

    // The actor is Unowned from the start (offered to A, never acquired), so the
    // privilege can be seized from A while A is inside its critical section.
    c.seize_token(B).await.unwrap();
    assert!(
        c.standing_of(A).unwrap().using,
        "A does not know; nothing reached it"
    );
    assert!(
        c.well_formed(),
        "using => believes still holds, so the layer's invariant does"
    );

    c.reconcile(from(ADDR_A)).await.unwrap();
    assert!(!c.standing_of(A).unwrap().using);
}

#[tokio::test]
async fn seizure_has_its_own_refusals() {
    let c = system();
    // Nothing to seize: B is not the holder, but seizing *to* the holder is.
    assert_eq!(code(c.seize_token(A).await.unwrap_err()), Some("NO".into()));
    // Not a node.
    assert_eq!(
        code(c.seize_token(Id(99)).await.unwrap_err()),
        Some("ERR".into())
    );
    // Nobody owes anything, so nobody may reconcile.
    assert_eq!(
        code(c.reconcile(from(ADDR_A)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(c.privilege(), A);
    assert!(c.log().is_empty());
}

/// A node that was never seized from cannot reconcile, even though it could
/// invent a belief to be stale about.
#[tokio::test]
async fn only_a_seized_node_may_reconcile() {
    let c = system();
    c.seize_token(B).await.unwrap();
    // C was not seized from.
    assert_eq!(
        code(c.reconcile(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into())
    );
    // B holds the privilege; it is not stale.
    assert_eq!(
        code(c.reconcile(from(ADDR_B)).await.unwrap_err()),
        Some("NO".into())
    );
    c.reconcile(from(ADDR_A)).await.unwrap();
    // And once is enough.
    assert_eq!(
        code(c.reconcile(from(ADDR_A)).await.unwrap_err()),
        Some("NO".into())
    );
}

#[tokio::test]
async fn a_stranger_is_refused_by_every_door() {
    let c = system();
    assert_eq!(
        code(c.acquire(from(STRANGER), 1).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(c.reconcile(from(STRANGER)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(c.request_cs(from(STRANGER)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(c.poll(from(STRANGER)).await.unwrap_err()),
        Some("NO".into())
    );
    assert!(c.log().is_empty());
}

/// Both layers are built from the one roster the coordinator is given, so a
/// bad first owner or a bad routing tree is refused at construction rather than
/// discovered as a disagreement between layers.
#[test]
fn both_layers_are_built_from_one_roster_or_not_at_all() {
    let floor = || Arc::new(MemoryFloor::new());
    // The actor cannot be offered to a node that is not on the roster.
    assert!(Coordinator::star(roster(), Id(9), floor(), A).is_err());
    // Nor can the privilege start at one.
    assert!(Coordinator::star(roster(), A, floor(), Id(9)).is_err());
    // And the routing tree is checked: B and C point at each other, off to one
    // side of the root A.
    let cycle = HashMap::from([(B, C), (C, B)]);
    assert!(Coordinator::new(roster(), A, floor(), A, cycle).is_err());
}
