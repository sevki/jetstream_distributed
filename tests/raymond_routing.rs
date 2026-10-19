//! The Raymond routing service: the textbook request path, run through the
//! verified steps, and every refusal those steps owe.
//!
//! `raymond::proofs::refinement` proves each step fires exactly when the model's
//! transition is enabled. These tests are that claim *exercised through the
//! service*, on the scenario the model's own docs draw:
//!
//! ```text
//! request:  D -> B -> A -> C[token]
//! token:    C -> A -> B -> D
//! ```
//!
//! They drive the `Router` directly. Identity still arrives the way the service
//! insists on, a `Context` carrying the caller's address and never an argument
//! naming the acting node.

use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr};

use jetstream_distributed::raymond::service::{Event, Router, Routing, Standing};
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

const ADDR_A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
const ADDR_B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));
const ADDR_C: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3));
const ADDR_D: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 4));
const STRANGER: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 9, 9, 9));

const A: u64 = 0;
const B: u64 = 1;
const C: u64 = 2;
const D: u64 = 3;

fn roster() -> HashMap<IpAddr, u64> {
    HashMap::from([(ADDR_A, A), (ADDR_B, B), (ADDR_C, C), (ADDR_D, D)])
}

fn from(addr: IpAddr) -> Context {
    Context::new(Some(RemoteAddr::IpAddr(addr)), None)
}

/// `C` holds the privilege; `A` points at `C`, `B` at `A`, `D` at `B`.
fn chain() -> Router {
    Router::new(roster(), C, HashMap::from([(A, C), (B, A), (D, B)])).expect("a tree rooted at C")
}

fn code(e: Error) -> Option<String> {
    e.code().map(String::from)
}

#[test]
fn a_router_must_be_a_tree_rooted_at_the_privilege() {
    let cases: [(&str, u64, HashMap<u64, u64>); 5] = [
        ("root off the roster", 9, HashMap::new()),
        ("a node with no parent", C, HashMap::from([(A, C), (B, A)])),
        (
            "a node that is its own parent",
            C,
            HashMap::from([(A, A), (B, A), (D, B)]),
        ),
        (
            "a parent off the roster",
            C,
            HashMap::from([(A, 9), (B, A), (D, B)]),
        ),
        // A and B point at each other, off to one side of the root C. There is
        // exactly one root and it is still not a tree.
        (
            "a cycle off to one side",
            C,
            HashMap::from([(A, B), (B, A), (D, B)]),
        ),
    ];
    for (name, root, parent) in cases {
        assert!(
            Router::new(roster(), root, parent).is_err(),
            "{name} must be refused"
        );
    }
}

/// **The textbook run, end to end.** `D` wants the privilege; the request hops
/// `D -> B -> A -> C`, the privilege hops back `C -> A -> B -> D`, and `D` enters.
#[tokio::test]
async fn the_privilege_travels_back_along_the_request_path() {
    let r = chain();
    assert!(r.well_formed());
    assert_eq!(r.privilege(), C);

    r.request_cs(from(ADDR_D)).await.unwrap();
    assert_eq!(r.queue_of(D), Some(vec![D]));

    // The request, hop by hop. Each hop is two model steps: the sender forwards
    // (resolving its holder pointer now) and the receiver accepts.
    assert_eq!(r.make_request(from(ADDR_D)).await.unwrap(), B);
    r.receive_request(from(ADDR_B), D).await.unwrap();
    assert_eq!(r.make_request(from(ADDR_B)).await.unwrap(), A);
    r.receive_request(from(ADDR_A), B).await.unwrap();
    assert_eq!(r.make_request(from(ADDR_A)).await.unwrap(), C);
    r.receive_request(from(ADDR_C), A).await.unwrap();
    assert!(r.well_formed());

    // The privilege, back along the reverse of that path.
    assert_eq!(r.assign_privilege(from(ADDR_C)).await.unwrap(), A);
    assert_eq!(r.privilege(), A);
    assert_eq!(r.assign_privilege(from(ADDR_A)).await.unwrap(), B);
    assert_eq!(r.assign_privilege(from(ADDR_B)).await.unwrap(), D);
    assert_eq!(r.privilege(), D);
    assert!(r.well_formed());

    r.enter_cs(from(ADDR_D)).await.unwrap();
    assert!(r.standing_of(D).unwrap().using);
    assert!(r.well_formed());
    r.exit_cs(from(ADDR_D)).await.unwrap();
    assert!(!r.standing_of(D).unwrap().using);

    assert_eq!(
        r.log(),
        vec![
            Event::Requested { node: D },
            Event::Forwarded { from: D, to: B },
            Event::Received { at: B, from: D },
            Event::Forwarded { from: B, to: A },
            Event::Received { at: A, from: B },
            Event::Forwarded { from: A, to: C },
            Event::Received { at: C, from: A },
            Event::Passed { from: C, to: A },
            Event::Passed { from: A, to: B },
            Event::Passed { from: B, to: D },
            Event::Entered { node: D },
            Event::Exited { node: D },
        ]
    );
}

/// The caller's own view is answered from the caller's own entries.
#[tokio::test]
async fn standing_is_the_callers_own_entries() {
    let r = chain();
    assert_eq!(
        r.standing(from(ADDR_C)).await.unwrap(),
        Standing {
            holder: C,
            asked: false,
            using: false,
            queued: 0,
            privileged: true
        }
    );
    assert_eq!(
        r.standing(from(ADDR_D)).await.unwrap(),
        Standing {
            holder: B,
            asked: false,
            using: false,
            queued: 0,
            privileged: false
        }
    );
}

/// The root has nobody to ask, a node asks once, and an empty queue has
/// nothing to ask for.
#[tokio::test]
async fn a_request_is_forwarded_only_when_there_is_one_to_forward() {
    let r = chain();
    assert_eq!(
        code(r.make_request(from(ADDR_D)).await.unwrap_err()),
        Some("NO".into()),
        "nothing queued"
    );

    r.request_cs(from(ADDR_C)).await.unwrap();
    assert_eq!(
        code(r.make_request(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into()),
        "the holder has nobody to ask"
    );

    r.request_cs(from(ADDR_D)).await.unwrap();
    r.make_request(from(ADDR_D)).await.unwrap();
    assert_eq!(
        code(r.make_request(from(ADDR_D)).await.unwrap_err()),
        Some("NO".into()),
        "already asked"
    );
}

/// **A request that was never sent cannot be received**, whoever claims to have
/// sent it.
#[tokio::test]
async fn a_request_must_have_been_sent_to_be_received() {
    let r = chain();
    r.request_cs(from(ADDR_D)).await.unwrap();
    r.make_request(from(ADDR_D)).await.unwrap(); // D -> B

    // A claims D asked it. D asked B.
    assert_eq!(
        code(r.receive_request(from(ADDR_A), D).await.unwrap_err()),
        Some("NO".into())
    );
    // Nobody asked C anything.
    assert_eq!(
        code(r.receive_request(from(ADDR_C), B).await.unwrap_err()),
        Some("NO".into())
    );
    // And a node that does not exist sent nothing.
    assert_eq!(
        code(r.receive_request(from(ADDR_B), 99).await.unwrap_err()),
        Some("ERR".into())
    );
    assert_eq!(r.queue_of(A), Some(vec![]));
    assert_eq!(r.queue_of(C), Some(vec![]));
}

/// **Duplicated, reordered and late requests are all permitted** — the model's
/// `ReceiveRequest` guard is the sent message, not the live topology.
///
/// The cost is fairness (extra queue entries), never safety.
#[tokio::test]
async fn a_request_may_arrive_twice_and_after_the_privilege_has_moved() {
    let r = chain();
    r.request_cs(from(ADDR_D)).await.unwrap();
    r.make_request(from(ADDR_D)).await.unwrap(); // D -> B

    r.receive_request(from(ADDR_B), D).await.unwrap();
    r.receive_request(from(ADDR_B), D).await.unwrap(); // a duplicate
    assert_eq!(r.queue_of(B), Some(vec![D, D]));
    assert!(r.well_formed());

    // Move the privilege somewhere else entirely, then deliver the old request
    // once more. The pointer D routed against is gone; the request is not.
    r.request_cs(from(ADDR_A)).await.unwrap();
    r.make_request(from(ADDR_A)).await.unwrap(); // A -> C
    r.receive_request(from(ADDR_C), A).await.unwrap();
    assert_eq!(r.assign_privilege(from(ADDR_C)).await.unwrap(), A);
    assert_eq!(r.privilege(), A);

    r.receive_request(from(ADDR_B), D).await.unwrap();
    assert_eq!(r.queue_of(B), Some(vec![D, D, D]));
    assert!(r.well_formed());
    assert_eq!(r.privilege(), A, "a late request moves nothing");
}

/// **Only the node that holds the privilege can pass it** — not one that merely
/// has a queue, and not one that is using it.
#[tokio::test]
async fn only_the_privileged_idle_node_with_a_waiter_can_pass_it() {
    let r = chain();
    // Not privileged.
    assert_eq!(
        code(r.assign_privilege(from(ADDR_A)).await.unwrap_err()),
        Some("NO".into())
    );
    // Privileged, but nobody is waiting.
    assert_eq!(
        code(r.assign_privilege(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into())
    );

    // Privileged, and the only waiter is itself: it enters, it does not pass.
    r.request_cs(from(ADDR_C)).await.unwrap();
    assert_eq!(
        code(r.assign_privilege(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into())
    );
    r.enter_cs(from(ADDR_C)).await.unwrap();

    // Inside its critical section it passes nothing, whoever is waiting.
    r.request_cs(from(ADDR_A)).await.unwrap();
    r.make_request(from(ADDR_A)).await.unwrap();
    r.receive_request(from(ADDR_C), A).await.unwrap();
    assert_eq!(
        code(r.assign_privilege(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into())
    );

    // Out of it, the waiter gets the privilege.
    r.exit_cs(from(ADDR_C)).await.unwrap();
    assert_eq!(r.assign_privilege(from(ADDR_C)).await.unwrap(), A);
}

#[tokio::test]
async fn entering_and_leaving_the_critical_section_have_guards_too() {
    let r = chain();
    // Not the holder.
    r.request_cs(from(ADDR_D)).await.unwrap();
    assert_eq!(
        code(r.enter_cs(from(ADDR_D)).await.unwrap_err()),
        Some("NO".into())
    );
    // Not in it.
    assert_eq!(
        code(r.exit_cs(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into())
    );

    // Holder, but the head of the queue is somebody else.
    r.request_cs(from(ADDR_A)).await.unwrap();
    r.make_request(from(ADDR_A)).await.unwrap();
    r.receive_request(from(ADDR_C), A).await.unwrap();
    r.request_cs(from(ADDR_C)).await.unwrap(); // queue at C: [A, C]
    assert_eq!(
        code(r.enter_cs(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(r.assign_privilege(from(ADDR_C)).await.unwrap(), A);
}

#[tokio::test]
async fn a_stranger_is_refused() {
    let r = chain();
    assert_eq!(
        code(r.request_cs(from(STRANGER)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(r.standing(Context::default()).await.unwrap_err()),
        Some("NO".into())
    );
    assert!(r.log().is_empty());
}

/// **Two nodes contending, one privilege.** However the requests interleave,
/// the privilege is at exactly one node and only a node that believes it holds
/// the privilege is ever inside its critical section.
#[tokio::test]
async fn two_contenders_are_served_one_at_a_time() {
    let r = Router::star(roster(), C).unwrap();
    for addr in [ADDR_A, ADDR_B] {
        r.request_cs(from(addr)).await.unwrap();
        r.make_request(from(addr)).await.unwrap();
    }
    r.receive_request(from(ADDR_C), A).await.unwrap();
    r.receive_request(from(ADDR_C), B).await.unwrap();
    assert_eq!(r.queue_of(C), Some(vec![A, B]));

    // A is served first.
    assert_eq!(r.assign_privilege(from(ADDR_C)).await.unwrap(), A);
    r.enter_cs(from(ADDR_A)).await.unwrap();
    assert!(r.well_formed());

    // B is not, while A is inside: C no longer holds the privilege, and A, which
    // does, will not pass it on while it is using it.
    assert_eq!(
        code(r.assign_privilege(from(ADDR_C)).await.unwrap_err()),
        Some("NO".into())
    );
    assert_eq!(
        code(r.assign_privilege(from(ADDR_A)).await.unwrap_err()),
        Some("NO".into())
    );
    assert!(!r.standing_of(B).unwrap().using);

    r.exit_cs(from(ADDR_A)).await.unwrap();
    assert!(r.well_formed());
}
