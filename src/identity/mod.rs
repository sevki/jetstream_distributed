//! Who is calling: one mechanism for every service.
//!
//! A service decides what a node may do, and so has to know which node is asking.
//! That must come from the connection and never from an argument naming the acting
//! node (a caller can write any number in an argument). Five services used to do it
//! five times, each with a private copy of the same table from an address to a node
//! number; this is the one thing they now ask.
//!
//! * [`Identity`], what a service holds: [`caller`](Identity::caller), which node
//!   this connection is, and [`nodes`](Identity::nodes), the nodes it can speak for.
//! * [`Roster`], the implementation there is: a table from the peer's address to its
//!   node number, fixed at construction.
//! * [`IntoIdentity`], so a service's constructor takes a table, a [`Roster`] or an
//!   `Arc<dyn Identity>` alike. A composition builds one `Arc` and gives the same one
//!   to both of its layers, so they cannot disagree about which address is which node.
//!
//! # The assumption this rests on
//!
//! **An address is not a credential.** [`Roster`] believes the transport's report of
//! the peer's address and nothing else. That is the stated assumption of every service
//! here, and it is now stated once: the thing to replace with TLS or any other proof of
//! identity is a different [`Identity`], and no service changes.
//!
//! # What this is not
//!
//! * **SWIM is not on it yet.** Its node is built with no table, and its methods take the
//!   sender in the message (a separate question, open on that service's own review).
//!   An adapter that derives the sender from [`Identity::caller`] and delegates to the
//!   transport-free methods is the natural next step and is not written.
//! * **Not verified.** This is plain Rust; the models know nothing of connections.

use std::collections::{BTreeSet, HashMap};
use std::net::IpAddr;
use std::sync::Arc;

use crate::id::Id;
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// Which node is calling, and which nodes there are.
pub trait Identity: Send + Sync {
    /// The node on the other end of this connection, from the transport and not from
    /// anything in the request. `None` when it is a machine this identity has never
    /// heard of, which is the only honest answer: it names no node, whatever it claims.
    fn caller(&self, ctx: &Context) -> Option<Id>;

    /// The nodes this identity can speak for, each once, in order.
    fn nodes(&self) -> Vec<Id>;

    /// Is `node` one of them?
    fn knows(&self, node: Id) -> bool {
        self.nodes().contains(&node)
    }
}

/// A table from a peer's address to its node number, fixed at construction.
///
/// Several addresses may name one node (a server is often reachable at more than one);
/// [`nodes`](Identity::nodes) counts each node once.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Roster {
    by_addr: HashMap<IpAddr, Id>,
}

impl Roster {
    /// The table `by_addr`.
    pub fn new(by_addr: HashMap<IpAddr, Id>) -> Self {
        Roster { by_addr }
    }
}

impl Identity for Roster {
    fn caller(&self, ctx: &Context) -> Option<Id> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) => self.by_addr.get(addr).copied(),
            _ => None,
        }
    }

    fn nodes(&self) -> Vec<Id> {
        self.by_addr
            .values()
            .copied()
            .collect::<BTreeSet<Id>>()
            .into_iter()
            .collect()
    }
}

/// Anything a service can be built from where it wants an [`Identity`].
pub trait IntoIdentity {
    /// The identity, shared.
    fn into_identity(self) -> Arc<dyn Identity>;
}

impl IntoIdentity for Arc<dyn Identity> {
    fn into_identity(self) -> Arc<dyn Identity> {
        self
    }
}

impl IntoIdentity for Roster {
    fn into_identity(self) -> Arc<dyn Identity> {
        Arc::new(self)
    }
}

impl IntoIdentity for HashMap<IpAddr, Id> {
    fn into_identity(self) -> Arc<dyn Identity> {
        Arc::new(Roster::new(self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::Ipv4Addr;

    const A: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1));
    const A2: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 1, 1));
    const B: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2));

    fn from(addr: Option<IpAddr>) -> Context {
        Context::new(addr.map(RemoteAddr::IpAddr), None)
    }

    fn roster() -> Roster {
        Roster::new(HashMap::from([(A, Id(10)), (A2, Id(10)), (B, Id(20))]))
    }

    #[test]
    fn a_caller_is_the_node_its_address_names() {
        let r = roster();
        assert_eq!(r.caller(&from(Some(A))), Some(Id(10)));
        assert_eq!(r.caller(&from(Some(A2))), Some(Id(10)));
        assert_eq!(r.caller(&from(Some(B))), Some(Id(20)));
    }

    #[test]
    fn a_stranger_and_a_connection_with_no_address_name_no_node() {
        let r = roster();
        let stranger = IpAddr::V4(Ipv4Addr::new(10, 9, 9, 9));
        assert_eq!(r.caller(&from(Some(stranger))), None);
        assert_eq!(r.caller(&from(None)), None);
    }

    #[test]
    fn nodes_are_counted_once_however_many_addresses_name_them() {
        let r = roster();
        assert_eq!(r.nodes(), vec![Id(10), Id(20)]);
        assert!(r.knows(Id(10)) && r.knows(Id(20)));
        assert!(!r.knows(Id(0)), "node numbers are values, not a range");
    }

    #[test]
    fn a_table_a_roster_and_a_shared_identity_are_the_same_identity() {
        let table = HashMap::from([(A, Id(10))]);
        let one = table.clone().into_identity();
        let two = Roster::new(table).into_identity();
        let three = one.clone().into_identity();
        for i in [one, two, three] {
            assert_eq!(i.caller(&from(Some(A))), Some(Id(10)));
        }
    }
}
