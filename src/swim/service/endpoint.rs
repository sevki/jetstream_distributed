//! Where a connection becomes a member: the [`Node`] behind an [`Authenticate`].
//!
//! [`Node`] knows nothing about transports. Its `ping` and `sync` take the caller's
//! `Id`, so they can be driven, and tested, with no connection at all. Something has
//! to turn a call arriving over one into that `Id`, and this is it. An [`Endpoint`]
//! is the [`Membership`] service: it asks its [`Authenticate`] who is calling,
//! refuses a caller it cannot identify, and otherwise hands the node the answer.
//!
//! The question is asked of the [`Context`], not of the request. A message cannot
//! name its own sender: the `Id` comes from the connection, through whatever the
//! `Authenticate` is willing to believe about it.
//!
//! # Writing an [`Authenticate`]
//!
//! One method, and a closure is one:
//!
//! ```
//! # use jetstream_distributed::swim::service::Authenticate;
//! # use jetstream_distributed::id::Id;
//! # use jetstream::prelude::*;
//! let everyone_is_member_7 = |_: &Context| Some(Id(7));
//! fn is_authenticate(_: &impl Authenticate) {}
//! is_authenticate(&everyone_is_member_7);
//! ```
//!
//! A test that wants a particular caller says so. A transport that can prove
//! something about its peer (the QUIC session's certificate chain is in
//! [`Context::peer`]) reads that, and maps it to an `Id`; nothing in the node or the
//! protocol changes. What the rules are (one live connection per member, a
//! certificate that has to chain to a given root, an address that has to be on a
//! list) belong to the `Authenticate`, and the node trusts the result.

use std::collections::HashMap;
use std::net::IpAddr;
use std::sync::Arc;

use super::refusal::refuse_no;
use super::{Membership, Node, Update};
use crate::id::Id;
use jetstream::prelude::jetstream_rpc::context::RemoteAddr;
use jetstream::prelude::*;

/// Who is calling, as far as the connection can say.
///
/// `None` is a caller that cannot be identified, and is refused. The answer is
/// the member's `Id`, and the node believes it, so this is where the trust is.
///
/// Called once per request, before the node's lock is taken, so it may be slow,
/// and it must not call into the node.
pub trait Authenticate: Send + Sync {
    /// The member `ctx`'s connection belongs to.
    fn identify(&self, ctx: &Context) -> Option<Id>;
}

impl<F> Authenticate for F
where
    F: Fn(&Context) -> Option<Id> + Send + Sync,
{
    fn identify(&self, ctx: &Context) -> Option<Id> {
        self(ctx)
    }
}

impl<A: Authenticate + ?Sized> Authenticate for Arc<A> {
    fn identify(&self, ctx: &Context) -> Option<Id> {
        (**self).identify(ctx)
    }
}

/// A fixed table from a connection's address to the member that address is.
///
/// **An address is not a credential.** Anything that can send from, or be
/// routed as, one of these addresses is that member. This is the weakest
/// [`Authenticate`] there is, and exists for simulations and tests, where there is
/// no transport security to read.
#[derive(Debug, Clone, Default)]
pub struct ByAddress(Arc<HashMap<IpAddr, Id>>);

impl ByAddress {
    /// The members at these addresses.
    pub fn new(members: impl IntoIterator<Item = (IpAddr, Id)>) -> Self {
        ByAddress(Arc::new(members.into_iter().collect()))
    }
}

impl Authenticate for ByAddress {
    fn identify(&self, ctx: &Context) -> Option<Id> {
        match ctx.remote() {
            Some(RemoteAddr::IpAddr(addr)) => self.0.get(addr).copied(),
            _ => None,
        }
    }
}

/// A [`Node`], served: the [`Membership`] service for callers an [`Authenticate`]
/// can identify.
#[derive(Clone)]
pub struct Endpoint<A> {
    node: Node,
    auth: A,
}

impl<A: Authenticate> Endpoint<A> {
    /// Serve `node` to the callers `auth` identifies.
    pub fn new(node: Node, auth: A) -> Self {
        Endpoint { node, auth }
    }

    /// The node behind it, for the things a node does that no caller may ask for
    /// (suspecting, declaring dead, leaving).
    pub fn node(&self) -> &Node {
        &self.node
    }

    fn caller(&self, ctx: &Context) -> Result<Id> {
        self.auth
            .identify(ctx)
            .ok_or_else(|| refuse_no("unknown caller"))
    }
}

impl<A: Authenticate> Membership for Endpoint<A> {
    async fn ping(&self, ctx: Context, updates: Vec<Update>) -> Result<Vec<Update>> {
        let from = self.caller(&ctx)?;
        self.node.ping(from, &updates)
    }

    async fn sync(&self, ctx: Context, updates: Vec<Update>) -> Result<Vec<Update>> {
        let from = self.caller(&ctx)?;
        self.node.sync(from, &updates)
    }
}
