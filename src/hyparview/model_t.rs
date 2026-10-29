//! **HyParView's views and the handlers that keep them**, for one node.
//!
//! HyParView ("Hybrid Partial View", Leitão, Pereira and Rodrigues, 2007) is a
//! membership protocol that keeps no table of the cluster. A node holds two small
//! sets and nothing else:
//!
//! * an **active view**, at most `active_cap` peers, the ones it gossips with. Links
//!   in it are meant to be symmetric: if `a` is in `b`'s active view, `b` is in `a`'s.
//! * a **passive view**, at most `passive_cap` peers, a reserve of nodes it has heard
//!   of and could promote when an active peer is lost.
//!
//! Where SWIM answers "is each member up?", this answers "who should I talk to?".
//! There is no verdict on anyone: a peer leaves the active view because a link
//! closed or a slot was needed, not because it was judged dead.
//!
//! # What is here, and what is not
//!
//! The four handlers a node runs on the messages that build and prune the active
//! view: `Join` (a newcomer contacts it), `ForwardJoin` (a newcomer's join, walked
//! on), `Disconnect` (a peer drops the link) and `Neighbor` (a peer asks for the
//! link). What a node does on each is a step of [`HvStep`]; the random choices the
//! paper leaves to the node (which peer to demote, which passive entry to evict,
//! which neighbour to forward to) are existentials in the step, not parameters, so
//! the model says what is *allowed* and every refinement of it is a correct way to
//! choose.
//!
//! **Not here yet**, in the order SWIM was built:
//!
//! * **shuffle**, which refreshes the passive view; and
//! * **promotion on failure**, which fills a vacated active slot from the passive
//!   view with a `Neighbor` request that may be refused. It is what uses a
//!   detector's verdict, and nothing here has one.
//!
//! Without them a passive view only ever receives what forwarded joins and
//! demotions give it. The claims below do not need more.
//!
//! # The network
//!
//! Like [`crate::raft::model`], the model keeps every message the node has ever
//! sent, in `sent`, and the set only grows. A sent message may be delivered any
//! number of times and in any order, so a handler is correct only if it is safe to
//! run on a replay; nothing here assumes delivery. This is a **one-node** model:
//! the link-symmetry that makes a cluster of these an overlay is a property of how
//! several of them are connected, and is checked by tests, not stated here.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

verus! {

/// The protocol's four parameters (the paper's `c+1`, the passive capacity, ARWL
/// and PRWL).
pub struct HvParams {
    /// The most peers in the active view.
    pub active_cap: nat,
    /// The most peers in the passive view.
    pub passive_cap: nat,
    /// How many hops a `ForwardJoin` walks before its receiver takes the newcomer
    /// as an active peer (the active random walk length).
    pub arwl: nat,
    /// The hop count at which a `ForwardJoin`'s receiver also notes the newcomer in
    /// its passive view (the passive random walk length).
    pub prwl: nat,
}

/// The two views, and nothing else about a node.
pub struct Views {
    pub active: Set<Id>,
    pub passive: Set<Id>,
}

/// A message a node sends. Its sender is the node whose `sent` it is in.
pub enum HvMsg {
    /// "`new` is joining; take it on, or walk it `ttl` more hops."
    ForwardJoin { to: Id, new: Id, ttl: nat },
    /// "I am dropping the link between us."
    Disconnect { to: Id },
    /// "Please add me to your active view" (always high priority here).
    Neighbor { to: Id },
}

/// One node: who it is, its parameters, its views, and everything it has sent.
pub struct HvNode {
    pub me: Id,
    pub params: HvParams,
    pub active: Set<Id>,
    pub passive: Set<Id>,
    /// Every message this node has ever sent. Only grows.
    pub sent: Set<HvMsg>,
}

/// The views of a node.
pub open spec fn views_of(n: HvNode) -> Views {
    Views { active: n.active, passive: n.passive }
}

/// `n` goes into the passive view, evicting one entry if the view is full.
///
/// A node never holds itself, and never holds in the passive view a peer that is in
/// the active one, so for those `n` nothing happens.
pub open spec fn passive_added(me: Id, pcap: nat, v: Views, w: Views, n: Id) -> bool {
    if n == me || v.active.contains(n) || v.passive.contains(n) || pcap == 0 {
        w == v
    } else if v.passive.len() < pcap {
        w == Views { active: v.active, passive: v.passive.insert(n) }
    } else {
        exists|e: Id|
            #![trigger v.passive.contains(e)]
            v.passive.contains(e) && w == Views {
                active: v.active,
                passive: v.passive.remove(e).insert(n),
            }
    }
}

/// `n` goes into the active view. If the view is full one member, `dropped`, is
/// demoted to the passive view (and will be told to disconnect).
///
/// `n` leaves the passive view if it was there: a peer is promoted, not copied.
pub open spec fn active_added(
    me: Id,
    acap: nat,
    pcap: nat,
    v: Views,
    w: Views,
    n: Id,
    dropped: Option<Id>,
) -> bool {
    if n == me || v.active.contains(n) || acap == 0 {
        w == v && dropped is None
    } else if v.active.len() < acap {
        w == Views { active: v.active.insert(n), passive: v.passive.remove(n) } && dropped is None
    } else {
        exists|x: Id, mid: Views|
            #![trigger v.active.contains(x), passive_added(me, pcap, Views { active: v.active.remove(x), passive: v.passive.remove(n) }, mid, x)]
            v.active.contains(x) && dropped == Some(x) && passive_added(
                me,
                pcap,
                Views { active: v.active.remove(x), passive: v.passive.remove(n) },
                mid,
                x,
            ) && w == Views { active: mid.active.insert(n), passive: mid.passive }
    }
}

/// `m` is a `ForwardJoin` of `new` with `ttl` to some member of `to`, other than
/// `new` itself.
pub open spec fn is_forward(m: HvMsg, to: Set<Id>, new: Id, ttl: nat) -> bool {
    match m {
        HvMsg::ForwardJoin { to: t, new: n, ttl: l } => to.contains(t) && t != new && n == new
            && l == ttl,
        _ => false,
    }
}

/// `m` is the `Disconnect` that tells `dropped` (if any) its link is gone.
pub open spec fn is_disconnect_of(m: HvMsg, dropped: Option<Id>) -> bool {
    match m {
        HvMsg::Disconnect { to } => dropped == Some(to),
        _ => false,
    }
}

/// `m` is a `Neighbor` request to `to`.
pub open spec fn is_neighbor_to(m: HvMsg, to: Id) -> bool {
    match m {
        HvMsg::Neighbor { to: t } => t == to,
        _ => false,
    }
}

/// The labelled steps: a handler, and the message it is a handler for.
pub enum HvStep {
    /// A newcomer `new` contacted this node.
    Join { new: Id },
    /// A walk of `new`'s join, `ttl` hops left, arrived from active peer `sender`.
    ForwardJoin { new: Id, ttl: nat, sender: Id },
    /// `peer` dropped the link.
    Disconnect { peer: Id },
    /// `from` asked to be an active peer.
    Neighbor { from: Id },
}

/// Hold everything constant but the views and the outbox.
pub open spec fn same_node(pre: HvNode, post: HvNode) -> bool {
    &&& post.me == pre.me
    &&& post.params == pre.params
}

/// **A newcomer contacts this node.** It joins the active view (demoting a peer if
/// the view is full), and every other active peer is told to walk its join on.
pub open spec fn hv_join(pre: HvNode, post: HvNode, new: Id) -> bool {
    &&& new != pre.me
    &&& same_node(pre, post)
    &&& exists|dropped: Option<Id>, w: Views|
        #![trigger active_added(pre.me, pre.params.active_cap, pre.params.passive_cap, views_of(pre), w, new, dropped)]
        {
            &&& active_added(
                pre.me,
                pre.params.active_cap,
                pre.params.passive_cap,
                views_of(pre),
                w,
                new,
                dropped,
            )
            &&& post.active == w.active
            &&& post.passive == w.passive
            &&& forall|m: HvMsg|
                #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || is_forward(
                    m,
                    w.active,
                    new,
                    pre.params.arwl,
                ) || is_disconnect_of(m, dropped)
        }
}

/// **A walk of a join arrives.** At the end of the walk (no hops left, or no other
/// active peer to pass it to) the newcomer becomes an active peer and is asked to
/// reciprocate. Before the end it is passed to another active peer, and noted in the
/// passive view when the walk has reached `prwl`.
pub open spec fn hv_forward_join(pre: HvNode, post: HvNode, new: Id, ttl: nat, sender: Id) -> bool {
    &&& same_node(pre, post)
    &&& pre.active.contains(sender)
    &&& if new == pre.me {
        // A walk that has come back to the newcomer is ignored.
        post.active == pre.active && post.passive == pre.passive && post.sent == pre.sent
    } else if ttl == 0 || pre.active.remove(sender).len() == 0 {
        exists|dropped: Option<Id>, w: Views|
            #![trigger active_added(pre.me, pre.params.active_cap, pre.params.passive_cap, views_of(pre), w, new, dropped)]
            {
                &&& active_added(
                    pre.me,
                    pre.params.active_cap,
                    pre.params.passive_cap,
                    views_of(pre),
                    w,
                    new,
                    dropped,
                )
                &&& post.active == w.active
                &&& post.passive == w.passive
                &&& forall|m: HvMsg|
                    #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || is_neighbor_to(
                        m,
                        new,
                    ) || is_disconnect_of(m, dropped)
            }
    } else {
        exists|next: Id|
            #![trigger pre.active.remove(sender).contains(next)]
            {
                &&& pre.active.remove(sender).contains(next)
                &&& if ttl == pre.params.prwl {
                    exists|w: Views|
                        #![trigger passive_added(pre.me, pre.params.passive_cap, views_of(pre), w, new)]
                        {
                            &&& passive_added(pre.me, pre.params.passive_cap, views_of(pre), w, new)
                            &&& post.active == w.active
                            &&& post.passive == w.passive
                        }
                } else {
                    post.active == pre.active && post.passive == pre.passive
                }
                &&& forall|m: HvMsg|
                    #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || m
                        == HvMsg::ForwardJoin { to: next, new: new, ttl: (ttl - 1) as nat }
            }
    }
}

/// **A peer drops the link.** It leaves the active view and goes to the passive
/// one. A `Disconnect` from someone who is not an active peer changes nothing.
pub open spec fn hv_disconnect(pre: HvNode, post: HvNode, peer: Id) -> bool {
    &&& same_node(pre, post)
    &&& post.sent == pre.sent
    &&& if pre.active.contains(peer) {
        exists|w: Views|
            #![trigger passive_added(pre.me, pre.params.passive_cap, Views { active: pre.active.remove(peer), passive: pre.passive }, w, peer)]
            {
                &&& passive_added(
                    pre.me,
                    pre.params.passive_cap,
                    Views { active: pre.active.remove(peer), passive: pre.passive },
                    w,
                    peer,
                )
                &&& post.active == w.active
                &&& post.passive == w.passive
            }
    } else {
        post.active == pre.active && post.passive == pre.passive
    }
}

/// **A peer asks for the link.** Always granted (high priority), demoting a peer if
/// the view is full.
pub open spec fn hv_neighbor(pre: HvNode, post: HvNode, from: Id) -> bool {
    &&& same_node(pre, post)
    &&& exists|dropped: Option<Id>, w: Views|
        #![trigger active_added(pre.me, pre.params.active_cap, pre.params.passive_cap, views_of(pre), w, from, dropped)]
        {
            &&& active_added(
                pre.me,
                pre.params.active_cap,
                pre.params.passive_cap,
                views_of(pre),
                w,
                from,
                dropped,
            )
            &&& post.active == w.active
            &&& post.passive == w.passive
            &&& forall|m: HvMsg|
                #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || is_disconnect_of(
                    m,
                    dropped,
                )
        }
}

pub open spec fn hv_step(pre: HvNode, post: HvNode, s: HvStep) -> bool {
    match s {
        HvStep::Join { new } => hv_join(pre, post, new),
        HvStep::ForwardJoin { new, ttl, sender } => hv_forward_join(pre, post, new, ttl, sender),
        HvStep::Disconnect { peer } => hv_disconnect(pre, post, peer),
        HvStep::Neighbor { from } => hv_neighbor(pre, post, from),
    }
}

pub open spec fn hv_next(pre: HvNode, post: HvNode) -> bool {
    exists|s: HvStep| #[trigger] hv_step(pre, post, s)
}

/// An empty node: no peers, nothing sent.
pub open spec fn hv_init(n: HvNode) -> bool {
    &&& n.active == Set::<Id>::empty()
    &&& n.passive == Set::<Id>::empty()
    &&& n.sent == Set::<HvMsg>::empty()
}

/// The node as a [`Protocol`]. The configuration is the node's identity and
/// parameters.
pub struct HyParViewProtocol;

impl crate::protocol::Protocol for HyParViewProtocol {
    type Config = (Id, HvParams);
    type State = HvNode;
    type Step = HvStep;

    open spec fn init(cfg: (Id, HvParams), s: HvNode) -> bool {
        &&& s.me == cfg.0
        &&& s.params == cfg.1
        &&& hv_init(s)
    }

    open spec fn step(pre: HvNode, post: HvNode, label: HvStep) -> bool {
        hv_step(pre, post, label)
    }
}

} // verus!
