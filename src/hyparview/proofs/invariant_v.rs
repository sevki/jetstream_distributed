//! **A node's views stay well-formed**, whatever it hears, in whatever order, any
//! number of times.
//!
//! Three things make a peer sample trustworthy, and a handler that lost one in its
//! glue would leave the protocol's description true and the node wrong:
//!
//! * **a node is never its own peer**, in either view;
//! * **a peer is in one view or the other, never both**, so promoting one is a move
//!   and not a copy; and
//! * **the views are bounded**, so "a small partial view" is a fact and not an
//!   intention.
//!
//! They are proved for the two small relations every handler is built from
//! ([`passive_added`], [`active_added`]), and then for the handlers. The network
//! is adversarial in the way [`crate::hyparview::model`] says: a message may arrive
//! any number of times and in any order, and the theorem covers every one of them
//! because it is about one step from *any* well-formed state.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::hyparview::model::*;
use crate::id::Id;

verus! {

/// The views are well-formed for a node `me` with these capacities.
pub open spec fn views_ok(me: Id, acap: nat, pcap: nat, v: Views) -> bool {
    &&& !v.active.contains(me)
    &&& !v.passive.contains(me)
    &&& forall|x: Id| !(#[trigger] v.active.contains(x) && v.passive.contains(x))
    &&& v.active.len() <= acap
    &&& v.passive.len() <= pcap
}

/// The invariant: a node's views are well-formed.
pub open spec fn hv_inv(n: HvNode) -> bool {
    views_ok(n.me, n.params.active_cap, n.params.passive_cap, views_of(n))
}

/// Adding to the passive view keeps the views well-formed, and leaves the active
/// view alone.
pub proof fn lemma_passive_added_keeps_views_ok(
    me: Id,
    acap: nat,
    pcap: nat,
    v: Views,
    w: Views,
    n: Id,
)
    requires
        views_ok(me, acap, pcap, v),
        passive_added(me, pcap, v, w, n),
    ensures
        views_ok(me, acap, pcap, w),
        w.active == v.active,
        w.passive.subset_of(v.passive.insert(n)),
{
    if n == me || v.active.contains(n) || v.passive.contains(n) || pcap == 0 {
        assert(w == v);
    } else if v.passive.len() < pcap {
        assert(w == Views { active: v.active, passive: v.passive.insert(n) });
    } else {
        let e = choose|e: Id| #[trigger] v.passive.contains(e) && w == Views {
            active: v.active,
            passive: v.passive.remove(e).insert(n),
        };
        assert(v.passive.contains(e));
        assert(w == Views { active: v.active, passive: v.passive.remove(e).insert(n) });
    }
}

/// Adding to the active view keeps the views well-formed, makes `n` an active peer
/// (unless it is the node itself, or the view has no room at all), and takes it out
/// of the passive view.
pub proof fn lemma_active_added_keeps_views_ok(
    me: Id,
    acap: nat,
    pcap: nat,
    v: Views,
    w: Views,
    n: Id,
    dropped: Option<Id>,
)
    requires
        views_ok(me, acap, pcap, v),
        active_added(me, acap, pcap, v, w, n, dropped),
    ensures
        views_ok(me, acap, pcap, w),
        !w.passive.contains(n) || n == me || acap == 0,
        n != me && acap > 0 ==> w.active.contains(n),
        match dropped {
            Some(x) => v.active.contains(x) && !w.active.contains(x),
            None => true,
        },
{
    if n == me || v.active.contains(n) || acap == 0 {
        assert(w == v);
    } else if v.active.len() < acap {
        assert(w == Views { active: v.active.insert(n), passive: v.passive.remove(n) });
    } else {
        let (x, mid) = choose|x: Id, mid: Views|
            v.active.contains(x) && dropped == Some(x) && passive_added(
                me,
                pcap,
                Views { active: v.active.remove(x), passive: v.passive.remove(n) },
                mid,
                x,
            ) && w == Views { active: mid.active.insert(n), passive: mid.passive };
        let v1 = Views { active: v.active.remove(x), passive: v.passive.remove(n) };
        assert(views_ok(me, acap, pcap, v1));
        lemma_passive_added_keeps_views_ok(me, acap, pcap, v1, mid, x);
        assert(mid.active == v1.active);
        assert(v.active.len() == acap);
        assert(x != n);
        assert(!mid.passive.contains(n));
    }
}

/// Every handler keeps the views well-formed.
pub proof fn theorem_every_step_keeps_the_views_well_formed(pre: HvNode, post: HvNode, s: HvStep)
    requires
        hv_inv(pre),
        hv_step(pre, post, s),
    ensures
        hv_inv(post),
{
    let me = pre.me;
    let acap = pre.params.active_cap;
    let pcap = pre.params.passive_cap;
    match s {
        HvStep::Join { new } => {
            let (dropped, w) = choose|dropped: Option<Id>, w: Views|
                active_added(me, acap, pcap, views_of(pre), w, new, dropped)
                    && post.active == w.active && post.passive == w.passive;
            lemma_active_added_keeps_views_ok(me, acap, pcap, views_of(pre), w, new, dropped);
        },
        HvStep::ForwardJoin { new, ttl, sender } => {
            if new == me || !pre.active.contains(sender) {
            } else if ttl == 0 || pre.active.remove(sender).len() == 0 {
                let (dropped, w) = choose|dropped: Option<Id>, w: Views|
                    active_added(me, acap, pcap, views_of(pre), w, new, dropped)
                        && post.active == w.active && post.passive == w.passive;
                lemma_active_added_keeps_views_ok(me, acap, pcap, views_of(pre), w, new, dropped);
            } else {
                let next = choose|next: Id| pre.active.remove(sender).contains(next)
                    && (if ttl == pre.params.prwl {
                    exists|w: Views|
                        #![trigger passive_added(me, pcap, views_of(pre), w, new)]
                        passive_added(me, pcap, views_of(pre), w, new) && post.active == w.active
                            && post.passive == w.passive
                } else {
                    post.active == pre.active && post.passive == pre.passive
                });
                if ttl == pre.params.prwl {
                    let w = choose|w: Views|
                        #[trigger] passive_added(me, pcap, views_of(pre), w, new)
                            && post.active == w.active && post.passive == w.passive;
                    lemma_passive_added_keeps_views_ok(me, acap, pcap, views_of(pre), w, new);
                }
            }
        },
        HvStep::Disconnect { peer } => {
            if pre.active.contains(peer) {
                let w = choose|w: Views|
                    #[trigger] passive_added(
                        me,
                        pcap,
                        Views { active: pre.active.remove(peer), passive: pre.passive },
                        w,
                        peer,
                    ) && post.active == w.active && post.passive == w.passive;
                let v1 = Views { active: pre.active.remove(peer), passive: pre.passive };
                assert(views_ok(me, acap, pcap, v1));
                lemma_passive_added_keeps_views_ok(me, acap, pcap, v1, w, peer);
            }
        },
        HvStep::Neighbor { from } => {
            let (dropped, w) = choose|dropped: Option<Id>, w: Views|
                active_added(me, acap, pcap, views_of(pre), w, from, dropped)
                    && post.active == w.active && post.passive == w.passive;
            lemma_active_added_keeps_views_ok(me, acap, pcap, views_of(pre), w, from, dropped);
        },
    }
}

/// An empty node is well-formed.
pub proof fn lemma_init_is_well_formed(n: HvNode)
    requires
        hv_init(n),
    ensures
        hv_inv(n),
{
}

} // verus!
