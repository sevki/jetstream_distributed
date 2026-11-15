//! A node's two views, executable and verified.
//!
//! [`crate::hyparview::model`] says what a node's views may become on each message.
//! This is the part that *holds* them: an [`HvTable`], two vectors of peers with no
//! repeats, and the operations that change them. [`HvTable::add_passive`] and
//! [`HvTable::add_active`] are the model's [`passive_added`] and [`active_added`];
//! the handlers built on them are the model's four steps.
//!
//! # Choices are arguments
//!
//! The paper leaves "drop a random peer" to the node. The model leaves it as an
//! existential. Here it is a `usize` the caller passes, and the table takes the peer
//! at that position modulo the view's length, so the verified code is deterministic
//! and the randomness is the service's. Any value is a correct choice, which is what
//! the existential in the model says.
//!
//! # What is verified, and what is not
//!
//! Verified: the views, and the messages a handler returns, against the model. The
//! vectors are searched linearly; that is a choice for the proof, and the views are
//! bounded by their capacities, which are small.
//!
//! Not: where the picks come from, the lock, and the delivery of the messages.
#![allow(unused_imports)]
#![allow(clippy::new_without_default, clippy::len_without_is_empty)]

use vstd::prelude::*;

use crate::hyparview::model::*;
use crate::hyparview::proofs::invariant::*;
use crate::id::Id;

verus! {

// --- facts about sequences of peers ---------------------------------------

/// Pushing a new peer keeps the sequence free of repeats and adds it to the set.
proof fn lemma_push(s: Seq<Id>, n: Id)
    requires
        s.no_duplicates(),
        !s.contains(n),
    ensures
        s.push(n).no_duplicates(),
        s.push(n).to_set() =~= s.to_set().insert(n),
{
    assert(s.push(n).no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < s.push(n).len() && 0 <= j < s.push(n).len() && i != j
            implies s.push(n)[i] != s.push(n)[j] by {
            if i < s.len() && j < s.len() {
            } else if i < s.len() {
                assert(s.contains(s[i]));
            } else if j < s.len() {
                assert(s.contains(s[j]));
            }
        }
    }
    assert forall|a: Id| s.push(n).to_set().contains(a) <==> s.to_set().insert(n).contains(a) by {
        assert(s.push(n).to_set().contains(a) <==> s.push(n).contains(a));
        assert(s.to_set().contains(a) <==> s.contains(a));
        if a == n {
            assert(s.push(n)[s.len() as int] == n);
        } else if s.contains(a) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == a;
            assert(s.push(n)[i] == a);
        }
    }
}

/// Removing the peer at position `i` keeps the sequence free of repeats and takes
/// exactly that peer out of the set.
proof fn lemma_remove_at(s: Seq<Id>, i: int)
    requires
        s.no_duplicates(),
        0 <= i < s.len(),
    ensures
        s.remove(i).no_duplicates(),
        s.remove(i).to_set() =~= s.to_set().remove(s[i]),
{
    let t = s.remove(i);
    assert(t.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && a != b
            implies t[a] != t[b] by {
            let sa = if a < i { a } else { a + 1 };
            let sb = if b < i { b } else { b + 1 };
            assert(t[a] == s[sa]);
            assert(t[b] == s[sb]);
            assert(sa != sb);
        }
    }
    assert forall|a: Id| #[trigger] t.to_set().contains(a) <==> s.to_set().remove(s[i]).contains(a) by {
        assert(t.to_set().contains(a) <==> t.contains(a));
        assert(s.to_set().contains(a) <==> s.contains(a));
        if t.contains(a) {
            let k = choose|k: int| 0 <= k < t.len() && t[k] == a;
            let sk = if k < i { k } else { k + 1 };
            assert(s[sk] == a);
            assert(sk != i);
        }
        if s.contains(a) && a != s[i] {
            let k = choose|k: int| 0 <= k < s.len() && s[k] == a;
            assert(k != i);
            let tk = if k < i { k } else { k - 1 };
            assert(t[tk] == a);
        }
    }
}

/// Replacing the peer at `i` with one not already present swaps them in the set.
proof fn lemma_replace_at(s: Seq<Id>, i: int, n: Id)
    requires
        s.no_duplicates(),
        0 <= i < s.len(),
        !s.contains(n),
    ensures
        s.update(i, n).no_duplicates(),
        s.update(i, n).to_set() =~= s.to_set().remove(s[i]).insert(n),
{
    let t = s.update(i, n);
    assert(t.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && a != b
            implies t[a] != t[b] by {
            if a == i {
                assert(s.contains(s[b]));
            } else if b == i {
                assert(s.contains(s[a]));
            }
        }
    }
    assert forall|a: Id| #[trigger] t.to_set().contains(a) <==> s.to_set().remove(s[i]).insert(n).contains(a) by {
        assert(t.to_set().contains(a) <==> t.contains(a));
        assert(s.to_set().contains(a) <==> s.contains(a));
        if t.contains(a) && a != n {
            let k = choose|k: int| 0 <= k < t.len() && t[k] == a;
            assert(k != i);
            assert(s[k] == a);
        }
        if a == n {
            assert(t[i] == n);
        }
        if s.contains(a) && a != s[i] {
            let k = choose|k: int| 0 <= k < s.len() && s[k] == a;
            assert(k != i);
            assert(t[k] == a);
        }
    }
}

/// A sequence free of repeats has as many members as its set has.
proof fn lemma_len(s: Seq<Id>)
    requires
        s.no_duplicates(),
    ensures
        s.len() == s.to_set().len(),
{
    s.unique_seq_to_set();
}

/// **A handler that is a step of the model keeps the views well-formed**, whatever
/// the history it ran after and whatever it sent.
proof fn lemma_handler_keeps_views_ok(
    me: Id,
    p: ExecParams,
    v: Views,
    w: Views,
    sent_now: Set<HvMsg>,
    s: HvStep,
)
    requires
        forall|sent: Set<HvMsg>|
            #[trigger] hv_step(
                node_of(me, p, v, sent),
                node_of(me, p, w, sent.union(sent_now)),
                s,
            ),
    ensures
        forall|sent: Set<HvMsg>|
            #[trigger] hv_inv(node_of(me, p, v, sent)) ==> hv_inv(
                node_of(me, p, w, sent.union(sent_now)),
            ),
{
    assert forall|sent: Set<HvMsg>| #[trigger] hv_inv(node_of(me, p, v, sent)) implies hv_inv(
        node_of(me, p, w, sent.union(sent_now)),
    ) by {
        theorem_every_step_keeps_the_views_well_formed(
            node_of(me, p, v, sent),
            node_of(me, p, w, sent.union(sent_now)),
            s,
        );
    }
}

// --- the table ------------------------------------------------------------

/// Where `n` is in `v`, if it is.
fn find(v: &[Id], n: Id) -> (found: Option<usize>)
    ensures
        match found {
            Some(i) => i < v@.len() && v@[i as int] == n,
            None => !v@.contains(n),
        },
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            forall|k: int| 0 <= k < i ==> v@[k] != n,
        decreases v@.len() - i,
    {
        if v[i] == n {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// A node's active and passive views.
pub struct HvTable {
    /// Private: a table built or edited from outside could hold a peer twice, and
    /// every method here assumes it does not.
    active: Vec<Id>,
    passive: Vec<Id>,
}

impl HvTable {
    /// Neither view holds a peer twice.
    pub closed spec fn well_formed(&self) -> bool {
        &&& self.active@.no_duplicates()
        &&& self.passive@.no_duplicates()
    }

    /// The model's views this table stands for.
    pub closed spec fn views(&self) -> Views {
        Views { active: self.active@.to_set(), passive: self.passive@.to_set() }
    }

    /// No peers.
    pub fn new() -> (t: HvTable)
        ensures
            t.well_formed(),
            t.views() == (Views { active: Set::<Id>::empty(), passive: Set::<Id>::empty() }),
    {
        let t = HvTable { active: Vec::new(), passive: Vec::new() };
        assert(t.active@.to_set() =~= Set::<Id>::empty());
        assert(t.passive@.to_set() =~= Set::<Id>::empty());
        t
    }

    /// Is `n` an active peer?
    pub fn in_active(&self, n: Id) -> (r: bool)
        ensures
            r == self.views().active.contains(n),
    {
        find(self.active.as_slice(), n).is_some()
    }

    /// Is `n` in the passive view?
    pub fn in_passive(&self, n: Id) -> (r: bool)
        ensures
            r == self.views().passive.contains(n),
    {
        find(self.passive.as_slice(), n).is_some()
    }

    /// The active peers, in the order held.
    pub fn active_peers(&self) -> (peers: Vec<Id>)
        requires
            self.well_formed(),
        ensures
            peers@.to_set() == self.views().active,
            peers@.no_duplicates(),
    {
        self.active.clone()
    }

    /// The passive peers, in the order held.
    pub fn passive_peers(&self) -> (peers: Vec<Id>)
        requires
            self.well_formed(),
        ensures
            peers@.to_set() == self.views().passive,
            peers@.no_duplicates(),
    {
        self.passive.clone()
    }

    /// Take `n` out of the passive view if it is there.
    fn remove_passive(&mut self, n: Id)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).active@ == old(self).active@,
            final(self).views().active == old(self).views().active,
            final(self).views().passive == old(self).views().passive.remove(n),
    {
        if let Some(i) = find(self.passive.as_slice(), n) {
            proof {
                lemma_remove_at(self.passive@, i as int);
            }
            self.passive.remove(i);
        } else {
            assert(self.passive@.to_set().remove(n) =~= self.passive@.to_set());
        }
    }

    /// The model's [`passive_added`]: `n` goes into the passive view, evicting the
    /// entry at `pick` (modulo the view's length) if it is full.
    pub fn add_passive(&mut self, me: Id, pcap: usize, n: Id, pick: usize)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            passive_added(me, pcap as nat, old(self).views(), final(self).views(), n),
    {
        let ghost v = self.views();
        if n == me || self.in_active(n) || self.in_passive(n) || pcap == 0 {
            assert(self.views() == v);
            return ;
        }
        if self.passive.len() < pcap {
            proof {
                lemma_push(self.passive@, n);
                lemma_len(self.passive@);
            }
            self.passive.push(n);
            assert(self.views().active == v.active);
            assert(self.views().passive == v.passive.insert(n));
            assert(self.views() == (Views { active: v.active, passive: v.passive.insert(n) }));
            assert(v.passive.len() < pcap as nat);
        } else {
            let i = pick % self.passive.len();
            proof {
                lemma_replace_at(self.passive@, i as int, n);
                lemma_len(self.passive@);
            }
            let ghost e = self.passive@[i as int];
            assert(v.passive.contains(e));
            self.passive.set(i, n);
            assert(self.views().active == v.active);
            assert(self.views().passive == v.passive.remove(e).insert(n));
            assert(self.views() == (Views { active: v.active, passive: v.passive.remove(e).insert(n) }));
            assert(!(v.passive.len() < pcap as nat));
        }
    }

    /// The model's [`active_added`]: `n` joins the active view. If the view is
    /// full, the peer at `pick_victim` (modulo its length) is demoted to the
    /// passive view, evicting the entry at `pick_evict` if that is full too, and is
    /// returned so the caller can tell it to disconnect.
    pub fn add_active(
        &mut self,
        me: Id,
        acap: usize,
        pcap: usize,
        n: Id,
        pick_victim: usize,
        pick_evict: usize,
    ) -> (dropped: Option<Id>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            active_added(
                me,
                acap as nat,
                pcap as nat,
                old(self).views(),
                final(self).views(),
                n,
                dropped,
            ),
    {
        let ghost v = self.views();
        if n == me || self.in_active(n) || acap == 0 {
            assert(self.views() == v);
            return None;
        }
        if self.active.len() < acap {
            self.remove_passive(n);
            proof {
                lemma_len(self.active@);
                lemma_push(self.active@, n);
            }
            assert(v.active.len() == self.active@.len());
            assert(v.active.len() < acap as nat);
            self.active.push(n);
            assert(self.views().active == v.active.insert(n));
            assert(self.views().passive == v.passive.remove(n));
            assert(self.views() == (Views { active: v.active.insert(n), passive: v.passive.remove(n) }));
            return None;
        }
        proof {
            lemma_len(self.active@);
        }
        let idx = pick_victim % self.active.len();
        let victim = self.active[idx];
        self.remove_passive(n);
        proof {
            lemma_remove_at(self.active@, idx as int);
        }
        self.active.remove(idx);
        let ghost v1 = self.views();
        assert(v1 == (Views { active: v.active.remove(victim), passive: v.passive.remove(n) }));
        self.add_passive(me, pcap, victim, pick_evict);
        let ghost mid = self.views();
        proof {
            assert(!self.active@.contains(n));
            lemma_push(self.active@, n);
        }
        self.active.push(n);
        assert(self.views().active == mid.active.insert(n));
        assert(self.views().passive == mid.passive);
        assert(v.active.contains(victim));
        assert(self.views() == (Views { active: mid.active.insert(n), passive: mid.passive }));
        Some(victim)
    }
}

// --- messages and parameters, at the machine ------------------------------

/// The protocol's parameters, at the machine.
#[derive(Clone, Copy)]
pub struct ExecParams {
    pub active_cap: usize,
    pub passive_cap: usize,
    pub arwl: u64,
    pub prwl: u64,
}

impl ExecParams {
    /// The model's parameters this stands for.
    pub open spec fn view(self) -> HvParams {
        HvParams {
            active_cap: self.active_cap as nat,
            passive_cap: self.passive_cap as nat,
            arwl: self.arwl as nat,
            prwl: self.prwl as nat,
        }
    }
}

/// The choices the paper leaves to a node, as arguments: which active peer to
/// demote when the view is full, which passive entry to evict when that is full,
/// and which active peer to pass a walk to. Each is taken modulo the number of
/// candidates, so any value is a correct choice, and the caller makes them random.
#[derive(Clone, Copy)]
pub struct Picks {
    pub victim: usize,
    pub evict: usize,
    pub next: usize,
}

/// A message to send, at the machine.
#[derive(Clone, Copy)]
pub enum ExecMsg {
    ForwardJoin { to: Id, new: Id, ttl: u64 },
    Disconnect { to: Id },
    Neighbor { to: Id },
}

impl ExecMsg {
    /// The model's message this stands for.
    pub open spec fn view(self) -> HvMsg {
        match self {
            ExecMsg::ForwardJoin { to, new, ttl } => HvMsg::ForwardJoin { to, new, ttl: ttl as nat },
            ExecMsg::Disconnect { to } => HvMsg::Disconnect { to },
            ExecMsg::Neighbor { to } => HvMsg::Neighbor { to },
        }
    }
}

/// The set of model messages a sequence of messages to send stands for.
pub open spec fn outset(out: Seq<ExecMsg>) -> Set<HvMsg> {
    out.map_values(|m: ExecMsg| m.view()).to_set()
}

/// A model message is in `outset(out)` exactly when some entry of `out` stands for it.
proof fn lemma_outset_contains(out: Seq<ExecMsg>, m: HvMsg)
    ensures
        outset(out).contains(m) <==> exists|i: int| 0 <= i < out.len() && #[trigger] out[i].view() == m,
{
    let mapped = out.map_values(|x: ExecMsg| x.view());
    assert(outset(out).contains(m) <==> mapped.contains(m));
    if mapped.contains(m) {
        let i = choose|i: int| 0 <= i < mapped.len() && mapped[i] == m;
        assert(mapped[i] == out[i].view());
    }
    if exists|i: int| 0 <= i < out.len() && #[trigger] out[i].view() == m {
        let i = choose|i: int| 0 <= i < out.len() && #[trigger] out[i].view() == m;
        assert(mapped[i] == m);
    }
}

/// Sending one more message adds exactly that message.
proof fn lemma_outset_push(out: Seq<ExecMsg>, x: ExecMsg, m: HvMsg)
    ensures
        outset(out.push(x)).contains(m) <==> outset(out).contains(m) || m == x.view(),
{
    lemma_outset_contains(out.push(x), m);
    lemma_outset_contains(out, m);
    if outset(out.push(x)).contains(m) {
        let i = choose|i: int| 0 <= i < out.push(x).len() && #[trigger] out.push(x)[i].view() == m;
        if i < out.len() {
            assert(out[i].view() == m);
        } else {
            assert(m == x.view());
        }
    }
    if outset(out).contains(m) {
        let i = choose|i: int| 0 <= i < out.len() && #[trigger] out[i].view() == m;
        assert(out.push(x)[i].view() == m);
    }
    if m == x.view() {
        assert(out.push(x)[out.len() as int].view() == m);
    }
}

/// Nothing sent is nothing in the set.
proof fn lemma_outset_empty(m: HvMsg)
    ensures
        !outset(Seq::<ExecMsg>::empty()).contains(m),
{
    lemma_outset_contains(Seq::<ExecMsg>::empty(), m);
}

/// The node, as the model sees it, with these views and this history.
pub open spec fn node_of(me: Id, p: ExecParams, v: Views, sent: Set<HvMsg>) -> HvNode {
    HvNode { me, params: p.view(), active: v.active, passive: v.passive, sent }
}

/// Send a `ForwardJoin` of `new` with `ttl` to every peer in `peers` but `new`.
fn forwards(peers: &[Id], new: Id, ttl: u64, out: &mut Vec<ExecMsg>)
    ensures
        forall|m: HvMsg|
            #[trigger] outset(final(out)@).contains(m) <==> outset(old(out)@).contains(m)
                || is_forward(m, peers@.to_set(), new, ttl as nat),
{
    let mut i: usize = 0;
    while i < peers.len()
        invariant
            i <= peers@.len(),
            forall|m: HvMsg|
                #[trigger] outset(out@).contains(m) <==> outset(old(out)@).contains(m)
                    || (exists|k: int|
                    0 <= k < i && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat)),
        decreases peers@.len() - i,
    {
        let n = peers[i];
        if n != new {
            let ghost before = out@;
            out.push(ExecMsg::ForwardJoin { to: n, new, ttl });
            assert forall|m: HvMsg|
                #[trigger] outset(out@).contains(m) <==> outset(old(out)@).contains(m)
                    || (exists|k: int|
                    0 <= k < i + 1 && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat)) by {
                lemma_outset_push(before, ExecMsg::ForwardJoin { to: n, new, ttl }, m);
                if m == (ExecMsg::ForwardJoin { to: n, new, ttl }).view() {
                    assert(is_forward(m, set![peers@[i as int]], new, ttl as nat));
                }
                if exists|k: int| 0 <= k < i + 1 && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat) {
                    let k = choose|k: int|
                        0 <= k < i + 1 && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat);
                    if k == i {
                        assert(m == (ExecMsg::ForwardJoin { to: n, new, ttl }).view());
                    }
                }
            }
        } else {
            assert forall|m: HvMsg|
                #[trigger] outset(out@).contains(m) <==> outset(old(out)@).contains(m)
                    || (exists|k: int|
                    0 <= k < i + 1 && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat)) by {
                if exists|k: int| 0 <= k < i + 1 && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat) {
                    let k = choose|k: int|
                        0 <= k < i + 1 && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat);
                    if k == i {
                        assert(false);
                    }
                }
            }
        }
        i += 1;
    }
    assert forall|m: HvMsg|
        #[trigger] outset(out@).contains(m) <==> outset(old(out)@).contains(m)
            || is_forward(m, peers@.to_set(), new, ttl as nat) by {
        if is_forward(m, peers@.to_set(), new, ttl as nat) {
            match m {
                HvMsg::ForwardJoin { to, new: _, ttl: _ } => {
                    let k = choose|k: int| 0 <= k < peers@.len() && peers@[k] == to;
                    assert(is_forward(m, set![peers@[k]], new, ttl as nat));
                },
                _ => {},
            }
        }
        if exists|k: int| 0 <= k < peers@.len() && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat) {
            let k = choose|k: int|
                0 <= k < peers@.len() && #[trigger] is_forward(m, set![peers@[k]], new, ttl as nat);
            assert(peers@.to_set().contains(peers@[k]));
        }
    }
}

impl HvTable {
    /// **A newcomer contacts this node**: the model's [`hv_join`].
    ///
    /// Returns the messages to send. For any history of earlier messages, the
    /// table's change together with these is a `Join` step of the model.
    pub fn join(
        &mut self,
        me: Id,
        p: ExecParams,
        new: Id,
        picks: Picks,
    ) -> (out: Vec<ExecMsg>)
        requires
            old(self).well_formed(),
            new != me,
        ensures
            final(self).well_formed(),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, old(self).views(), sent),
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                    HvStep::Join { new },
                ),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_inv(node_of(me, p, old(self).views(), sent)) ==> hv_inv(
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                ),
    {
        let ghost v = self.views();
        let dropped = self.add_active(me, p.active_cap, p.passive_cap, new, picks.victim, picks.evict);
        let peers = self.active_peers();
        let mut out: Vec<ExecMsg> = Vec::new();
        forwards(peers.as_slice(), new, p.arwl, &mut out);
        let ghost fwd = out@;
        if let Some(x) = dropped {
            out.push(ExecMsg::Disconnect { to: x });
        }
        let ghost w = self.views();
        proof {
            assert forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, v, sent),
                    node_of(me, p, w, sent.union(outset(out@))),
                    HvStep::Join { new },
                ) by {
                let pre = node_of(me, p, v, sent);
                let post = node_of(me, p, w, sent.union(outset(out@)));
                assert(active_added(me, p.active_cap as nat, p.passive_cap as nat, views_of(pre), w, new, dropped));
                assert forall|m: HvMsg| #[trigger] post.sent.contains(m) <==> pre.sent.contains(m)
                    || is_forward(m, w.active, new, pre.params.arwl) || is_disconnect_of(m, dropped) by {
                    lemma_outset_empty(m);
                    if let Some(x) = dropped {
                        lemma_outset_push(fwd, ExecMsg::Disconnect { to: x }, m);
                    }
                }
                assert(new != pre.me);
                assert(same_node(pre, post));
                assert(post.active == w.active);
                assert(post.passive == w.passive);
                assert(forall|m: HvMsg|
                    #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || is_forward(
                        m,
                        w.active,
                        new,
                        pre.params.arwl,
                    ) || is_disconnect_of(m, dropped));
                assert(active_added(
                    pre.me,
                    pre.params.active_cap,
                    pre.params.passive_cap,
                    views_of(pre),
                    w,
                    new,
                    dropped,
                ));
                assert(hv_join(pre, post, new));
            }
        }
        proof {
            lemma_handler_keeps_views_ok(me, p, v, w, outset(out@), HvStep::Join { new });
        }
        out
    }

    /// **A neighbour asks for the link**: the model's [`hv_neighbor`].
    pub fn neighbor(
        &mut self,
        me: Id,
        p: ExecParams,
        from: Id,
        picks: Picks,
    ) -> (out: Vec<ExecMsg>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, old(self).views(), sent),
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                    HvStep::Neighbor { from },
                ),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_inv(node_of(me, p, old(self).views(), sent)) ==> hv_inv(
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                ),
    {
        let ghost v = self.views();
        let dropped = self.add_active(me, p.active_cap, p.passive_cap, from, picks.victim, picks.evict);
        let mut out: Vec<ExecMsg> = Vec::new();
        if let Some(x) = dropped {
            out.push(ExecMsg::Disconnect { to: x });
        }
        let ghost w = self.views();
        proof {
            assert forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, v, sent),
                    node_of(me, p, w, sent.union(outset(out@))),
                    HvStep::Neighbor { from },
                ) by {
                let pre = node_of(me, p, v, sent);
                let post = node_of(me, p, w, sent.union(outset(out@)));
                assert(active_added(me, p.active_cap as nat, p.passive_cap as nat, views_of(pre), w, from, dropped));
                assert forall|m: HvMsg| #[trigger] post.sent.contains(m) <==> pre.sent.contains(m)
                    || is_disconnect_of(m, dropped) by {
                    lemma_outset_empty(m);
                    if let Some(x) = dropped {
                        lemma_outset_push(Seq::<ExecMsg>::empty(), ExecMsg::Disconnect { to: x }, m);
                    }
                }
                assert(same_node(pre, post));
                assert(post.active == w.active);
                assert(post.passive == w.passive);
                assert(forall|m: HvMsg|
                    #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || is_disconnect_of(
                        m,
                        dropped,
                    ));
                assert(active_added(
                    pre.me,
                    pre.params.active_cap,
                    pre.params.passive_cap,
                    views_of(pre),
                    w,
                    from,
                    dropped,
                ));
                assert(hv_neighbor(pre, post, from));
            }
        }
        proof {
            lemma_handler_keeps_views_ok(me, p, v, w, outset(out@), HvStep::Neighbor { from });
        }
        out
    }

    /// **A peer drops the link**: the model's [`hv_disconnect`]. Sends nothing.
    pub fn disconnect(&mut self, me: Id, p: ExecParams, peer: Id, picks: Picks) -> (out: Vec<ExecMsg>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, old(self).views(), sent),
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                    HvStep::Disconnect { peer },
                ),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_inv(node_of(me, p, old(self).views(), sent)) ==> hv_inv(
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                ),
    {
        let ghost v = self.views();
        if let Some(i) = find(self.active.as_slice(), peer) {
            proof {
                lemma_remove_at(self.active@, i as int);
            }
            self.active.remove(i);
            assert(self.views() == (Views { active: v.active.remove(peer), passive: v.passive }));
            self.add_passive(me, p.passive_cap, peer, picks.evict);
        } else {
            assert(self.views() == v);
        }
        let out: Vec<ExecMsg> = Vec::new();
        let ghost w = self.views();
        proof {
            assert forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, v, sent),
                    node_of(me, p, w, sent.union(outset(out@))),
                    HvStep::Disconnect { peer },
                ) by {
                assert forall|m: HvMsg| !outset(out@).contains(m) by {
                    lemma_outset_empty(m);
                }
                assert(sent.union(outset(out@)) =~= sent);
                if v.active.contains(peer) {
                    assert(passive_added(
                        me,
                        p.passive_cap as nat,
                        Views { active: v.active.remove(peer), passive: v.passive },
                        w,
                        peer,
                    ));
                } else {
                    assert(w == v);
                }
                let pre = node_of(me, p, v, sent);
                let post = node_of(me, p, w, sent.union(outset(out@)));
                assert(same_node(pre, post));
                assert(post.sent == pre.sent);
                if pre.active.contains(peer) {
                    assert(passive_added(
                        pre.me,
                        pre.params.passive_cap,
                        Views { active: pre.active.remove(peer), passive: pre.passive },
                        w,
                        peer,
                    ));
                    assert(post.active == w.active);
                    assert(post.passive == w.passive);
                } else {
                    assert(post.active == pre.active);
                    assert(post.passive == pre.passive);
                }
                assert(hv_disconnect(pre, post, peer));
            }
        }
        proof {
            lemma_handler_keeps_views_ok(me, p, v, w, outset(out@), HvStep::Disconnect { peer });
        }
        out
    }
}

impl HvTable {
    /// **A walk of a join arrives from `sender`**: the model's
    /// [`hv_forward_join`].
    ///
    /// A walk from a node that is not an active peer, or one that has come back to
    /// `new` itself, changes nothing and sends nothing.
    ///
    /// At the end of the walk (no hops left, or `sender` is the only active peer)
    /// `new` becomes an active peer and is asked to reciprocate. Before the end the
    /// walk goes on to another active peer, picked by `picks.next` among the ones
    /// that are not `sender`, and `new` is noted in the passive view when the walk
    /// has reached `p.prwl`.
    pub fn forward_join(
        &mut self,
        me: Id,
        p: ExecParams,
        new: Id,
        ttl: u64,
        sender: Id,
        picks: Picks,
    ) -> (out: Vec<ExecMsg>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, old(self).views(), sent),
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                    HvStep::ForwardJoin { new, ttl: ttl as nat, sender },
                ),
            forall|sent: Set<HvMsg>|
                #[trigger] hv_inv(node_of(me, p, old(self).views(), sent)) ==> hv_inv(
                    node_of(me, p, final(self).views(), sent.union(outset(out@))),
                ),
    {
        let ghost v = self.views();
        let mut out: Vec<ExecMsg> = Vec::new();
        proof {
            lemma_len(self.active@);
        }
        if new == me || !self.in_active(sender) {
            proof {
                assert forall|sent: Set<HvMsg>|
                    #[trigger] hv_step(
                        node_of(me, p, v, sent),
                        node_of(me, p, v, sent.union(outset(out@))),
                        HvStep::ForwardJoin { new, ttl: ttl as nat, sender },
                    ) by {
                    assert forall|m: HvMsg| !outset(out@).contains(m) by {
                        lemma_outset_empty(m);
                    }
                    assert(sent.union(outset(out@)) =~= sent);
                    let pre = node_of(me, p, v, sent);
                    let post = node_of(me, p, v, sent.union(outset(out@)));
                    assert(same_node(pre, post));
                    assert(hv_forward_join(pre, post, new, ttl as nat, sender));
                }
            }
            proof {
                lemma_handler_keeps_views_ok(me, p, v, v, outset(out@), HvStep::ForwardJoin { new, ttl: ttl as nat, sender });
            }
            return out;
        }
        if ttl == 0 || self.active.len() == 1 {
            let dropped = self.add_active(
                me,
                p.active_cap,
                p.passive_cap,
                new,
                picks.victim,
                picks.evict,
            );
            out.push(ExecMsg::Neighbor { to: new });
            let ghost after_neighbor = out@;
            if let Some(x) = dropped {
                out.push(ExecMsg::Disconnect { to: x });
            }
            let ghost w = self.views();
            proof {
                assert forall|sent: Set<HvMsg>|
                    #[trigger] hv_step(
                        node_of(me, p, v, sent),
                        node_of(me, p, w, sent.union(outset(out@))),
                        HvStep::ForwardJoin { new, ttl: ttl as nat, sender },
                    ) by {
                    let pre = node_of(me, p, v, sent);
                    let post = node_of(me, p, w, sent.union(outset(out@)));
                    assert(v.active.remove(sender).len() == 0 || ttl == 0);
                    assert(ttl as nat == 0 || pre.active.remove(sender).len() == 0);
                    assert forall|m: HvMsg|
                        #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || is_neighbor_to(
                            m,
                            new,
                        ) || is_disconnect_of(m, dropped) by {
                        lemma_outset_empty(m);
                        lemma_outset_push(Seq::<ExecMsg>::empty(), ExecMsg::Neighbor { to: new }, m);
                        if let Some(x) = dropped {
                            lemma_outset_push(after_neighbor, ExecMsg::Disconnect { to: x }, m);
                        }
                    }
                    assert(same_node(pre, post));
                    assert(active_added(
                        pre.me,
                        pre.params.active_cap,
                        pre.params.passive_cap,
                        views_of(pre),
                        w,
                        new,
                        dropped,
                    ));
                    assert(post.active == w.active);
                    assert(post.passive == w.passive);
                    assert(hv_forward_join(pre, post, new, ttl as nat, sender));
                }
            }
            proof {
                lemma_handler_keeps_views_ok(me, p, v, w, outset(out@), HvStep::ForwardJoin { new, ttl: ttl as nat, sender });
            }
            return out;
        }
        let i0 = match find(self.active.as_slice(), sender) {
            Some(i) => i,
            None => {
                assert(false);
                0
            },
        };
        let len = self.active.len();
        let mut idx = picks.next % (len - 1);
        if idx >= i0 {
            idx += 1;
        }
        let next = self.active[idx];
        assert(next != sender) by {
            assert(self.active@[idx as int] != self.active@[i0 as int]);
        }
        assert(v.active.remove(sender).contains(next));
        if ttl == p.prwl {
            self.add_passive(me, p.passive_cap, new, picks.evict);
        }
        out.push(ExecMsg::ForwardJoin { to: next, new, ttl: ttl - 1 });
        let ghost w = self.views();
        proof {
            assert forall|sent: Set<HvMsg>|
                #[trigger] hv_step(
                    node_of(me, p, v, sent),
                    node_of(me, p, w, sent.union(outset(out@))),
                    HvStep::ForwardJoin { new, ttl: ttl as nat, sender },
                ) by {
                let pre = node_of(me, p, v, sent);
                let post = node_of(me, p, w, sent.union(outset(out@)));
                assert(!(ttl as nat == 0 || pre.active.remove(sender).len() == 0));
                assert forall|m: HvMsg|
                    #[trigger] post.sent.contains(m) <==> pre.sent.contains(m) || m
                        == (HvMsg::ForwardJoin { to: next, new: new, ttl: (ttl as nat - 1) as nat }) by {
                    lemma_outset_push(
                        Seq::<ExecMsg>::empty(),
                        ExecMsg::ForwardJoin { to: next, new, ttl: (ttl - 1) as u64 },
                        m,
                    );
                    lemma_outset_empty(m);
                }
                assert(same_node(pre, post));
                assert(pre.active.remove(sender).contains(next));
                if ttl as nat == pre.params.prwl {
                    assert(passive_added(pre.me, pre.params.passive_cap, views_of(pre), w, new));
                    assert(post.active == w.active);
                    assert(post.passive == w.passive);
                } else {
                    assert(w == views_of(pre));
                    assert(post.active == pre.active);
                    assert(post.passive == pre.passive);
                }
                assert(hv_forward_join(pre, post, new, ttl as nat, sender));
            }
        }
        proof {
            lemma_handler_keeps_views_ok(me, p, v, w, outset(out@), HvStep::ForwardJoin { new, ttl: ttl as nat, sender });
        }
        out
    }
}

} // verus!
