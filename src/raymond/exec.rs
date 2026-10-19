//! The routing record, executable and verified.
//!
//! [`crate::raymond::steps`] decides, from one node's scalars, whether a routing
//! step fires. This is the thing those scalars are read from and written to: a
//! [`RayTable`], the whole routing record of a cluster — every node's holder
//! pointer, queue, `asked` and `using` flags, the set of requests sent, and where
//! the privilege is — with one method per model step.
//!
//! # The contract is the model's
//!
//! A [`RayTable`] has a view, `RayTable::view`, that is a model
//! [`Raymond`]. Each method's postcondition says
//! what the view becomes — the model's `*_post` — and that the model's step is
//! enabled to it; a refusal says the view did not change and that the model's step
//! was **not** enabled, to any state. So [`crate::raymond::proofs::refinement`]'s
//! per-node theorems apply to the live table, not only to a hypothesis about it,
//! and what the service used to assert in a comment is checked.
//!
//! # What is verified
//!
//! * `request_cs`, `make_request`, `receive_request`, `assign_privilege`,
//!   `enter_cs` and `exit_cs` are the model's steps; `seize` and `reconcile` are
//!   the composed machine's two privilege-moving steps on the routing side.
//! * A node that is not on the roster is refused, as every model step begins
//!   with `pre.nodes.contains(..)`.
//!
//! # What is not
//!
//! The roster (which connection is which node), the lock, the audit log, and
//! who may call `seize` and `reconcile` — the composed coordinator checks the
//! token — are the service's. The table is searched linearly, because the
//! proof is easier that way and a roster is small.
#![allow(unused_imports)]
#![allow(
    clippy::new_without_default,
    clippy::len_without_is_empty,
    clippy::vec_init_then_push
)]

use std::collections::VecDeque;

use vstd::prelude::*;

use crate::ownership::model::NodeId;
use crate::raymond::model::*;
use crate::raymond::proofs::refinement::*;
use crate::raymond::steps::*;

verus! {

/// One node's routing entries.
pub struct RayEntry {
    /// Which node.
    pub id: u64,
    /// Where the node believes the privilege is, one hop.
    pub holder: u64,
    /// Requests waiting at the node, front first.
    pub queue: VecDeque<u64>,
    /// A request towards `holder` is outstanding.
    pub asked: bool,
    /// The node is inside its critical section.
    pub using: bool,
}

/// The routing record of a whole cluster.
pub struct RayTable {
    /// One entry per node.
    pub entries: Vec<RayEntry>,
    /// Every request ever sent, `(originator, destination)`. Never shrinks.
    pub requests: Vec<(u64, u64)>,
    /// Where the privilege actually is.
    pub privilege: u64,
}

/// Where `n` is among `ids`, if it is.
pub open spec fn index_in(ids: Seq<u64>, n: nat) -> int {
    choose|i: int| 0 <= i < ids.len() && ids[i] as nat == n
}

/// `n` is among `ids`.
pub open spec fn ids_has(ids: Seq<u64>, n: nat) -> bool {
    exists|i: int| 0 <= i < ids.len() && ids[i] as nat == n
}

/// The queue as the model sees it.
pub open spec fn queue_view(e: RayEntry) -> Seq<NodeId> {
    e.queue@.map_values(|x: u64| x as nat)
}

impl RayTable {
    /// The nodes, in entry order.
    pub open spec fn ids(&self) -> Seq<u64> {
        self.entries@.map_values(|e: RayEntry| e.id)
    }

    /// Each node has one entry, and the privilege is at a node.
    pub open spec fn well_formed(&self) -> bool {
        &&& forall|i: int, j: int|
            0 <= i < self.ids().len() && 0 <= j < self.ids().len() && self.ids()[i] == self.ids()[j]
                ==> i == j
        &&& ids_has(self.ids(), self.privilege as nat)
    }

    /// `n` is a node.
    pub open spec fn has_node(&self, n: nat) -> bool {
        ids_has(self.ids(), n)
    }

    /// The set of nodes.
    pub open spec fn node_set(&self) -> Set<NodeId> {
        self.ids().map_values(|x: u64| x as nat).to_set()
    }

    /// Node `n`'s entry. Meaningful when `n` is a node.
    pub open spec fn entry_of(&self, n: nat) -> RayEntry {
        self.entries@[index_in(self.ids(), n)]
    }

    /// `(a, b)` has been sent.
    pub open spec fn has_request(&self, a: nat, b: nat) -> bool {
        exists|k: int|
            0 <= k < self.requests@.len() && self.requests@[k].0 as nat == a
                && self.requests@[k].1 as nat == b
    }

    /// The set of requests sent.
    pub open spec fn request_set(&self) -> Set<(NodeId, NodeId)> {
        self.requests@.map_values(|p: (u64, u64)| (p.0 as nat, p.1 as nat)).to_set()
    }
}

impl View for RayTable {
    type V = Raymond;

    /// The model state this table stands for.
    open spec fn view(&self) -> Raymond {
        Raymond {
            nodes: self.node_set(),
            holder: Map::new(self.node_set(), |n: nat| self.entry_of(n).holder as nat),
            queue: Map::new(self.node_set(), |n: nat| queue_view(self.entry_of(n))),
            asked: Map::new(self.node_set(), |n: nat| self.entry_of(n).asked),
            using: Map::new(self.node_set(), |n: nat| self.entry_of(n).using),
            requests: self.request_set(),
            privilege: self.privilege as nat,
        }
    }
}

/// `r` with node `id`'s entries replaced by `e`'s.
pub open spec fn upd(r: Raymond, id: NodeId, e: RayEntry) -> Raymond {
    Raymond {
        nodes: r.nodes,
        holder: r.holder.insert(id, e.holder as nat),
        queue: r.queue.insert(id, queue_view(e)),
        asked: r.asked.insert(id, e.asked),
        using: r.using.insert(id, e.using),
        requests: r.requests,
        privilege: r.privilege,
    }
}

/// The node set is the nodes.
pub proof fn lemma_node_set(t: RayTable, n: nat)
    ensures
        t.node_set().contains(n) <==> t.has_node(n),
{
    let m = t.ids().map_values(|x: u64| x as nat);
    m.to_set_ensures();
    assert(m.to_set().contains(n) <==> m.contains(n));
    if t.has_node(n) {
        let i = choose|i: int| 0 <= i < t.ids().len() && t.ids()[i] as nat == n;
        assert(m[i] == n);
        assert(m.contains(n));
    }
    if m.contains(n) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == n;
        assert(t.ids()[i] as nat == n);
    }
}

/// The request set is the requests.
pub proof fn lemma_request_set(t: RayTable, a: nat, b: nat)
    ensures
        t.request_set().contains((a, b)) <==> t.has_request(a, b),
{
    let m = t.requests@.map_values(|p: (u64, u64)| (p.0 as nat, p.1 as nat));
    m.to_set_ensures();
    if t.has_request(a, b) {
        let k = choose|k: int|
            0 <= k < t.requests@.len() && t.requests@[k].0 as nat == a && t.requests@[k].1 as nat == b;
        assert(m[k] == (a, b));
        assert(m.contains((a, b)));
    }
    if m.contains((a, b)) {
        let k = choose|k: int| 0 <= k < m.len() && m[k] == (a, b);
        assert(t.requests@[k].0 as nat == a);
    }
}

/// **Replacing one node's entry changes the view by `upd`, and nothing else.**
pub proof fn lemma_update_entry(t0: RayTable, t1: RayTable, i: int)
    requires
        t0.well_formed(),
        0 <= i < t0.entries@.len(),
        t1.entries@.len() == t0.entries@.len(),
        t1.entries@[i].id == t0.entries@[i].id,
        forall|k: int| 0 <= k < t0.entries@.len() && k != i ==> t1.entries@[k] == t0.entries@[k],
        t1.requests@ == t0.requests@,
        t1.privilege == t0.privilege,
    ensures
        t1.well_formed(),
        t1.ids() == t0.ids(),
        t1@ == upd(t0@, t0.entries@[i].id as nat, t1.entries@[i]),
{
    assert(t1.ids() =~= t0.ids()) by {
        assert forall|k: int| 0 <= k < t0.ids().len() implies t1.ids()[k] == t0.ids()[k] by {
            assert(t1.ids()[k] == t1.entries@[k].id);
            assert(t0.ids()[k] == t0.entries@[k].id);
        }
    }
    let id = t0.entries@[i].id as nat;
    assert(t0.ids()[i] as nat == id);
    assert(t0.has_node(id));
    lemma_node_set(t0, id);
    assert(index_in(t0.ids(), id) == i) by {
        let j = index_in(t0.ids(), id);
        assert(0 <= j < t0.ids().len() && t0.ids()[j] as nat == id);
        assert(t0.ids()[j] == t0.ids()[i]);
    }
    let e = t1.entries@[i];
    let u = upd(t0@, id, e);
    assert(t1.node_set() == t0.node_set());
    assert(t0@.nodes.contains(id));
    // The node `n` names is `id` or some other entry, which did not change.
    assert forall|n: nat| t0.has_node(n) && n != id implies index_in(t0.ids(), n) != i by {
        let j = index_in(t0.ids(), n);
        assert(t0.ids()[j] as nat == n);
        if j == i {
            assert(t0.ids()[i] as nat == id);
        }
    }
    assert forall|n: nat| t0.node_set().contains(n) && n != id implies t1.entry_of(n)
        == t0.entry_of(n) by {
        lemma_node_set(t0, n);
        let j = index_in(t0.ids(), n);
        assert(j != i);
        assert(t1.entries@[j] == t0.entries@[j]);
    }
    assert(t0@.holder.dom() == t0.node_set());
    assert(t1@.holder =~= u.holder) by {
        assert(u.holder.dom() =~= t0.node_set().insert(id));
        assert(t0.node_set().insert(id) =~= t0.node_set());
    }
    assert(t1@.queue =~= u.queue) by {
        assert(u.queue.dom() =~= t0.node_set().insert(id));
        assert(t0.node_set().insert(id) =~= t0.node_set());
    }
    assert(t1@.asked =~= u.asked) by {
        assert(u.asked.dom() =~= t0.node_set().insert(id));
        assert(t0.node_set().insert(id) =~= t0.node_set());
    }
    assert(t1@.using =~= u.using) by {
        assert(u.using.dom() =~= t0.node_set().insert(id));
        assert(t0.node_set().insert(id) =~= t0.node_set());
    }
    assert(t1.request_set() == t0.request_set());
    assert(t1@ == u);
}

/// A found entry is the node's: its fields are the view's.
pub proof fn lemma_found(t: RayTable, i: int)
    requires
        t.well_formed(),
        0 <= i < t.entries@.len(),
    ensures
        t.has_node(t.entries@[i].id as nat),
        t@.nodes.contains(t.entries@[i].id as nat),
        t.entry_of(t.entries@[i].id as nat) == t.entries@[i],
        t@.holder[t.entries@[i].id as nat] == t.entries@[i].holder as nat,
        t@.queue[t.entries@[i].id as nat] == queue_view(t.entries@[i]),
        t@.asked[t.entries@[i].id as nat] == t.entries@[i].asked,
        t@.using[t.entries@[i].id as nat] == t.entries@[i].using,
{
    let id = t.entries@[i].id as nat;
    assert(t.ids()[i] as nat == id);
    assert(t.has_node(id));
    lemma_node_set(t, id);
    let j = index_in(t.ids(), id);
    assert(t.ids()[j] == t.ids()[i]);
    assert(j == i);
}

/// A node that is not found is not in the view.
pub proof fn lemma_absent(t: RayTable, id: u64)
    requires
        forall|k: int| 0 <= k < t.entries@.len() ==> t.entries@[k].id != id,
    ensures
        !t@.nodes.contains(id as nat),
{
    lemma_node_set(t, id as nat);
    if t.has_node(id as nat) {
        let k = choose|k: int| 0 <= k < t.ids().len() && t.ids()[k] as nat == id as nat;
        assert(t.entries@[k].id == id);
    }
}

/// **Sending a request adds it to the set sent, and nothing else changes.**
pub proof fn lemma_push_request(t0: RayTable, t1: RayTable, a: u64, b: u64)
    requires
        t0.well_formed(),
        t1.entries@ == t0.entries@,
        t1.requests@ == t0.requests@.push((a, b)),
        t1.privilege == t0.privilege,
    ensures
        t1.well_formed(),
        t1@ == (Raymond { requests: t0@.requests.insert((a as nat, b as nat)), ..t0@ }),
{
    assert(t1.ids() == t0.ids());
    assert(t1.node_set() == t0.node_set());
    let m0 = t0.requests@.map_values(|p: (u64, u64)| (p.0 as nat, p.1 as nat));
    let m1 = t1.requests@.map_values(|p: (u64, u64)| (p.0 as nat, p.1 as nat));
    assert(m1 =~= m0.push((a as nat, b as nat)));
    m0.to_set_ensures();
    m1.to_set_ensures();
    assert(t1.request_set() =~= t0.request_set().insert((a as nat, b as nat))) by {
        assert forall|p: (nat, nat)| t1.request_set().contains(p) == t0.request_set()
            .insert((a as nat, b as nat)).contains(p) by {
            let x = (a as nat, b as nat);
            assert(m1.to_set().contains(p) == m1.contains(p));
            assert(m0.to_set().contains(p) == m0.contains(p));
            assert(m1.len() == m0.len() + 1);
            if m1.contains(p) {
                let k = choose|k: int| 0 <= k < m1.len() && m1[k] == p;
                if k < m0.len() {
                    assert(m0[k] == p);
                    assert(m0.contains(p));
                } else {
                    assert(p == x);
                }
            }
            if m0.contains(p) {
                let k = choose|k: int| 0 <= k < m0.len() && m0[k] == p;
                assert(m1[k] == p);
                assert(m1.contains(p));
            }
            if p == x {
                assert(m1[m0.len() as int] == x);
                assert(m1.contains(p));
            }
        }
    }
    assert(t1@.holder =~= t0@.holder);
    assert(t1@.queue =~= t0@.queue);
    assert(t1@.asked =~= t0@.asked);
    assert(t1@.using =~= t0@.using);
}

impl RayTable {
    /// Where node `id` is, if it is.
    pub fn find(&self, id: u64) -> (found: Option<usize>)
        ensures
            match found {
                Some(i) => i < self.entries@.len() && self.entries@[i as int].id == id,
                None => forall|k: int| 0 <= k < self.entries@.len() ==> self.entries@[k].id != id,
            },
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries@.len(),
                forall|k: int| 0 <= k < i ==> self.entries@[k].id != id,
            decreases self.entries@.len() - i,
        {
            if self.entries[i].id == id {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// Whether `(a, b)` has been sent.
    pub fn sent(&self, a: u64, b: u64) -> (r: bool)
        ensures
            r == self.has_request(a as nat, b as nat),
    {
        let mut k: usize = 0;
        while k < self.requests.len()
            invariant
                k <= self.requests@.len(),
                forall|m: int| 0 <= m < k ==> self.requests@[m] != (a, b),
            decreases self.requests@.len() - k,
        {
            if self.requests[k].0 == a && self.requests[k].1 == b {
                return true;
            }
            k += 1;
        }
        false
    }

    /// `RequestCs`: node `me` asks for the privilege for itself.
    pub fn request_cs(&mut self, me: u64) -> (r: Result<(), RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(_) => {
                    &&& final(self)@ == request_cs_post(old(self)@, me as nat)
                    &&& ray_request_cs(old(self)@, final(self)@, me as nat)
                },
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond| !ray_request_cs(old(self)@, p, me as nat)
                },
            },
    {
        let ghost t0 = *self;
        let Some(i) = self.find(me) else {
            proof {
                lemma_absent(t0, me);
            }
            return Err(RayRefusal::NotANode);
        };
        proof {
            lemma_found(t0, i as int);
        }
        self.entries[i].queue.push_back(me);
        proof {
            lemma_update_entry(t0, *self, i as int);
            let r0 = t0@;
            let e = self.entries@[i as int];
            assert(queue_view(e) =~= queue_view(t0.entries@[i as int]).push(me as nat));
            assert(self@.queue =~= request_cs_post(r0, me as nat).queue) by {
                assert(r0.queue.insert(me as nat, queue_view(e)) =~= r0.queue.insert(
                    me as nat,
                    r0.queue[me as nat].push(me as nat),
                ));
            }
            assert(self@.holder =~= r0.holder.insert(me as nat, r0.holder[me as nat])) ;
            assert(self@.asked =~= r0.asked.insert(me as nat, r0.asked[me as nat]));
            assert(self@.using =~= r0.using.insert(me as nat, r0.using[me as nat]));
            assert(r0.holder.insert(me as nat, r0.holder[me as nat]) =~= r0.holder);
            assert(r0.asked.insert(me as nat, r0.asked[me as nat]) =~= r0.asked);
            assert(r0.using.insert(me as nat, r0.using[me as nat]) =~= r0.using);
            assert(self@ == request_cs_post(r0, me as nat));
            theorem_request_cs_post_is_the_model_step(r0, me as nat);
        }
        Ok(())
    }
}

/// Re-inserting what a map already holds changes nothing.
pub proof fn lemma_insert_same<K, V>(m: Map<K, V>, k: K)
    requires
        m.dom().contains(k),
    ensures
        m.insert(k, m[k]) =~= m,
{
}

/// The view's maps are total on its nodes.
pub proof fn lemma_view_total(t: RayTable)
    ensures
        ray_maps_total(t@),
{
    assert forall|n: NodeId| #[trigger] t@.nodes.contains(n) implies t@.holder.contains_key(n)
        && t@.queue.contains_key(n) && t@.asked.contains_key(n) && t@.using.contains_key(n) by {
        assert(t@.holder.dom() =~= t.node_set());
    }
}

/// **Moving the privilege changes the view's `privilege`, and nothing else.**
pub proof fn lemma_set_privilege(t0: RayTable, t1: RayTable, p: u64)
    requires
        t0.well_formed(),
        t1.entries@ == t0.entries@,
        t1.requests@ == t0.requests@,
        t1.privilege == p,
        t0.has_node(p as nat),
    ensures
        t1.well_formed(),
        t1@ == (Raymond { privilege: p as nat, ..t0@ }),
{
    assert(t1.ids() == t0.ids());
    assert(t1.node_set() == t0.node_set());
    assert(t1.request_set() == t0.request_set());
    assert(t1@.holder =~= t0@.holder);
    assert(t1@.queue =~= t0@.queue);
    assert(t1@.asked =~= t0@.asked);
    assert(t1@.using =~= t0@.using);
}

impl RayTable {
    /// A table of one node, `root`, which holds the privilege. **Construction is
    /// not a model step**: that the finished table is `ray_init` — every other
    /// node points somewhere, the pointers reach the root — is the service's
    /// check at start-up, not something proved here.
    pub fn new(root: u64) -> (t: RayTable)
        ensures
            t.well_formed(),
            t.privilege == root,
            t.entries@.len() == 1,
            t.requests@.len() == 0,
    {
        let mut entries = Vec::new();
        entries.push(RayEntry { id: root, holder: root, queue: VecDeque::new(), asked: false, using: false });
        let t = RayTable { entries, requests: Vec::new(), privilege: root };
        proof {
            assert(t.ids() =~= seq![root]);
            assert(t.has_node(root as nat)) by {
                assert(t.ids()[0] as nat == root as nat);
            }
        }
        t
    }

    /// Add node `id`, pointing at `holder`, with nothing queued. Refused if `id`
    /// is already a node. Construction, not a model step; see
    /// [`RayTable::new`].
    pub fn add_node(&mut self, id: u64, holder: u64) -> (added: bool)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).privilege == old(self).privilege,
            final(self).requests@ == old(self).requests@,
            added == !old(self).has_node(id as nat),
    {
        let ghost t0 = *self;
        if self.find(id).is_some() {
            proof {
                let k = choose|k: int| 0 <= k < t0.entries@.len() && t0.entries@[k].id == id;
                assert(t0.ids()[k] as nat == id as nat);
            }
            return false;
        }
        self.entries.push(RayEntry { id, holder, queue: VecDeque::new(), asked: false, using: false });
        proof {
            let n = t0.entries@.len() as int;
            assert(self.ids() =~= t0.ids().push(id));
            assert forall|i: int, j: int|
                0 <= i < self.ids().len() && 0 <= j < self.ids().len() && self.ids()[i]
                    == self.ids()[j] implies i == j by {
                if i == n && j != n {
                    assert(t0.entries@[j].id != id);
                }
                if j == n && i != n {
                    assert(t0.entries@[i].id != id);
                }
            }
            assert(ids_has(self.ids(), self.privilege as nat)) by {
                let k = choose|k: int| 0 <= k < t0.ids().len() && t0.ids()[k] as nat == t0.privilege as nat;
                assert(self.ids()[k] as nat == self.privilege as nat);
            }
            assert(!t0.has_node(id as nat)) by {
                if t0.has_node(id as nat) {
                    let k = choose|k: int| 0 <= k < t0.ids().len() && t0.ids()[k] as nat == id as nat;
                    assert(t0.entries@[k].id == id);
                }
            }
        }
        true
    }

    /// `MakeRequest`: node `me` forwards a request one hop towards the privilege.
    /// Returns where it goes: the holder pointer, resolved now.
    pub fn make_request(&mut self, me: u64) -> (r: Result<u64, RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(dest) => {
                    &&& final(self)@ == make_request_post(old(self)@, me as nat)
                    &&& ray_make_request(old(self)@, final(self)@, me as nat)
                    &&& dest as nat == old(self)@.holder[me as nat]
                },
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond| !ray_make_request(old(self)@, p, me as nat)
                },
            },
    {
        let ghost t0 = *self;
        let Some(i) = self.find(me) else {
            proof {
                lemma_absent(t0, me);
            }
            return Err(RayRefusal::NotANode);
        };
        proof {
            lemma_found(t0, i as int);
            lemma_view_total(t0);
        }
        let queue_len = self.entries[i].queue.len() as u64;
        let holder = self.entries[i].holder;
        let asked = self.entries[i].asked;
        match make_request_step(me, holder, queue_len, asked) {
            Err(why) => {
                proof {
                    assert forall|p: Raymond| !ray_make_request(t0@, p, me as nat) by {
                        theorem_make_request_step_refuses_exactly_when_disabled(t0@, p, me as nat);
                    }
                }
                Err(why)
            },
            Ok(dest) => {
                self.entries[i].asked = true;
                let ghost t1 = *self;
                proof {
                    lemma_update_entry(t0, t1, i as int);
                }
                self.requests.push((me, dest));
                proof {
                    lemma_push_request(t1, *self, me, dest);
                    let r0 = t0@;
                    let n = me as nat;
                    lemma_insert_same(r0.holder, n);
                    lemma_insert_same(r0.using, n);
                    assert(queue_view(t1.entries@[i as int]) =~= r0.queue[n]);
                    lemma_insert_same(r0.queue, n);
                    assert(t1@ == (Raymond { asked: r0.asked.insert(n, true), ..r0 }));
                    assert(self@ == make_request_post(r0, n));
                    theorem_make_request_step_refines(r0, n);
                }
                Ok(dest)
            },
        }
    }

    /// `ReceiveRequest`: node `at` accepts a request from `from` that was sent.
    pub fn receive_request(&mut self, at: u64, from: u64) -> (r: Result<(), RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(_) => {
                    &&& final(self)@ == receive_request_post(old(self)@, at as nat, from as nat)
                    &&& ray_receive_request(old(self)@, final(self)@, at as nat, from as nat)
                },
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond| !ray_receive_request(old(self)@, p, at as nat, from as nat)
                },
            },
    {
        let ghost t0 = *self;
        let Some(i) = self.find(at) else {
            proof {
                lemma_absent(t0, at);
            }
            return Err(RayRefusal::NotANode);
        };
        let Some(_j) = self.find(from) else {
            proof {
                lemma_absent(t0, from);
            }
            return Err(RayRefusal::NotANode);
        };
        proof {
            lemma_found(t0, i as int);
            lemma_found(t0, _j as int);
            lemma_request_set(t0, from as nat, at as nat);
        }
        let was_sent = self.sent(from, at);
        match receive_request_step(was_sent) {
            Err(why) => {
                proof {
                    assert forall|p: Raymond| !ray_receive_request(t0@, p, at as nat, from as nat) by {
                        theorem_receive_request_step_refuses_exactly_when_disabled(
                            t0@,
                            p,
                            at as nat,
                            from as nat,
                        );
                    }
                }
                Err(why)
            },
            Ok(_) => {
                self.entries[i].queue.push_back(from);
                proof {
                    lemma_update_entry(t0, *self, i as int);
                    let r0 = t0@;
                    let n = at as nat;
                    lemma_insert_same(r0.holder, n);
                    lemma_insert_same(r0.asked, n);
                    lemma_insert_same(r0.using, n);
                    assert(queue_view(self.entries@[i as int]) =~= r0.queue[n].push(from as nat));
                    assert(self@ == receive_request_post(r0, n, from as nat));
                    theorem_receive_request_step_refines(r0, n, from as nat);
                }
                Ok(())
            },
        }
    }

    /// `EnterCs`: node `me`, at the head of its own queue and believing it holds
    /// the privilege, enters its critical section.
    pub fn enter_cs(&mut self, me: u64) -> (r: Result<(), RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(_) => {
                    &&& final(self)@ == enter_cs_post(old(self)@, me as nat)
                    &&& ray_enter_cs(old(self)@, final(self)@, me as nat)
                },
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond| !ray_enter_cs(old(self)@, p, me as nat)
                },
            },
    {
        let ghost t0 = *self;
        let Some(i) = self.find(me) else {
            proof {
                lemma_absent(t0, me);
            }
            return Err(RayRefusal::NotANode);
        };
        proof {
            lemma_found(t0, i as int);
            lemma_view_total(t0);
        }
        let queue_len = self.entries[i].queue.len() as u64;
        let head = if queue_len > 0 {
            self.entries[i].queue[0]
        } else {
            0
        };
        let holder = self.entries[i].holder;
        let using = self.entries[i].using;
        match enter_cs_step(me, holder, using, queue_len, head) {
            Err(why) => {
                proof {
                    assert forall|p: Raymond| !ray_enter_cs(t0@, p, me as nat) by {
                        if queue_len > 0 {
                            theorem_enter_cs_step_refuses_exactly_when_disabled(t0@, p, me as nat);
                        } else {
                            theorem_enter_cs_step_refuses_an_empty_queue(t0@, p, me as nat);
                        }
                    }
                }
                Err(why)
            },
            Ok(_) => {
                self.entries[i].queue.pop_front();
                self.entries[i].using = true;
                proof {
                    lemma_update_entry(t0, *self, i as int);
                    let r0 = t0@;
                    let n = me as nat;
                    lemma_insert_same(r0.holder, n);
                    lemma_insert_same(r0.asked, n);
                    assert(queue_view(self.entries@[i as int]) =~= r0.queue[n].drop_first());
                    assert(self@ == enter_cs_post(r0, n));
                    theorem_enter_cs_step_refines(r0, n);
                }
                Ok(())
            },
        }
    }

    /// `ExitCs`: node `me` leaves its critical section.
    pub fn exit_cs(&mut self, me: u64) -> (r: Result<(), RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(_) => {
                    &&& final(self)@ == exit_cs_post(old(self)@, me as nat)
                    &&& ray_exit_cs(old(self)@, final(self)@, me as nat)
                },
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond| !ray_exit_cs(old(self)@, p, me as nat)
                },
            },
    {
        let ghost t0 = *self;
        let Some(i) = self.find(me) else {
            proof {
                lemma_absent(t0, me);
            }
            return Err(RayRefusal::NotANode);
        };
        proof {
            lemma_found(t0, i as int);
            lemma_view_total(t0);
        }
        let using = self.entries[i].using;
        match exit_cs_step(using) {
            Err(why) => {
                proof {
                    assert forall|p: Raymond| !ray_exit_cs(t0@, p, me as nat) by {
                        theorem_exit_cs_step_refuses_exactly_when_disabled(t0@, p, me as nat);
                    }
                }
                Err(why)
            },
            Ok(_) => {
                self.entries[i].using = false;
                proof {
                    lemma_update_entry(t0, *self, i as int);
                    let r0 = t0@;
                    let n = me as nat;
                    lemma_insert_same(r0.holder, n);
                    lemma_insert_same(r0.asked, n);
                    assert(queue_view(self.entries@[i as int]) =~= r0.queue[n]);
                    lemma_insert_same(r0.queue, n);
                    assert(self@ == exit_cs_post(r0, n));
                    theorem_exit_cs_step_refines(r0, n);
                }
                Ok(())
            },
        }
    }

    /// `AssignPrivilege`: node `me`, which holds the privilege and is not using
    /// it, hands it to the head of its queue. Returns the node it goes to.
    pub fn assign_privilege(&mut self, me: u64) -> (r: Result<u64, RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(head) => {
                    &&& final(self)@ == assign_post(old(self)@, me as nat, head as nat)
                    &&& ray_assign_privilege(old(self)@, final(self)@, me as nat, head as nat)
                },
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond, h: NodeId| !ray_assign_privilege(old(self)@, p, me as nat, h)
                },
            },
    {
        let ghost t0 = *self;
        let Some(i) = self.find(me) else {
            proof {
                lemma_absent(t0, me);
            }
            return Err(RayRefusal::NotANode);
        };
        proof {
            lemma_found(t0, i as int);
            lemma_view_total(t0);
        }
        let queue_len = self.entries[i].queue.len() as u64;
        let head = if queue_len > 0 {
            self.entries[i].queue[0]
        } else {
            0
        };
        let found_head = self.find(head);
        let head_is_node = found_head.is_some();
        proof {
            match found_head {
                Some(j) => {
                    lemma_found(t0, j as int);
                },
                None => {
                    lemma_absent(t0, head);
                },
            }
        }
        let privilege = self.privilege;
        let holder = self.entries[i].holder;
        let using = self.entries[i].using;
        match assign_step(me, privilege, holder, using, queue_len, head, head_is_node) {
            Err(why) => {
                proof {
                    let r0 = t0@;
                    let n = me as nat;
                    assert forall|p: Raymond, h: NodeId| !ray_assign_privilege(r0, p, n, h) by {
                        if r0.queue[n].len() == 0 {
                            theorem_assign_step_refuses_an_empty_queue(r0, p, n, h);
                        } else if h == head as nat {
                            theorem_assign_step_refuses_exactly_when_disabled(r0, p, n, h);
                        }
                    }
                }
                Err(why)
            },
            Ok(to) => {
                let Some(j) = found_head else {
                    // `assign_step` only fires for a head that is a node.
                    return Err(RayRefusal::HeadNotANode);
                };
                proof {
                    assert(i != j) by {
                        assert(t0.entries@[i as int].id == me);
                        assert(t0.entries@[j as int].id == head);
                    }
                }
                self.entries[i].holder = to;
                self.entries[i].queue.pop_front();
                self.entries[i].asked = false;
                let ghost t1 = *self;
                proof {
                    lemma_update_entry(t0, t1, i as int);
                }
                self.entries[j].holder = to;
                let ghost t2 = *self;
                proof {
                    lemma_update_entry(t1, t2, j as int);
                }
                self.privilege = to;
                proof {
                    lemma_set_privilege(t2, *self, to);
                    let r0 = t0@;
                    let n = me as nat;
                    let h = to as nat;
                    // Node `to`'s own entries are untouched, so only its holder pointer moves.
                    assert(t1.entries@[j as int] == t0.entries@[j as int]);
                    assert(queue_view(t1.entries@[i as int]) =~= r0.queue[n].drop_first());
                    let q1 = r0.queue.insert(n, r0.queue[n].drop_first());
                    let a1 = r0.asked.insert(n, false);
                    let u1 = r0.using.insert(n, r0.using[n]);
                    lemma_insert_same(r0.using, n);
                    assert(q1[h] == r0.queue[h]);
                    assert(a1[h] == r0.asked[h]);
                    lemma_insert_same(q1, h);
                    lemma_insert_same(a1, h);
                    lemma_insert_same(r0.using, h);
                    assert(t2.entries@[j as int].using == t0.entries@[j as int].using);
                    assert(self@ == assign_post(r0, n, h));
                    theorem_assign_step_refines(r0, n, h);
                }
                Ok(to)
            },
        }
    }

    /// `Seize`: re-establish the privilege at `to`, which acts alone — nothing
    /// belonging to the old holder is touched. The composed coordinator, which
    /// checks the token, is the only caller.
    pub fn seize(&mut self, to: u64) -> (r: Result<(), RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(_) => {
                    &&& ray_seize(old(self)@, final(self)@, old(self).privilege as nat, to as nat)
                    &&& final(self)@.privilege == to as nat
                },
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond|
                        !ray_seize(old(self)@, p, old(self).privilege as nat, to as nat)
                },
            },
    {
        let ghost t0 = *self;
        let Some(j) = self.find(to) else {
            proof {
                lemma_absent(t0, to);
            }
            return Err(RayRefusal::NotANode);
        };
        if to == self.privilege {
            return Err(RayRefusal::HoldsPrivilege);
        }
        proof {
            lemma_found(t0, j as int);
        }
        self.entries[j].holder = to;
        let ghost t1 = *self;
        proof {
            lemma_update_entry(t0, t1, j as int);
        }
        self.privilege = to;
        proof {
            lemma_set_privilege(t1, *self, to);
            let r0 = t0@;
            let n = to as nat;
            lemma_insert_same(r0.queue, n);
            lemma_insert_same(r0.asked, n);
            lemma_insert_same(r0.using, n);
            assert(queue_view(t1.entries@[j as int]) =~= r0.queue[n]);
            assert(self@.holder =~= r0.holder.insert(n, n));
            assert(self@.queue =~= r0.queue);
            assert(self@.asked =~= r0.asked);
            assert(self@.using =~= r0.using);
            lemma_node_set(t0, t0.privilege as nat);
            assert(has_token(r0, t0.privilege as nat));
            assert(r0.nodes.contains(n));
            assert(ray_seize(r0, self@, t0.privilege as nat, n));
        }
        Ok(())
    }

    /// `Reconcile`: a stale holder — one that believes it holds the privilege and
    /// does not — learns the privilege was taken, and where it is.
    pub fn reconcile(&mut self, node: u64) -> (r: Result<(), RayRefusal>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match r {
                Ok(_) => ray_reconcile(old(self)@, final(self)@, node as nat),
                Err(_) => {
                    &&& final(self)@ == old(self)@
                    &&& forall|p: Raymond| !ray_reconcile(old(self)@, p, node as nat)
                },
            },
    {
        let ghost t0 = *self;
        let Some(i) = self.find(node) else {
            proof {
                lemma_absent(t0, node);
            }
            return Err(RayRefusal::NotANode);
        };
        proof {
            lemma_found(t0, i as int);
        }
        if self.entries[i].holder != node {
            return Err(RayRefusal::NotHolder);
        }
        if self.privilege == node {
            return Err(RayRefusal::HoldsPrivilege);
        }
        let privilege = self.privilege;
        self.entries[i].holder = privilege;
        self.entries[i].using = false;
        self.entries[i].asked = false;
        proof {
            lemma_update_entry(t0, *self, i as int);
            let r0 = t0@;
            let n = node as nat;
            lemma_insert_same(r0.queue, n);
            assert(queue_view(self.entries@[i as int]) =~= r0.queue[n]);
            assert(self@.holder =~= r0.holder.insert(n, r0.privilege));
            assert(self@.using =~= r0.using.insert(n, false));
            assert(self@.asked =~= r0.asked.insert(n, false));
            assert(self@.queue =~= r0.queue);
            assert(ray_reconcile(r0, self@, n));
        }
        Ok(())
    }
}

} // verus!
