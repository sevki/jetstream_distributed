//! The composed machine's four steps, executable and verified.
//!
//! [`crate::composed::steps`] decides whether the *coupling* lets a step through.
//! This is the step: it holds the two layers' records —
//! [`RegistryCore`] and
//! [`RayTable`] — and the set of nodes that owe a
//! reconciliation, and each function checks the coupling guard, takes the layers'
//! steps, and keeps the debts, with one contract that is the model's composed
//! step.
//!
//! # Why free functions
//!
//! The two layers live behind their own locks in the service, and the coordinator
//! takes both, in one fixed order, behind its own gate. A function over
//! `&mut RayTable`, `&mut NodeSet` and `&RegistryCore` is what it can call with
//! the guards it holds, and what the proofs can say about without a struct that
//! owns both.
//!
//! # What is verified
//!
//! * `pass_token` — `cs_pass_token`: only once the actor is `Unowned`, the
//!   routing layer's assignment, and the recipient's debt discharged.
//! * `seize_token` — `cs_seize_token`: only once the actor is `Unowned`, only
//!   `to` acts, and the old holder now owes a reconciliation.
//! * `acquire_under_token` — `cs_acquire_under_token`: the ownership layer's
//!   acquire, for the node holding the privilege.
//! * `reconcile` — `cs_reconcile`: a node that owes one and really is stale.
//! * A refusal changes nothing.
//!
//! # What is not
//!
//! The locks and their order, the gate, the identity lookup and the logs.
#![allow(unused_imports)]
#![allow(clippy::new_without_default, clippy::match_like_matches_macro)]

use vstd::prelude::*;

use crate::composed::model::*;
use crate::composed::proofs::refinement::*;
use crate::composed::steps::*;
use crate::ownership::fencing::*;
use crate::ownership::model::NodeId;
use crate::ownership::registry::*;
use crate::ownership::spec::*;
use crate::ownership::steps::*;
use crate::raymond::exec::*;
use crate::raymond::model::*;
use crate::raymond::proofs::refinement::*;
use crate::raymond::steps::*;

verus! {

/// A set of nodes. The composed machine's `seized`: the nodes that owe a
/// reconciliation.
pub struct NodeSet {
    /// The members, possibly more than once.
    pub items: Vec<u64>,
}

impl View for NodeSet {
    type V = Set<nat>;

    open spec fn view(&self) -> Set<nat> {
        self.items@.map_values(|x: u64| x as nat).to_set()
    }
}

/// A node is in the set exactly when it is among the items.
pub proof fn lemma_in_items(items: Seq<u64>, n: nat)
    ensures
        items.map_values(|x: u64| x as nat).to_set().contains(n) <==> exists|i: int|
            0 <= i < items.len() && items[i] as nat == n,
{
    let m = items.map_values(|x: u64| x as nat);
    m.to_set_ensures();
    if exists|i: int| 0 <= i < items.len() && items[i] as nat == n {
        let i = choose|i: int| 0 <= i < items.len() && items[i] as nat == n;
        assert(m[i] == n);
        assert(m.contains(n));
    }
    if m.contains(n) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == n;
        assert(items[i] as nat == n);
    }
}

impl NodeSet {
    /// The empty set.
    pub fn new() -> (s: NodeSet)
        ensures
            forall|n: nat| !s@.contains(n),
    {
        let s = NodeSet { items: Vec::new() };
        proof {
            assert forall|n: nat| !s@.contains(n) by {
                lemma_in_items(s.items@, n);
            }
        }
        s
    }

    /// Whether `x` is in the set.
    pub fn contains(&self, x: u64) -> (r: bool)
        ensures
            r == self@.contains(x as nat),
    {
        let mut i: usize = 0;
        while i < self.items.len()
            invariant
                i <= self.items@.len(),
                forall|k: int| 0 <= k < i ==> self.items@[k] != x,
            decreases self.items@.len() - i,
        {
            if self.items[i] == x {
                proof {
                    lemma_in_items(self.items@, x as nat);
                    assert(self.items@[i as int] as nat == x as nat);
                }
                return true;
            }
            i += 1;
        }
        proof {
            lemma_in_items(self.items@, x as nat);
            if self@.contains(x as nat) {
                let k = choose|k: int| 0 <= k < self.items@.len() && self.items@[k] as nat == x as nat;
                assert(self.items@[k] == x);
            }
        }
        false
    }

    /// Add `x`.
    pub fn insert(&mut self, x: u64)
        ensures
            final(self)@ == old(self)@.insert(x as nat),
    {
        let ghost before = self.items@;
        if !self.contains(x) {
            self.items.push(x);
        }
        proof {
            let after = self.items@;
            assert forall|n: nat| self@.contains(n) == old(self)@.insert(x as nat).contains(n) by {
                lemma_in_items(before, n);
                lemma_in_items(after, n);
                if n == x as nat {
                    lemma_in_items(before, x as nat);
                    if !old(self)@.contains(x as nat) {
                        assert(after[after.len() - 1] == x);
                    }
                } else {
                    if self@.contains(n) {
                        let k = choose|k: int| 0 <= k < after.len() && after[k] as nat == n;
                        assert(k < before.len());
                    }
                    if old(self)@.contains(n) {
                        let k = choose|k: int| 0 <= k < before.len() && before[k] as nat == n;
                        assert(after[k] == before[k]);
                    }
                }
            }
            assert(self@ =~= old(self)@.insert(x as nat));
        }
    }

    /// Remove `x`.
    pub fn remove(&mut self, x: u64)
        ensures
            final(self)@ == old(self)@.remove(x as nat),
    {
        let ghost before = self.items@;
        let mut out: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < self.items.len()
            invariant
                i <= self.items@.len(),
                self.items@ == before,
                forall|k: int| 0 <= k < out@.len() ==> out@[k] != x,
                forall|k: int|
                    #![trigger out@[k]]
                    0 <= k < out@.len() ==> exists|j: int|
                        #![trigger before[j]]
                        0 <= j < i && before[j] == out@[k],
                forall|j: int|
                    #![trigger before[j]]
                    0 <= j < i && before[j] != x ==> exists|k: int|
                        #![trigger out@[k]]
                        0 <= k < out@.len() && out@[k] == before[j],
            decreases self.items@.len() - i,
        {
            let v = self.items[i];
            let ghost old_out = out@;
            if v != x {
                out.push(v);
            }
            proof {
                assert(before[i as int] == v);
                assert forall|j: int| 0 <= j < i + 1 && before[j] != x implies exists|k: int|
                    #![trigger out@[k]]
                    0 <= k < out@.len() && out@[k] == before[j] by {
                    if j == i as int {
                        let last = (out@.len() - 1) as int;
                        assert(out@[last] == v);
                    } else {
                        let k = choose|k: int| 0 <= k < old_out.len() && old_out[k] == before[j];
                        assert(out@[k] == old_out[k]);
                    }
                }
                assert forall|k: int|
                    #![trigger out@[k]]
                    0 <= k < out@.len() implies exists|j: int|
                    #![trigger before[j]]
                    0 <= j < i + 1 && before[j] == out@[k] by {
                    if k == old_out.len() as int && v != x {
                        assert(before[i as int] == out@[k]);
                    } else {
                        let j = choose|j: int| 0 <= j < i && before[j] == old_out[k];
                        assert(out@[k] == old_out[k]);
                    }
                }
            }
            i += 1;
        }
        self.items = out;
        proof {
            let after = self.items@;
            assert forall|n: nat| self@.contains(n) == old(self)@.remove(x as nat).contains(n) by {
                lemma_in_items(before, n);
                lemma_in_items(after, n);
                if self@.contains(n) {
                    let k = choose|k: int| 0 <= k < after.len() && after[k] as nat == n;
                    let j = choose|j: int| 0 <= j < before.len() && before[j] == after[k];
                    assert(before[j] as nat == n);
                    assert(n != x as nat);
                }
                if old(self)@.remove(x as nat).contains(n) {
                    let j = choose|j: int| 0 <= j < before.len() && before[j] as nat == n;
                    assert(before[j] != x);
                    let k = choose|k: int| 0 <= k < after.len() && after[k] == before[j];
                    assert(after[k] as nat == n);
                }
            }
            assert(self@ =~= old(self)@.remove(x as nat));
        }
    }
}

/// Why a composed step did not happen: the coupling's reason, or one of the
/// layers'.
#[derive(Clone, Copy)]
pub enum ComposedError {
    /// The coupling declined it.
    Coupled(CoupledRefusal),
    /// The routing layer declined it.
    Ray(RayRefusal),
    /// The ownership layer declined it.
    Own(Refusal),
}

/// Is the actor `Unowned`?
pub fn actor_unowned(own: &RegistryCore) -> (r: bool)
    ensures
        r == is_unowned(own.state.view()),
{
    match own.state {
        ExecState::Unowned { epoch: _, intended: _ } => true,
        _ => false,
    }
}

/// `cs_pass_token`: the node holding the privilege passes it to the head of its
/// queue — but only once the actor has been released. The recipient's debt, if it
/// had one, is discharged: receiving the privilege is learning the truth.
pub fn pass_token(own: &RegistryCore, ray: &mut RayTable, seized: &mut NodeSet, me: u64) -> (r:
    Result<u64, ComposedError>)
    requires
        old(ray).well_formed(),
    ensures
        final(ray).well_formed(),
        match r {
            Ok(head) => {
                &&& is_unowned(own.state.view())
                &&& final(ray)@ == assign_post(old(ray)@, me as nat, head as nat)
                &&& ray_assign_privilege(old(ray)@, final(ray)@, me as nat, head as nat)
                &&& final(seized)@ == old(seized)@.remove(head as nat)
            },
            Err(_) => {
                &&& final(ray)@ == old(ray)@
                &&& final(seized)@ == old(seized)@
                &&& (!is_unowned(own.state.view()) || forall|p: Raymond, h: NodeId|
                    !ray_assign_privilege(old(ray)@, p, me as nat, h))
            },
        },
{
    let unowned = actor_unowned(own);
    match pass_token_step(unowned) {
        Err(why) => Err(ComposedError::Coupled(why)),
        Ok(_) => match ray.assign_privilege(me) {
            Ok(head) => {
                seized.remove(head);
                Ok(head)
            },
            Err(why) => Err(ComposedError::Ray(why)),
        },
    }
}

/// `cs_seize_token`: re-establish the privilege at `to`, once the actor has been
/// released. **Only `to` acts**; the old holder now owes a reconciliation and
/// `to` no longer does. Returns the old holder.
pub fn seize_token(own: &RegistryCore, ray: &mut RayTable, seized: &mut NodeSet, to: u64) -> (r:
    Result<u64, ComposedError>)
    requires
        old(ray).well_formed(),
    ensures
        final(ray).well_formed(),
        match r {
            Ok(from) => {
                &&& is_unowned(own.state.view())
                &&& from == old(ray).privilege
                &&& ray_seize(old(ray)@, final(ray)@, from as nat, to as nat)
                &&& final(ray)@.privilege == to as nat
                &&& final(seized)@ == old(seized)@.insert(from as nat).remove(to as nat)
            },
            Err(_) => {
                &&& final(ray)@ == old(ray)@
                &&& final(seized)@ == old(seized)@
                &&& (!is_unowned(own.state.view()) || forall|p: Raymond|
                    !ray_seize(old(ray)@, p, old(ray).privilege as nat, to as nat))
            },
        },
{
    let unowned = actor_unowned(own);
    let from = ray.privilege;
    let found = ray.find(to);
    let to_is_node = found.is_some();
    proof {
        match found {
            Some(j) => {
                lemma_found(*ray, j as int);
            },
            None => {
                lemma_absent(*ray, to);
            },
        }
    }
    match seize_step(unowned, from, ray.privilege, to, to_is_node) {
        Err(why) => Err(ComposedError::Coupled(why)),
        Ok(_) => match ray.seize(to) {
            Ok(_) => {
                seized.insert(from);
                seized.remove(to);
                Ok(from)
            },
            Err(why) => Err(ComposedError::Ray(why)),
        },
    }
}

/// `cs_acquire_under_token`: the ownership layer's acquire, for the node holding
/// the privilege and nobody else.
pub fn acquire_under_token(own: &mut RegistryCore, ray: &RayTable, node: u64, epoch: u64) -> (r:
    Result<(), ComposedError>)
    requires
        ray.well_formed(),
    ensures
        final(own).writes == old(own).writes,
        grants_same(*old(own), *final(own)),
        match r {
            Ok(_) => {
                &&& has_token(ray@, node as nat)
                &&& acquire_fires(
                    old(own).state.view(),
                    node as nat,
                    epoch as nat,
                    old(own).has_grant(node as nat, epoch as nat),
                )
                &&& final(own).state.view() == acquire_next(old(own).state.view(), node as nat)
            },
            Err(ComposedError::Coupled(_)) => {
                &&& !has_token(ray@, node as nat)
                &&& final(own).state.view() == old(own).state.view()
            },
            Err(ComposedError::Own(_)) => {
                &&& !acquire_fires(
                    old(own).state.view(),
                    node as nat,
                    epoch as nat,
                    old(own).has_grant(node as nat, epoch as nat),
                )
                &&& final(own).state.view() == old(own).state.view()
            },
            Err(ComposedError::Ray(_)) => false,
        },
{
    proof {
        lemma_node_set(*ray, ray.privilege as nat);
    }
    match acquire_under_token_step(ray.privilege, node) {
        Err(why) => Err(ComposedError::Coupled(why)),
        Ok(_) => match own.acquire(node, epoch) {
            Ok(_) => Ok(()),
            Err(why) => Err(ComposedError::Own(why)),
        },
    }
}

/// `cs_reconcile`: a node that owes a reconciliation, and whose belief really is
/// stale, learns the privilege was taken.
pub fn reconcile(ray: &mut RayTable, seized: &mut NodeSet, node: u64) -> (r: Result<
    (),
    ComposedError,
>)
    requires
        old(ray).well_formed(),
    ensures
        final(ray).well_formed(),
        match r {
            Ok(_) => {
                &&& old(seized)@.contains(node as nat)
                &&& ray_reconcile(old(ray)@, final(ray)@, node as nat)
                &&& final(seized)@ == old(seized)@.remove(node as nat)
            },
            Err(_) => {
                &&& final(ray)@ == old(ray)@
                &&& final(seized)@ == old(seized)@
                &&& (!old(seized)@.contains(node as nat) || forall|p: Raymond|
                    !ray_reconcile(old(ray)@, p, node as nat))
            },
        },
{
    let owes = seized.contains(node);
    let Some(i) = ray.find(node) else {
        proof {
            lemma_absent(*ray, node);
        }
        return Err(ComposedError::Coupled(CoupledRefusal::NotANode));
    };
    proof {
        lemma_found(*ray, i as int);
    }
    let believes_holds = ray.entries[i].holder == node;
    let has_token = ray.privilege == node;
    match reconcile_step(owes, believes_holds, has_token) {
        Err(why) => Err(ComposedError::Coupled(why)),
        Ok(_) => match ray.reconcile(node) {
            Ok(_) => {
                seized.remove(node);
                Ok(())
            },
            Err(why) => Err(ComposedError::Ray(why)),
        },
    }
}

} // verus!
