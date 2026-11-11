//! **The model is not vacuous**, and what a benign network does.
//!
//! A safety proof about a step relation that no step satisfies would be true and
//! worthless. This file builds a step, from any state the invariant allows, and
//! shows what it does when the network is as kind as it can be: every replica hears
//! from every live replica in every `tcast`, so every replica's existent, common and
//! universal sets are all the live replicas and every replica's best existent
//! proposal is its best universal one. **Every live replica decides in that round.**
//!
//! That is not the paper's liveness theorem. The paper's liveness is that the
//! protocol terminates with probability one under *any* scheduling, including an
//! adversarial one; this model has no probability and says nothing about that. It is
//! the other direction of the same fact: the safety proof is not holding because
//! nothing can ever decide.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::id::Id;
use crate::quepaxa::model::*;
use crate::quepaxa::proofs::agreement::*;

verus! {

/// **With fewer than half the replicas crashed, the live ones are a majority.**
pub proof fn lemma_the_live_replicas_are_a_majority(s: QpState)
    requires
        qp_inv(s),
    ensures
        is_majority(s.replicas.len(), live(s)),
        live(s).len() > 0,
{
    lemma_set_difference_len(s.replicas, s.crashed);
    assert(s.replicas.intersect(s.crashed) =~= s.crashed);
    assert(live(s).len() == s.replicas.len() - s.crashed.len());
    lemma_len_subset(s.crashed, s.replicas);
}

/// **The initial states exist.** Without this, every safety theorem would be about a
/// machine that cannot start.
pub proof fn lemma_the_initial_states_exist(replicas: Set<Id>)
    requires
        replicas.len() > 0,
    ensures
        exists|s: QpState| qp_init(replicas, s),
{
    let s = QpState {
        replicas,
        pref: Map::<Id, nat>::new(replicas, |i: Id| 0nat),
        crashed: Set::<Id>::empty(),
        decided: Map::<Id, nat>::empty(),
        inputs: Set::<nat>::empty().insert(0nat),
    };
    let r0 = replicas.choose();
    assert(replicas.contains(r0));
    assert forall|v: nat| #[trigger] s.inputs.contains(v) <==> exists|i: Id|
        replicas.contains(i) && s.pref[i] == v by {
        if v == 0 {
            assert(s.pref[r0] == 0);
        }
    }
    assert(qp_init(replicas, s));
}

/// If everyone heard from all of `l` in `tcast 2`, and what each of them heard in
/// `tcast 1` is `l`, then `E_i` is `l`.
proof fn lemma_full_e(l: Set<Id>, heard1: Map<Id, Set<Id>>, heard2: Map<Id, Set<Id>>, i: Id)
    requires
        l.contains(i),
        heard2[i] == l,
        forall|x: Id| l.contains(x) ==> #[trigger] heard1[x] == l,
    ensures
        e_set(l, heard1, heard2, i) =~= l,
{
    assert forall|x: Id| #[trigger] e_set(l, heard1, heard2, i).contains(x) <==> l.contains(x) by {
        lemma_in_e_set(l, heard1, heard2, i, x);
        if l.contains(x) {
            assert(heard2[i].contains(x));
            assert(heard1[x] == l);
            assert(heard1[x].contains(x));
        }
    }
}

/// Likewise `C_i` is `l`, when everyone is relayed `x0`'s view.
proof fn lemma_full_c(
    l: Set<Id>,
    x0: Id,
    heard1: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    heard3: Map<Id, Set<Id>>,
    i: Id,
)
    requires
        l.contains(i),
        l.contains(x0),
        heard3[i] == l,
        heard1[x0] == l,
        forall|x: Id| l.contains(x) ==> #[trigger] relay2[x] == x0,
    ensures
        c_set(l, heard1, relay2, heard3, i) =~= l,
{
    assert forall|x: Id| #[trigger] c_set(l, heard1, relay2, heard3, i).contains(x) <==> l.contains(x) by {
        lemma_in_c_set(l, heard1, relay2, heard3, i, x);
        if l.contains(x) {
            assert(heard3[i].contains(x));
            assert(relay2[x] == x0);
            assert(pp_set(heard1, relay2, x).contains(x));
        }
    }
}

/// Witnesses in which everyone hears from every live replica, and is relayed the
/// same replica's view, satisfy `tcast`'s guarantees, and make every replica's
/// existent, common and universal sets the live replicas.
pub proof fn lemma_full_information_is_a_round(
    n: nat,
    l: Set<Id>,
    x0: Id,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
)
    requires
        l.contains(x0),
        is_majority(n, l),
        prio.dom() == l,
        heard1.dom() == l,
        heard2.dom() == l,
        heard3.dom() == l,
        relay2.dom() == l,
        relay3.dom() == l,
        forall|i: Id| l.contains(i) ==> #[trigger] heard1[i] == l,
        forall|i: Id| l.contains(i) ==> #[trigger] heard2[i] == l,
        forall|i: Id| l.contains(i) ==> #[trigger] heard3[i] == l,
        forall|i: Id| l.contains(i) ==> #[trigger] relay2[i] == x0,
        forall|i: Id| l.contains(i) ==> #[trigger] relay3[i] == x0,
    ensures
        round_ok(n, l, prio, heard1, heard2, heard3, relay2, relay3),
        forall|i: Id| l.contains(i) ==> #[trigger] e_set(l, heard1, heard2, i) =~= l,
        forall|i: Id| l.contains(i) ==> #[trigger] c_set(l, heard1, relay2, heard3, i) =~= l,
        forall|i: Id| l.contains(i) ==> #[trigger] u_set(heard1, relay2, relay3, i) =~= l,
{
    assert forall|i: Id| l.contains(i) implies #[trigger] e_set(l, heard1, heard2, i) =~= l by {
        lemma_full_e(l, heard1, heard2, i);
    }
    assert(heard1[x0] == l);
    assert forall|i: Id| l.contains(i) implies #[trigger] c_set(l, heard1, relay2, heard3, i) =~= l by {
        lemma_full_c(l, x0, heard1, relay2, heard3, i);
    }
    assert forall|i: Id| l.contains(i) implies #[trigger] u_set(heard1, relay2, relay3, i) =~= l by {
        assert(relay3[i] == x0);
        assert(relay2[x0] == x0);
    }
    assert forall|i: Id| l.contains(i) implies #[trigger] heard1[i].subset_of(l) && is_majority(n, heard1[i]) by {}
    assert forall|i: Id| l.contains(i) implies #[trigger] heard2[i].subset_of(l) && is_majority(n, heard2[i]) by {}
    assert forall|i: Id| l.contains(i) implies #[trigger] heard3[i].subset_of(l) && is_majority(n, heard3[i]) by {}
    assert forall|i: Id| l.contains(i) implies l.contains(#[trigger] relay2[i]) by {}
    assert forall|i: Id| l.contains(i) implies l.contains(#[trigger] relay3[i]) by {}
    assert forall|i: Id, m: Id| l.contains(i) && l.contains(m) implies #[trigger] pp_set(heard1, relay2, i).subset_of(
        #[trigger] e_set(l, heard1, heard2, m),
    ) by {
        assert(relay2[i] == x0);
        assert(pp_set(heard1, relay2, i) == l);
    }
    assert forall|i: Id, m: Id| l.contains(i) && l.contains(m) implies #[trigger] u_set(
        heard1,
        relay2,
        relay3,
        i,
    ).subset_of(#[trigger] c_set(l, heard1, relay2, heard3, m)) by {
    }
}

/// A round in which every set is the live replicas, and the post-state is what such a
/// round produces, is a step of the model.
proof fn lemma_a_full_information_round_is_a_step(
    pre: QpState,
    post: QpState,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
)
    requires
        round_ok(pre.replicas.len(), live(pre), prio, heard1, heard2, heard3, relay2, relay3),
        forall|i: Id|
            live(pre).contains(i) ==> #[trigger] e_set(live(pre), heard1, heard2, i) =~= live(pre),
        forall|i: Id|
            live(pre).contains(i) ==> #[trigger] c_set(live(pre), heard1, relay2, heard3, i)
                =~= live(pre),
        forall|i: Id|
            live(pre).contains(i) ==> #[trigger] u_set(heard1, relay2, relay3, i) =~= live(pre),
        post.replicas == pre.replicas,
        post.crashed == pre.crashed,
        post.inputs == pre.inputs,
        post.pref.dom() == pre.pref.dom(),
        forall|i: Id|
            pre.pref.dom().contains(i) ==> #[trigger] post.pref[i] == if live(pre).contains(i) {
                pre.pref[best(prio, live(pre))]
            } else {
                pre.pref[i]
            },
        post.decided.dom() == pre.decided.dom().union(live(pre)),
        forall|i: Id|
            post.decided.dom().contains(i) ==> #[trigger] post.decided[i] == if pre.decided.dom().contains(
                i,
            ) {
                pre.decided[i]
            } else {
                pre.pref[best(prio, live(pre))]
            },
    ensures
        qp_round(pre, post, prio, heard1, heard2, heard3, relay2, relay3),
{
    let l = live(pre);
    // Every replica's best existent proposal is its best universal one: all decide.
    assert(deciders(pre, prio, heard1, heard2, relay2, relay3) =~= l) by {
        assert forall|i: Id| l.contains(i) implies #[trigger] deciders(
            pre,
            prio,
            heard1,
            heard2,
            relay2,
            relay3,
        ).contains(i) by {
            assert(e_set(l, heard1, heard2, i) == l);
            assert(u_set(heard1, relay2, relay3, i) == l);
        }
    }
    assert forall|i: Id| #[trigger] pre.pref.dom().contains(i) implies post.pref[i] == if l.contains(i) {
        pre.pref[best(prio, c_set(l, heard1, relay2, heard3, i))]
    } else {
        pre.pref[i]
    } by {
        if l.contains(i) {
            assert(c_set(l, heard1, relay2, heard3, i) == l);
        }
    }
    assert forall|i: Id| #[trigger] post.decided.dom().contains(i) implies post.decided[i] == if pre.decided.dom().contains(
        i,
    ) {
        pre.decided[i]
    } else {
        pre.pref[best(prio, u_set(heard1, relay2, relay3, i))]
    } by {
        if !pre.decided.dom().contains(i) {
            assert(l.contains(i));
            assert(u_set(heard1, relay2, relay3, i) == l);
        }
    }
}

/// **A round in which every replica hears from every live replica exists, and
/// every live replica decides in it.**
pub proof fn theorem_a_round_with_full_information_decides(pre: QpState)
    requires
        qp_inv(pre),
    ensures
        exists|post: QpState, label: QpStep|
            #[trigger] qp_step(pre, post, label) && forall|i: Id|
                live(pre).contains(i) ==> post.decided.dom().contains(i),
{
    let l = live(pre);
    let n = pre.replicas.len();
    lemma_the_live_replicas_are_a_majority(pre);
    let x0 = l.choose();
    assert(l.contains(x0));
    let prio = Map::<Id, nat>::new(l, |i: Id| 0nat);
    let heard1 = Map::<Id, Set<Id>>::new(l, |i: Id| l);
    let heard2 = Map::<Id, Set<Id>>::new(l, |i: Id| l);
    let heard3 = Map::<Id, Set<Id>>::new(l, |i: Id| l);
    let relay2 = Map::<Id, Id>::new(l, |i: Id| x0);
    let relay3 = Map::<Id, Id>::new(l, |i: Id| x0);
    lemma_full_information_is_a_round(n, l, x0, prio, heard1, heard2, heard3, relay2, relay3);
    let b = best(prio, l);
    let post = QpState {
        pref: Map::new(pre.pref.dom(), |i: Id| if l.contains(i) { pre.pref[b] } else { pre.pref[i] }),
        decided: Map::new(
            pre.decided.dom().union(l),
            |i: Id| if pre.decided.dom().contains(i) { pre.decided[i] } else { pre.pref[b] },
        ),
        ..pre
    };
    let label = QpStep::Round { prio, heard1, heard2, heard3, relay2, relay3 };
    assert(post.pref.dom() =~= pre.pref.dom());
    assert(post.decided.dom() =~= pre.decided.dom().union(l));
    lemma_a_full_information_round_is_a_step(
        pre,
        post,
        prio,
        heard1,
        heard2,
        heard3,
        relay2,
        relay3,
    );
    assert(qp_step(pre, post, label));
    assert forall|i: Id| l.contains(i) implies post.decided.dom().contains(i) by {}
}

} // verus!
