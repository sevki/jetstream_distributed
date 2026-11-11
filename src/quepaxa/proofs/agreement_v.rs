//! **Agreement, validity and integrity of the abstract algorithm.**
//!
//! The whole argument is one chain of containments and one fact about the best
//! element of a set.
//!
//! The chain is `U_i ⊆ C_j ⊆ E_k` for every `i`, `j`, `k`: `tcast 3` makes the
//! universal set of one replica a subset of every replica's common set
//! ([`lemma_universal_in_common`]), and `tcast 2` makes every set that is relayed
//! into a common set a subset of every replica's existent set
//! ([`lemma_common_in_existent`]).
//!
//! The fact: a replica that decides takes `b = best(U_i) = best(E_i)`. Since
//! `b ∈ U_i ⊆ C_j ⊆ E_i` and `b` is the best of all of `E_i`, it is the best of
//! `C_j` for *every* `j` ([`lemma_a_decision_is_everyones_best_common`]). So every
//! live replica prefers `b`'s value next round, and every later round proposes
//! that value alone, which no later decision can depart from.
//!
//! Nothing here mentions probability, timing or a network. The conditions are
//! [`round_ok`](crate::quepaxa::model::round_ok)'s: `tcast`'s two guarantees,
//! stated of the witnesses a step carries.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::id::Id;
use crate::id::value::*;
use crate::quepaxa::model::*;

verus! {

// ---------------------------------------------------------------------------
// The best element of a set
// ---------------------------------------------------------------------------

/// `lt` is irreflexive and asymmetric: nothing ranks below itself, and two
/// proposals cannot each rank below the other.
pub proof fn lemma_lt_is_asymmetric(prio: Map<Id, nat>, x: Id, y: Id)
    ensures
        !(lt(prio, x, y) && lt(prio, y, x)),
{
}

/// Of two different proposers' proposals, one ranks below the other.
///
/// Different proposers have different ids, so a tie in priority is broken.
pub proof fn lemma_lt_is_total(prio: Map<Id, nat>, x: Id, y: Id)
    requires
        x != y,
    ensures
        lt(prio, x, y) || lt(prio, y, x),
{
    lemma_id_eq(x, y);
    assert(x.0 != y.0);
}

/// **Every non-empty set of proposals has a best one.**
pub proof fn lemma_best_exists(prio: Map<Id, nat>, s: Set<Id>)
    requires
        s.len() > 0,
    ensures
        exists|b: Id| is_best(prio, s, b),
    decreases s.len(),
{
    let x = s.choose();
    let rest = s.remove(x);
    assert(rest.len() == s.len() - 1);
    if rest.len() == 0 {
        assert(is_best(prio, s, x)) by {
            assert forall|y: Id| #[trigger] s.contains(y) && y != x implies lt(prio, y, x) by {
                assert(rest.contains(y));
                assert(rest.len() > 0);
            }
        }
    } else {
        lemma_best_exists(prio, rest);
        let b = choose|b: Id| is_best(prio, rest, b);
        assert(b != x);
        if lt(prio, x, b) {
            assert(is_best(prio, s, b)) by {
                assert forall|y: Id| #[trigger] s.contains(y) && y != b implies lt(prio, y, b) by {
                    if y == x {
                    } else {
                        assert(rest.contains(y));
                    }
                }
            }
        } else {
            lemma_lt_is_total(prio, x, b);
            assert(lt(prio, b, x));
            assert(is_best(prio, s, x)) by {
                assert forall|y: Id| #[trigger] s.contains(y) && y != x implies lt(prio, y, x) by {
                    assert(rest.contains(y));
                    if y == b {
                    } else {
                        assert(lt(prio, y, b));
                        // `y` ranks below `b`, which ranks below `x`.
                    }
                }
            }
        }
    }
}

/// **A set's best proposal is unique.**
pub proof fn lemma_best_is_unique(prio: Map<Id, nat>, s: Set<Id>, a: Id, b: Id)
    requires
        is_best(prio, s, a),
        is_best(prio, s, b),
    ensures
        a == b,
{
    if a != b {
        assert(lt(prio, a, b));
        assert(lt(prio, b, a));
        lemma_lt_is_asymmetric(prio, a, b);
    }
}

/// The element `best` names *is* the best, for a non-empty set.
pub proof fn lemma_best_is_best(prio: Map<Id, nat>, s: Set<Id>)
    requires
        s.len() > 0,
    ensures
        is_best(prio, s, best(prio, s)),
{
    lemma_best_exists(prio, s);
}

/// A majority is non-empty.
pub proof fn lemma_majority_is_nonempty(n: nat, s: Set<Id>)
    requires
        is_majority(n, s),
    ensures
        s.len() > 0,
{
}

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// The invariant every reachable state satisfies.
pub open spec fn qp_inv(s: QpState) -> bool {
    &&& s.replicas.len() > 0
    &&& s.crashed.subset_of(s.replicas)
    // A minority has crashed, so a majority is alive.
    &&& 2 * s.crashed.len() < s.replicas.len()
    &&& s.pref.dom() == s.replicas
    &&& s.decided.dom().subset_of(s.replicas)
    // **Validity**: every preference and every decision is a value some replica began with.
    &&& forall|i: Id| #[trigger] s.replicas.contains(i) ==> s.inputs.contains(s.pref[i])
    &&& forall|i: Id| #[trigger] s.decided.dom().contains(i) ==> s.inputs.contains(s.decided[i])
    // **Agreement**: no two replicas decided differently.
    &&& forall|i: Id, j: Id|
        #[trigger] s.decided.dom().contains(i) && #[trigger] s.decided.dom().contains(j)
            ==> s.decided[i] == s.decided[j]
    // **The decision is locked in**: once anyone has decided, every live replica prefers it.
    &&& forall|i: Id, j: Id|
        #[trigger] s.decided.dom().contains(i) && #[trigger] live(s).contains(j)
            ==> s.pref[j] == s.decided[i]
}

/// The initial states satisfy it.
pub proof fn lemma_init_satisfies_inv(replicas: Set<Id>, s: QpState)
    requires
        qp_init(replicas, s),
    ensures
        qp_inv(s),
{
    assert(s.crashed =~= Set::<Id>::empty());
    assert(s.crashed.len() == 0);
    assert(s.decided.dom() =~= Set::<Id>::empty());
    assert forall|i: Id| #[trigger] s.replicas.contains(i) implies s.inputs.contains(s.pref[i]) by {
        assert(s.pref[i] == s.pref[i]);
    }
}

// ---------------------------------------------------------------------------
// One round
// ---------------------------------------------------------------------------

/// What it is to be in `E_i`: a live replica, proposed by someone in the majority `i`
/// heard from in `tcast 2`, among what that someone heard in `tcast 1`.
pub proof fn lemma_in_e_set(
    l: Set<Id>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    i: Id,
    x: Id,
)
    ensures
        e_set(l, heard1, heard2, i).contains(x) <==> (l.contains(x) && exists|j: Id|
            #[trigger] heard2[i].contains(j) && heard1[j].contains(x)),
{
}

/// What it is to be in `C_i`.
pub proof fn lemma_in_c_set(
    l: Set<Id>,
    heard1: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    heard3: Map<Id, Set<Id>>,
    i: Id,
    x: Id,
)
    ensures
        c_set(l, heard1, relay2, heard3, i).contains(x) <==> (l.contains(x) && exists|j: Id|
            #[trigger] heard3[i].contains(j) && pp_set(heard1, relay2, j).contains(x)),
{
}

/// A round's sets are non-empty and inside the live replicas.
pub proof fn lemma_round_sets_are_sane(
    pre: QpState,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
    i: Id,
)
    requires
        qp_inv(pre),
        round_ok(pre.replicas.len(), live(pre), prio, heard1, heard2, heard3, relay2, relay3),
        live(pre).contains(i),
    ensures
        e_set(live(pre), heard1, heard2, i).subset_of(live(pre)),
        e_set(live(pre), heard1, heard2, i).len() > 0,
        c_set(live(pre), heard1, relay2, heard3, i).subset_of(live(pre)),
        c_set(live(pre), heard1, relay2, heard3, i).len() > 0,
        u_set(heard1, relay2, relay3, i).subset_of(live(pre)),
        u_set(heard1, relay2, relay3, i).len() > 0,
{
    let l = live(pre);
    let n = pre.replicas.len();
    // E_i is a filter of the live replicas, so is inside them; it is non-empty because
    // the majority it heard from is, and so is what the first of them heard.
    assert(heard2[i].subset_of(l));
    assert(is_majority(n, heard2[i]));
    lemma_majority_is_nonempty(n, heard2[i]);
    let j0 = heard2[i].choose();
    assert(heard2[i].contains(j0));
    assert(l.contains(j0));
    assert(heard1[j0].subset_of(l));
    assert(is_majority(n, heard1[j0]));
    lemma_majority_is_nonempty(n, heard1[j0]);
    let x0 = heard1[j0].choose();
    assert(heard1[j0].contains(x0));
    assert(l.contains(x0));
    lemma_in_e_set(l, heard1, heard2, i, x0);
    assert(e_set(l, heard1, heard2, i).contains(x0));
    // C_i likewise.
    assert(heard3[i].subset_of(l));
    assert(is_majority(n, heard3[i]));
    lemma_majority_is_nonempty(n, heard3[i]);
    let k0 = heard3[i].choose();
    assert(heard3[i].contains(k0));
    assert(l.contains(k0));
    assert(l.contains(relay2[k0]));
    assert(heard1[relay2[k0]].subset_of(l));
    assert(is_majority(n, heard1[relay2[k0]]));
    lemma_majority_is_nonempty(n, heard1[relay2[k0]]);
    let y0 = heard1[relay2[k0]].choose();
    assert(heard1[relay2[k0]].contains(y0));
    assert(l.contains(y0));
    lemma_in_c_set(l, heard1, relay2, heard3, i, y0);
    assert(pp_set(heard1, relay2, k0).contains(y0));
    assert(c_set(l, heard1, relay2, heard3, i).contains(y0));
    // U_i is the set one replica was relayed.
    assert(l.contains(relay3[i]));
    assert(l.contains(relay2[relay3[i]]));
    assert(heard1[relay2[relay3[i]]].subset_of(l));
    assert(is_majority(n, heard1[relay2[relay3[i]]]));
    lemma_majority_is_nonempty(n, heard1[relay2[relay3[i]]]);
    assert(u_set(heard1, relay2, relay3, i).len() > 0);
}

/// **`U_i ⊆ C_j`**: what `tcast 3` guarantees.
pub proof fn lemma_universal_in_common(
    pre: QpState,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
    i: Id,
    j: Id,
)
    requires
        round_ok(pre.replicas.len(), live(pre), prio, heard1, heard2, heard3, relay2, relay3),
        live(pre).contains(i),
        live(pre).contains(j),
    ensures
        u_set(heard1, relay2, relay3, i).subset_of(c_set(live(pre), heard1, relay2, heard3, j)),
{
}

/// **`C_j ⊆ E_k`**: every set relayed into a common set is inside every replica's
/// existent set, by what `tcast 2` guarantees.
pub proof fn lemma_common_in_existent(
    pre: QpState,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
    j: Id,
    k: Id,
)
    requires
        round_ok(pre.replicas.len(), live(pre), prio, heard1, heard2, heard3, relay2, relay3),
        live(pre).contains(j),
        live(pre).contains(k),
    ensures
        c_set(live(pre), heard1, relay2, heard3, j).subset_of(e_set(live(pre), heard1, heard2, k)),
{
    let l = live(pre);
    assert forall|x: Id| #[trigger] c_set(live(pre), heard1, relay2, heard3, j).contains(x) implies e_set(
        l,
        heard1,
        heard2,
        k,
    ).contains(x) by {
        let m = choose|m: Id|
            #[trigger] heard3[j].contains(m) && pp_set(heard1, relay2, m).contains(x);
        assert(heard3[j].subset_of(l));
        assert(l.contains(m));
        assert(pp_set(heard1, relay2, m).subset_of(e_set(live(pre), heard1, heard2, k)));
    }
}

/// **A decision is everyone's best common proposal.**
///
/// If replica `i` decides, then for *every* live replica `j` the best proposal of
/// `C_j` is the one `i` decided on.
pub proof fn lemma_a_decision_is_everyones_best_common(
    pre: QpState,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
    i: Id,
    j: Id,
)
    requires
        qp_inv(pre),
        round_ok(pre.replicas.len(), live(pre), prio, heard1, heard2, heard3, relay2, relay3),
        deciders(pre, prio, heard1, heard2, relay2, relay3).contains(i),
        live(pre).contains(j),
    ensures
        best(prio, c_set(live(pre), heard1, relay2, heard3, j)) == best(
            prio,
            u_set(heard1, relay2, relay3, i),
        ),
{
    let e = e_set(live(pre), heard1, heard2, i);
    let u = u_set(heard1, relay2, relay3, i);
    let c = c_set(live(pre), heard1, relay2, heard3, j);
    lemma_round_sets_are_sane(pre, prio, heard1, heard2, heard3, relay2, relay3, i);
    lemma_round_sets_are_sane(pre, prio, heard1, heard2, heard3, relay2, relay3, j);
    lemma_best_is_best(prio, e);
    lemma_best_is_best(prio, u);
    let b = best(prio, u);
    assert(best(prio, e) == b);
    lemma_universal_in_common(pre, prio, heard1, heard2, heard3, relay2, relay3, i, j);
    lemma_common_in_existent(pre, prio, heard1, heard2, heard3, relay2, relay3, j, i);
    // b ∈ U_i ⊆ C_j ⊆ E_i, and b is the best of all of E_i, so of C_j.
    assert(u.contains(b));
    assert(c.contains(b));
    assert(is_best(prio, c, b)) by {
        assert forall|y: Id| #[trigger] c.contains(y) && y != b implies lt(prio, y, b) by {
            assert(e.contains(y));
        }
    }
    lemma_best_is_best(prio, c);
    lemma_best_is_unique(prio, c, best(prio, c), b);
}

/// **A round preserves the invariant.**
pub proof fn lemma_round_preserves_inv(
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
        qp_inv(pre),
        qp_round(pre, post, prio, heard1, heard2, heard3, relay2, relay3),
    ensures
        qp_inv(post),
{
    let l = live(pre);
    let d = deciders(pre, prio, heard1, heard2, relay2, relay3);
    assert(live(post) =~= l);
    assert(post.crashed.len() == pre.crashed.len());
    // Every adopted or decided proposal is a live replica's.
    assert forall|j: Id| #[trigger] l.contains(j) implies {
        &&& l.contains(best(prio, c_set(live(pre), heard1, relay2, heard3, j)))
        &&& c_set(live(pre), heard1, relay2, heard3, j).contains(best(prio, c_set(live(pre), heard1, relay2, heard3, j)))
    } by {
        lemma_round_sets_are_sane(pre, prio, heard1, heard2, heard3, relay2, relay3, j);
        lemma_best_is_best(prio, c_set(live(pre), heard1, relay2, heard3, j));
    }
    assert forall|i: Id| #[trigger] d.contains(i) implies {
        &&& l.contains(best(prio, u_set(heard1, relay2, relay3, i)))
        &&& l.contains(i)
    } by {
        lemma_round_sets_are_sane(pre, prio, heard1, heard2, heard3, relay2, relay3, i);
        lemma_best_is_best(prio, u_set(heard1, relay2, relay3, i));
    }
    assert(post.decided.dom().subset_of(post.replicas)) by {
        assert forall|i: Id| #[trigger] post.decided.dom().contains(i) implies post.replicas.contains(i) by {
            if pre.decided.dom().contains(i) {
            } else {
                assert(d.contains(i));
            }
        }
    }
    // Validity.
    assert forall|i: Id| #[trigger] post.replicas.contains(i) implies post.inputs.contains(post.pref[i]) by {
        assert(pre.pref.dom().contains(i));
        if l.contains(i) {
            lemma_round_sets_are_sane(pre, prio, heard1, heard2, heard3, relay2, relay3, i);
            let x = best(prio, c_set(live(pre), heard1, relay2, heard3, i));
            assert(pre.replicas.contains(x));
        }
    }
    assert forall|i: Id| #[trigger] post.decided.dom().contains(i) implies post.inputs.contains(
        post.decided[i],
    ) by {
        if !pre.decided.dom().contains(i) {
            assert(d.contains(i));
            let x = best(prio, u_set(heard1, relay2, relay3, i));
            assert(pre.replicas.contains(x));
        }
    }
    // Agreement and lock-in. A decider is either one who decided before, or a new one
    // whose decision every live replica adopts, by the lemma above.
    assert forall|i: Id, j: Id|
        #[trigger] post.decided.dom().contains(i) && #[trigger] live(post).contains(j) implies post.pref[j]
        == post.decided[i] by {
        lemma_round_sets_are_sane(pre, prio, heard1, heard2, heard3, relay2, relay3, j);
        let xj = best(prio, c_set(live(pre), heard1, relay2, heard3, j));
        assert(pre.pref.dom().contains(j));
        assert(post.pref[j] == pre.pref[xj]);
        if pre.decided.dom().contains(i) {
            assert(pre.decided[i] == pre.decided[i]);
            assert(post.decided[i] == pre.decided[i]);
            assert(l.contains(xj));
            assert(pre.pref[xj] == pre.decided[i]);
        } else {
            assert(d.contains(i));
            lemma_a_decision_is_everyones_best_common(
                pre,
                prio,
                heard1,
                heard2,
                heard3,
                relay2,
                relay3,
                i,
                j,
            );
        }
    }
    assert forall|i: Id, j: Id|
        #[trigger] post.decided.dom().contains(i) && #[trigger] post.decided.dom().contains(j) implies post.decided[i]
        == post.decided[j] by {
        // Both decided in `pre`, or one did and one is new, or both are new.
        let in_i = pre.decided.dom().contains(i);
        let in_j = pre.decided.dom().contains(j);
        if in_i && in_j {
        } else if in_i && !in_j {
            assert(d.contains(j));
            let xj = best(prio, u_set(heard1, relay2, relay3, j));
            assert(l.contains(xj));
            assert(pre.pref[xj] == pre.decided[i]);
        } else if !in_i && in_j {
            assert(d.contains(i));
            let xi = best(prio, u_set(heard1, relay2, relay3, i));
            assert(l.contains(xi));
            assert(pre.pref[xi] == pre.decided[j]);
        } else {
            assert(d.contains(i));
            assert(d.contains(j));
            // Both are the best common proposal of any one live replica.
            lemma_round_sets_are_sane(pre, prio, heard1, heard2, heard3, relay2, relay3, i);
            lemma_a_decision_is_everyones_best_common(
                pre,
                prio,
                heard1,
                heard2,
                heard3,
                relay2,
                relay3,
                i,
                i,
            );
            lemma_a_decision_is_everyones_best_common(
                pre,
                prio,
                heard1,
                heard2,
                heard3,
                relay2,
                relay3,
                j,
                i,
            );
        }
    }
}

/// **A crash preserves the invariant.**
pub proof fn lemma_crash_preserves_inv(pre: QpState, post: QpState, node: Id)
    requires
        qp_inv(pre),
        qp_crash(pre, post, node),
    ensures
        qp_inv(post),
{
    lemma_len_subset(pre.crashed, pre.replicas);
    assert(post.crashed.len() == pre.crashed.len() + 1);
    assert(post.crashed.subset_of(post.replicas));
    // Fewer replicas are live; everything else is as it was.
    assert(live(post).subset_of(live(pre)));
    assert forall|i: Id, j: Id|
        #[trigger] post.decided.dom().contains(i) && #[trigger] live(post).contains(j) implies post.pref[j]
        == post.decided[i] by {
        assert(live(pre).contains(j));
    }
}

/// **Every step preserves the invariant.**
pub proof fn lemma_step_preserves_inv(pre: QpState, post: QpState, label: QpStep)
    requires
        qp_inv(pre),
        qp_step(pre, post, label),
    ensures
        qp_inv(post),
{
    match label {
        QpStep::Crash { node } => lemma_crash_preserves_inv(pre, post, node),
        QpStep::Round { prio, heard1, heard2, heard3, relay2, relay3 } => {
            lemma_round_preserves_inv(pre, post, prio, heard1, heard2, heard3, relay2, relay3)
        },
    }
}

/// **Every reachable state satisfies the invariant.**
pub proof fn theorem_every_reachable_state_satisfies_the_invariant(replicas: Set<Id>, s: QpState)
    requires
        qp_reachable(replicas, s),
    ensures
        qp_inv(s),
{
    let tr = choose|tr: Seq<QpState>| qp_execution(replicas, tr) && tr[tr.len() - 1] == s;
    lemma_init_satisfies_inv(replicas, tr[0]);
    lemma_trace_satisfies_inv(replicas, tr, tr.len() - 1);
}

/// Every state of an execution, up to `k`, satisfies the invariant.
proof fn lemma_trace_satisfies_inv(replicas: Set<Id>, tr: Seq<QpState>, k: int)
    requires
        qp_execution(replicas, tr),
        0 <= k < tr.len(),
    ensures
        qp_inv(tr[k]),
    decreases k,
{
    lemma_init_satisfies_inv(replicas, tr[0]);
    if k > 0 {
        lemma_trace_satisfies_inv(replicas, tr, k - 1);
        assert(0 <= k - 1 < tr.len() - 1);
        assert(qp_next(tr[k - 1], tr[(k - 1) + 1]));
        assert(tr[(k - 1) + 1] == tr[k]);
        let label = choose|label: QpStep| #[trigger] qp_step(tr[k - 1], tr[k], label);
        lemma_step_preserves_inv(tr[k - 1], tr[k], label);
    }
}

// ---------------------------------------------------------------------------
// The theorems
// ---------------------------------------------------------------------------

/// **Agreement.** In every reachable state, no two replicas have decided
/// differently.
pub proof fn theorem_agreement(replicas: Set<Id>, s: QpState, i: Id, j: Id)
    requires
        qp_reachable(replicas, s),
        s.decided.dom().contains(i),
        s.decided.dom().contains(j),
    ensures
        s.decided[i] == s.decided[j],
{
    theorem_every_reachable_state_satisfies_the_invariant(replicas, s);
}

/// A step does not change the record of inputs.
proof fn lemma_step_keeps_inputs(pre: QpState, post: QpState, label: QpStep)
    requires
        qp_step(pre, post, label),
    ensures
        post.inputs == pre.inputs,
{
}

/// The record of inputs is the same all along an execution.
proof fn lemma_inputs_never_change(replicas: Set<Id>, tr: Seq<QpState>, k: int)
    requires
        qp_execution(replicas, tr),
        0 <= k < tr.len(),
    ensures
        tr[k].inputs == tr[0].inputs,
    decreases k,
{
    if k > 0 {
        lemma_inputs_never_change(replicas, tr, k - 1);
        assert(0 <= k - 1 < tr.len() - 1);
        assert(qp_next(tr[k - 1], tr[(k - 1) + 1]));
        assert(tr[(k - 1) + 1] == tr[k]);
        let label = choose|label: QpStep| #[trigger] qp_step(tr[k - 1], tr[k], label);
        lemma_step_keeps_inputs(tr[k - 1], tr[k], label);
    }
}

/// **Validity.** At every point of every execution, whatever a replica has decided is
/// a value some replica began with.
pub proof fn theorem_validity(replicas: Set<Id>, tr: Seq<QpState>, k: int, i: Id)
    requires
        qp_execution(replicas, tr),
        0 <= k < tr.len(),
        tr[k].decided.dom().contains(i),
    ensures
        exists|r: Id| replicas.contains(r) && #[trigger] tr[0].pref[r] == tr[k].decided[i],
{
    lemma_trace_satisfies_inv(replicas, tr, k);
    lemma_inputs_never_change(replicas, tr, k);
    assert(tr[k].inputs.contains(tr[k].decided[i]));
    assert(tr[0].inputs.contains(tr[k].decided[i]));
}

/// **A decision is locked in.** Once any replica has decided, every replica that
/// has not crashed prefers the decided value, so no later round proposes another.
pub proof fn theorem_a_decision_is_locked_in(replicas: Set<Id>, s: QpState, i: Id, j: Id)
    requires
        qp_reachable(replicas, s),
        s.decided.dom().contains(i),
        live(s).contains(j),
    ensures
        s.pref[j] == s.decided[i],
{
    theorem_every_reachable_state_satisfies_the_invariant(replicas, s);
}

} // verus!
