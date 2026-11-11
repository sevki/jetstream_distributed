//! **QuePaxa's abstract consensus algorithm**, over an ideal threshold broadcast.
//!
//! QuePaxa (Tennage, Băsescu, Kokoris-Kogias, Syta, Jovanovic, Estrada-Galiñanes
//! and Ford, "QuePaxa: Escaping the Tyranny of Timeouts in Consensus", SOSP 2023)
//! is a consensus protocol whose liveness does not depend on timeouts. Its core is
//! a randomised asynchronous algorithm that the paper states first as an *abstract*
//! algorithm (its Algorithm 1) over a lock-step primitive, `tcast`, and then
//! implements, concretely, with recorders and proposers (its Algorithms 2 to 4).
//! This file is the abstract algorithm. The concrete protocol is not here.
//!
//! # The round
//!
//! Every round, each live replica `i` makes a **proposal**: its preferred value
//! with a priority. Proposals are compared by priority and, at a tie, by the
//! proposer's id, so any set of proposals has exactly one best. The replicas then
//! disseminate proposals in three `tcast` steps:
//!
//! ```text
//! tcast 1:  P_i   the proposals i heard from some majority
//! tcast 2:  E_i   the union of P_j over some majority:  proposals that *exist* for i
//!           P'_i  one replica's P_k that every replica's E contains
//! tcast 3:  C_i   the union of P'_j over some majority: proposals that are *common*
//!           U_i   one replica's P'_k that every replica's C contains
//! ```
//!
//! and then each replica `i` takes `best(C_i)` as its preferred value for the next
//! round, and **decides** `best(U_i)` if `best(E_i) = best(U_i)`.
//!
//! The two guarantees `tcast` gives are exactly what [`QpStep::Round`] states of
//! its witnesses: a replica hears from a majority, and the set it is handed back
//! as `P'` (or `U`) is contained in every replica's `E` (or `C`). Nothing else
//! about the network is assumed: *which* majority each replica heard from, and
//! which relay it was handed, are the label's data, so every way of choosing them
//! is a step. The priorities are the label's data too, and any assignment is a
//! step, so the model says what is *allowed* and every refinement is a correct way
//! to choose.
//!
//! # What is and is not here
//!
//! This is the **abstract** algorithm. That the paper's concrete protocol
//! (recorders with interval summary registers, and proposers that catch up) really
//! provides `tcast`'s two guarantees is the paper's Appendix B argument, and is
//! **not** modelled or proved here. So the theorems about this model are
//! conditional on an ideal `tcast`. They say the *idea* is sound, not that any
//! implementation of it is.
//!
//! Also not here: the probability of termination (the paper's liveness is
//! probabilistic, and this model has no probability), the fast path that lets a
//! designated leader decide in one round trip, and the hedging schedule. A replica
//! crashes between rounds and never takes another step; a crash in the middle of
//! a `tcast` is the same as a crash after it, because a replica heard from by only
//! some is just a replica some majorities contain.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

verus! {

/// `s` is more than half of `n`.
pub open spec fn is_majority(n: nat, s: Set<Id>) -> bool {
    2 * s.len() > n
}

/// The state of the consensus for one slot.
///
/// `replicas` is fixed and part of the state, so that a step can say what a
/// majority is. `inputs` is a ghost record of the values the replicas started
/// with, so that validity can be stated.
pub struct QpState {
    /// Every replica, crashed or not.
    pub replicas: Set<Id>,
    /// What each replica prefers for the current round.
    pub pref: Map<Id, nat>,
    /// The replicas that have crashed. They take no further step.
    pub crashed: Set<Id>,
    /// Who has decided, and on what. A replica decides at most once.
    pub decided: Map<Id, nat>,
    /// The values the replicas began with.
    pub inputs: Set<nat>,
}

/// The replicas that have not crashed.
pub open spec fn live(s: QpState) -> Set<Id> {
    s.replicas.difference(s.crashed)
}

/// Proposal `x` ranks below proposal `y`: lower priority, or equal priority and a
/// lower proposer id. A proposal is identified by its proposer within a round, so
/// this is a strict total order on a round's proposals.
pub open spec fn lt(prio: Map<Id, nat>, x: Id, y: Id) -> bool {
    prio[x] < prio[y] || (prio[x] == prio[y] && x.0 < y.0)
}

/// `b` is the best proposal in `s`: it is in `s` and every other one ranks below it.
pub open spec fn is_best(prio: Map<Id, nat>, s: Set<Id>, b: Id) -> bool {
    &&& s.contains(b)
    &&& forall|y: Id| #[trigger] s.contains(y) && y != b ==> lt(prio, y, b)
}

/// The best proposal in `s`. Meaningful for a non-empty `s`, where it
/// exists and is unique ([`crate::quepaxa::proofs::agreement::lemma_best_exists`],
/// [`crate::quepaxa::proofs::agreement::lemma_best_is_unique`]).
pub open spec fn best(prio: Map<Id, nat>, s: Set<Id>) -> Id {
    choose|b: Id| is_best(prio, s, b)
}

/// What a replica's `tcast 2` hands it: the union, over the majority it heard from,
/// of what each of them received in `tcast 1`.
pub open spec fn e_set(
    l: Set<Id>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    i: Id,
) -> Set<Id> {
    l.filter(|x: Id| exists|j: Id| #[trigger] heard2[i].contains(j) && heard1[j].contains(x))
}

/// The set `tcast 2` guarantees every replica's `E` contains: the `tcast 1` set of
/// the replica `i` was relayed.
pub open spec fn pp_set(heard1: Map<Id, Set<Id>>, relay2: Map<Id, Id>, i: Id) -> Set<Id> {
    heard1[relay2[i]]
}

/// What a replica's `tcast 3` hands it: the union, over the majority it heard from,
/// of the sets `tcast 2` relayed to them.
pub open spec fn c_set(
    l: Set<Id>,
    heard1: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    heard3: Map<Id, Set<Id>>,
    i: Id,
) -> Set<Id> {
    l.filter(
        |x: Id|
            exists|j: Id| #[trigger] heard3[i].contains(j) && pp_set(heard1, relay2, j).contains(x),
    )
}

/// The set `tcast 3` guarantees every replica's `C` contains.
pub open spec fn u_set(
    heard1: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
    i: Id,
) -> Set<Id> {
    pp_set(heard1, relay2, relay3[i])
}

/// A round's witnesses satisfy `tcast`'s two guarantees for the live replicas `l`
/// of a cluster of `n`.
///
/// Every live replica hears from a majority of live replicas in each of the three
/// steps; the set relayed in `tcast 2` is inside every live replica's `E`; the set
/// relayed in `tcast 3` is inside every live replica's `C`.
pub open spec fn round_ok(
    n: nat,
    l: Set<Id>,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
) -> bool {
    &&& forall|i: Id|
        #[trigger] l.contains(i) ==> {
            &&& prio.contains_key(i)
            &&& heard1.contains_key(i)
            &&& heard2.contains_key(i)
            &&& heard3.contains_key(i)
            &&& relay2.contains_key(i)
            &&& relay3.contains_key(i)
        }
    // The quantifiers below trigger on the lookup they constrain and not on
    // `l.contains(i)`, because a conclusion that mentions `l.contains(relay2[i])`
    // would otherwise match its own trigger and the solver would chase relays forever.
    //
    // tcast 1: each replica hears from a majority of the live replicas.
    &&& forall|i: Id|
        l.contains(i) ==> #[trigger] heard1[i].subset_of(l) && is_majority(n, heard1[i])
    // tcast 2: a majority of the live replicas, and a relay that is one of them...
    &&& forall|i: Id|
        l.contains(i) ==> #[trigger] heard2[i].subset_of(l) && is_majority(n, heard2[i])
    &&& forall|i: Id| l.contains(i) ==> l.contains(#[trigger] relay2[i])
    // ...whose set is inside everyone's E.
    &&& forall|i: Id, m: Id|
        l.contains(i) && l.contains(m) ==> #[trigger] pp_set(heard1, relay2, i).subset_of(
            e_set(l, heard1, heard2, m),
        )
    // tcast 3: likewise, a majority and a relay...
    &&& forall|i: Id|
        l.contains(i) ==> #[trigger] heard3[i].subset_of(l) && is_majority(n, heard3[i])
    &&& forall|i: Id| l.contains(i) ==> l.contains(#[trigger] relay3[i])
    // ...whose set is inside everyone's C.
    &&& forall|i: Id, m: Id|
        l.contains(i) && l.contains(m) ==> #[trigger] u_set(heard1, relay2, relay3, i).subset_of(
            c_set(l, heard1, relay2, heard3, m),
        )
}

/// The two kinds of step.
pub enum QpStep {
    /// A replica crashes. At most a minority of the replicas may.
    Crash { node: Id },
    /// A round: every live replica proposes, the three `tcast` steps run, and every
    /// live replica adopts and possibly decides. The fields are the witnesses
    /// [`round_ok`] constrains.
    Round {
        prio: Map<Id, nat>,
        heard1: Map<Id, Set<Id>>,
        heard2: Map<Id, Set<Id>>,
        heard3: Map<Id, Set<Id>>,
        relay2: Map<Id, Id>,
        relay3: Map<Id, Id>,
    },
}

/// The replicas that decide in the round: those whose best existing proposal is
/// also their best universal one.
pub open spec fn deciders(
    s: QpState,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
) -> Set<Id> {
    live(s).filter(
        |i: Id|
            best(prio, e_set(live(s), heard1, heard2, i)) == best(
                prio,
                u_set(heard1, relay2, relay3, i),
            ),
    )
}

/// A crash step.
pub open spec fn qp_crash(pre: QpState, post: QpState, node: Id) -> bool {
    &&& pre.replicas.contains(node)
    &&& !pre.crashed.contains(node)
    // A minority only: with `n` replicas, fewer than half may crash, which is what
    // leaves a majority alive to hear from.
    &&& 2 * (pre.crashed.len() + 1) < pre.replicas.len()
    &&& post == (QpState { crashed: pre.crashed.insert(node), ..pre })
}

/// A round step.
pub open spec fn qp_round(
    pre: QpState,
    post: QpState,
    prio: Map<Id, nat>,
    heard1: Map<Id, Set<Id>>,
    heard2: Map<Id, Set<Id>>,
    heard3: Map<Id, Set<Id>>,
    relay2: Map<Id, Id>,
    relay3: Map<Id, Id>,
) -> bool {
    &&& round_ok(pre.replicas.len(), live(pre), prio, heard1, heard2, heard3, relay2, relay3)
    &&& post.replicas == pre.replicas
    &&& post.crashed == pre.crashed
    &&& post.inputs == pre.inputs
    // A live replica prefers the value of the best common proposal; a crashed
    // one is left as it was.
    &&& post.pref.dom() == pre.pref.dom()
    &&& forall|i: Id|
        #[trigger] pre.pref.dom().contains(i) ==> post.pref[i] == if live(pre).contains(i) {
            pre.pref[best(prio, c_set(live(pre), heard1, relay2, heard3, i))]
        } else {
            pre.pref[i]
        }
    // A replica that decides takes the value of its best universal proposal; one
    // that has decided keeps what it decided.
    &&& post.decided.dom() == pre.decided.dom().union(
        deciders(pre, prio, heard1, heard2, relay2, relay3),
    )
    &&& forall|i: Id|
        #[trigger] post.decided.dom().contains(i) ==> post.decided[i] == if pre.decided.dom().contains(
            i,
        ) {
            pre.decided[i]
        } else {
            pre.pref[best(prio, u_set(heard1, relay2, relay3, i))]
        }
}

/// `label` is an allowed step from `pre` to `post`.
pub open spec fn qp_step(pre: QpState, post: QpState, label: QpStep) -> bool {
    match label {
        QpStep::Crash { node } => qp_crash(pre, post, node),
        QpStep::Round { prio, heard1, heard2, heard3, relay2, relay3 } => qp_round(
            pre,
            post,
            prio,
            heard1,
            heard2,
            heard3,
            relay2,
            relay3,
        ),
    }
}

/// Some step takes `pre` to `post`.
pub open spec fn qp_next(pre: QpState, post: QpState) -> bool {
    exists|label: QpStep| #[trigger] qp_step(pre, post, label)
}

/// The initial states of a cluster of `replicas`: nobody has crashed or decided,
/// and every replica prefers some value, which is then an input.
pub open spec fn qp_init(replicas: Set<Id>, s: QpState) -> bool {
    &&& replicas.len() > 0
    &&& s.replicas == replicas
    &&& s.pref.dom() == replicas
    &&& s.crashed == Set::<Id>::empty()
    &&& s.decided == Map::<Id, nat>::empty()
    &&& forall|v: nat|
        #[trigger] s.inputs.contains(v) <==> exists|i: Id| replicas.contains(i) && s.pref[i] == v
}

/// `tr` is a finite execution.
pub open spec fn qp_execution(replicas: Set<Id>, tr: Seq<QpState>) -> bool {
    &&& tr.len() > 0
    &&& qp_init(replicas, tr[0])
    &&& forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> qp_next(tr[i], tr[i + 1])
}

/// `s` is reachable in a cluster of `replicas`.
pub open spec fn qp_reachable(replicas: Set<Id>, s: QpState) -> bool {
    exists|tr: Seq<QpState>| qp_execution(replicas, tr) && tr[tr.len() - 1] == s
}

/// The abstract algorithm as a [`Protocol`](crate::protocol::Protocol). The
/// configuration is the replica set.
pub struct QuePaxaAbstract;

impl crate::protocol::Protocol for QuePaxaAbstract {
    type Config = Set<Id>;
    type State = QpState;
    type Step = QpStep;

    open spec fn init(cfg: Set<Id>, s: QpState) -> bool {
        qp_init(cfg, s)
    }

    open spec fn step(pre: QpState, post: QpState, label: QpStep) -> bool {
        qp_step(pre, post, label)
    }
}

} // verus!
