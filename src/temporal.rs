//! A small temporal logic of actions, enough to state and prove liveness.
//!
//! Everything else in this crate proves **safety**: a bad state is not
//! reachable, which is a statement about each finite prefix of a run. A
//! liveness claim — *this message is eventually delivered* — is a statement
//! about the whole infinite run, and it is false of a machine that is merely
//! *allowed* to do the right thing: a scheduler that never picks the one process
//! that could make progress satisfies every safety property and delivers nothing.
//! What closes the gap is a **fairness assumption**, and it has to be stated,
//! because a liveness theorem is only as strong as the assumption beneath it.
//!
//! This is the idiom of [verus-tla](https://github.com/anvil-verifier/verus-tla)
//! (Anvil's embedding of Lamport's TLA in Verus): an execution is a function from
//! step number to state, `leads_to` and weak fairness are quantifiers over its
//! suffixes, and the one proof rule that turns an *action* into *progress* is
//! WF1. It is rebuilt here, rather than depended on, for the same reason the rest
//! of the crate has no dependencies the proofs do not need: `verus
//! --crate-type=lib src/lib.rs` links `vstd` and nothing else. The definitions
//! are the standard ones, specialised to a state-predicate rather than a
//! temporal-predicate calculus, which is all the proofs here use.
//!
//! # What is here
//!
//! * [`runs`] — an infinite execution of a machine: an initial state, and every
//!   consecutive pair a step. Machines here include a stutter step, so "nothing
//!   is enabled" is an infinite run and not a deadlock the logic cannot speak of.
//! * [`leads_to`] — `p ~> q`: whenever `p` holds, `q` holds then or later.
//! * [`weakly_fair`] — `WF(A)`: an action that stays enabled is eventually taken.
//! * [`lemma_wf1`] — if `p` can only be left by `A` firing, and `A` is enabled
//!   while `p` holds, then under `WF(A)`, `p ~> q`.
//! * [`lemma_leads_to_trans`], [`lemma_leads_to_cases`] — chaining, and splitting
//!   on cases.
//!
//! Every rule is *proved*, not assumed. Nothing in this file is an axiom.
#![allow(unused_imports)]

use vstd::prelude::*;

verus! {

/// An execution is an infinite sequence of states: step `i` is `ex(i)`.
///
/// `ex` is an execution of the machine `(init, next)`.
pub open spec fn runs<S>(
    ex: spec_fn(nat) -> S,
    init: spec_fn(S) -> bool,
    next: spec_fn(S, S) -> bool,
) -> bool {
    &&& init(ex(0))
    &&& forall|i: nat| #[trigger] next(ex(i), ex(i + 1))
}

/// `p ~> q`: from every point at which `p` holds, `q` holds at that point or a
/// later one.
pub open spec fn leads_to<S>(ex: spec_fn(nat) -> S, p: spec_fn(S) -> bool, q: spec_fn(S) -> bool) -> bool {
    forall|i: nat| #[trigger] p(ex(i)) ==> exists|j: nat| i <= j && #[trigger] q(ex(j))
}

/// Weak fairness of the action `taken`, which is enabled where `enabled` holds:
/// if the action is enabled at every step from `i` onwards, it is taken at some
/// step from `i` onwards.
///
/// This is `WF(A)` — `[]<>(A taken) \/ []<>(~enabled)` — said as a quantifier. An
/// action that is enabled only now and then is owed nothing, which is the whole
/// of what it assumes.
pub open spec fn weakly_fair<S>(
    ex: spec_fn(nat) -> S,
    enabled: spec_fn(S) -> bool,
    taken: spec_fn(S, S) -> bool,
) -> bool {
    forall|i: nat|
        #[trigger] enabled_from(ex, enabled, i) ==> exists|j: nat|
            i <= j && #[trigger] taken(ex(j), ex(j + 1))
}

/// `enabled` holds at every step from `i` onwards.
pub open spec fn enabled_from<S>(ex: spec_fn(nat) -> S, enabled: spec_fn(S) -> bool, i: nat) -> bool {
    forall|j: nat| i <= j ==> #[trigger] enabled(ex(j))
}

/// If `p` holds at `i`, never `q` from there on, and `p` can only be left by `q`
/// or stay, then `p` holds at every later step.
proof fn lemma_p_persists<S>(
    ex: spec_fn(nat) -> S,
    inv: spec_fn(S) -> bool,
    next: spec_fn(S, S) -> bool,
    p: spec_fn(S) -> bool,
    q: spec_fn(S) -> bool,
    i: nat,
    n: nat,
)
    requires
        forall|k: nat| #[trigger] inv(ex(k)),
        forall|k: nat| #[trigger] next(ex(k), ex(k + 1)),
        forall|s: S, t: S| inv(s) && inv(t) && p(s) && #[trigger] next(s, t) ==> p(t) || q(t),
        p(ex(i)),
        forall|j: nat| i <= j ==> !#[trigger] q(ex(j)),
    ensures
        p(ex(i + n)),
    decreases n,
{
    if n > 0 {
        lemma_p_persists(ex, inv, next, p, q, i, (n - 1) as nat);
        let k = (i + (n - 1) as nat) as nat;
        assert(k + 1 == i + n);
        assert(next(ex(k), ex(k + 1)));
        assert(inv(ex(k)));
        assert(inv(ex(k + 1)));
        assert(!q(ex(k + 1)));
    }
}

/// **WF1.** `p ~> q`, provided
///
/// * a step from a `p`-state either stays in `p` or reaches `q`;
/// * the action `taken`, when it fires from a `p`-state, reaches `q`;
/// * `taken` is enabled in every `p`-state; and
/// * `taken` is weakly fair.
///
/// `inv` is an invariant of the machine that the step conditions may use; it is
/// a hypothesis here and is established by the caller for every state of the
/// execution.
pub proof fn lemma_wf1<S>(
    ex: spec_fn(nat) -> S,
    inv: spec_fn(S) -> bool,
    next: spec_fn(S, S) -> bool,
    enabled: spec_fn(S) -> bool,
    taken: spec_fn(S, S) -> bool,
    p: spec_fn(S) -> bool,
    q: spec_fn(S) -> bool,
)
    requires
        forall|k: nat| #[trigger] inv(ex(k)),
        forall|k: nat| #[trigger] next(ex(k), ex(k + 1)),
        weakly_fair(ex, enabled, taken),
        forall|s: S, t: S| inv(s) && inv(t) && p(s) && #[trigger] next(s, t) ==> p(t) || q(t),
        forall|s: S, t: S|
            inv(s) && inv(t) && p(s) && #[trigger] next(s, t) && taken(s, t) ==> q(t),
        forall|s: S| inv(s) && #[trigger] p(s) ==> enabled(s),
    ensures
        leads_to(ex, p, q),
{
    assert forall|i: nat| #[trigger] p(ex(i)) implies exists|j: nat| i <= j && #[trigger] q(ex(j)) by {
        if !(exists|j: nat| i <= j && #[trigger] q(ex(j))) {
            assert forall|j: nat| i <= j implies !#[trigger] q(ex(j)) by {}
            assert forall|j: nat| i <= j implies #[trigger] enabled(ex(j)) by {
                lemma_p_persists(ex, inv, next, p, q, i, (j - i) as nat);
                assert(i + (j - i) as nat == j);
                assert(inv(ex(j)));
                assert(p(ex(j)));
            }
            assert(enabled_from(ex, enabled, i));
            let j = choose|j: nat| i <= j && #[trigger] taken(ex(j), ex(j + 1));
            lemma_p_persists(ex, inv, next, p, q, i, (j - i) as nat);
            assert(i + (j - i) as nat == j);
            assert(inv(ex(j)));
            assert(p(ex(j)));
            assert(inv(ex(j + 1)));
            assert(next(ex(j), ex(j + 1)));
            assert(q(ex(j + 1)));
            assert(i <= j + 1);
        }
    }
}

/// `p ~> q` and `q ~> r` give `p ~> r`.
pub proof fn lemma_leads_to_trans<S>(
    ex: spec_fn(nat) -> S,
    p: spec_fn(S) -> bool,
    q: spec_fn(S) -> bool,
    r: spec_fn(S) -> bool,
)
    requires
        leads_to(ex, p, q),
        leads_to(ex, q, r),
    ensures
        leads_to(ex, p, r),
{
    assert forall|i: nat| #[trigger] p(ex(i)) implies exists|j: nat| i <= j && #[trigger] r(ex(j)) by {
        let j = choose|j: nat| i <= j && #[trigger] q(ex(j));
        let k = choose|k: nat| j <= k && #[trigger] r(ex(k));
    }
}

/// If every `p`-state is a `p1`-state or a `p2`-state, and each of those leads
/// to `q`, then `p ~> q`.
pub proof fn lemma_leads_to_cases<S>(
    ex: spec_fn(nat) -> S,
    p: spec_fn(S) -> bool,
    p1: spec_fn(S) -> bool,
    p2: spec_fn(S) -> bool,
    q: spec_fn(S) -> bool,
)
    requires
        forall|i: nat| #[trigger] p(ex(i)) ==> p1(ex(i)) || p2(ex(i)),
        leads_to(ex, p1, q),
        leads_to(ex, p2, q),
    ensures
        leads_to(ex, p, q),
{
    assert forall|i: nat| #[trigger] p(ex(i)) implies exists|j: nat| i <= j && #[trigger] q(ex(j)) by {
        if p1(ex(i)) {
            let j = choose|j: nat| i <= j && #[trigger] q(ex(j));
        } else {
            assert(p2(ex(i)));
            let j = choose|j: nat| i <= j && #[trigger] q(ex(j));
        }
    }
}

/// `p ~> q` where `p` implies `q`: trivially, at once.
pub proof fn lemma_leads_to_implies<S>(
    ex: spec_fn(nat) -> S,
    p: spec_fn(S) -> bool,
    q: spec_fn(S) -> bool,
)
    requires
        forall|i: nat| #[trigger] p(ex(i)) ==> q(ex(i)),
    ensures
        leads_to(ex, p, q),
{
    assert forall|i: nat| #[trigger] p(ex(i)) implies exists|j: nat| i <= j && #[trigger] q(ex(j)) by {
        assert(q(ex(i)));
    }
}

} // verus!
