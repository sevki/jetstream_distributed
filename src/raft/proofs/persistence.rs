//! **The induction's second step: the voter still held it when it voted.**
//!
//! # What was in the way
//!
//! [`crate::raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`]
//! (C48) says an entry survives a run whenever every leader replicating to its
//! holder already agrees with it at that index. Its hypothesis is a quantifier
//! **over steps**:
//!
//! ```text
//! forall|t| a <= t < b ==> replication_agrees_at(tr[t], labels[t], n, i)
//! ```
//!
//! and that is not the shape Leader Completeness's induction hypothesis has.
//! The induction knows something about **leaders of terms**, not about steps: *every
//! leader of a term between the commit and the election holds the entry*. Between
//! those two forms sat a gap that no theorem here had crossed, and the roadmap
//! crossed it in prose by saying the hypothesis "is the induction hypothesis at
//! the intervening terms" — true, and not a translation.
//!
//! This module is the translation. It is four facts, and the first two are the
//! ones that make it work.
//!
//! # A commit quorum is at or past the commit's own term
//!
//! [`theorem_a_commit_quorum_is_at_or_past_its_term`]. This is the fact that
//! bounds *which* leaders the induction has to worry about, and it is short:
//!
//! * `tr_advance_commit`'s figure-8 guard says the last entry of the committed
//!   prefix carries the leader's own term `T`;
//! * a member of the quorum holds that prefix, so it holds an entry of term `T`;
//! * [`terms_within`] says no entry's term exceeds its holder's `current_term`.
//!
//! So every member of the quorum is already at term `T` or beyond. Terms never
//! fall ([`theorem_a_term_never_falls_across_a_run`]), so it stays that way.
//!
//! # Therefore only a leader at the holder's own term can ever touch it again
//!
//! [`theorem_a_replicating_leader_shares_the_followers_term`]. `tr_append_entries`
//! is the only transition that can shorten a log, and its guard requires the
//! leader's `current_term` to **equal** the follower's.
//!
//! That is what turns C48's quantifier over steps into a quantifier over
//! leaders: the steps that could hurt are driven by leaders at one known term.
//!
//! # The hypothesis, in the induction's own words — and bounded on both sides
//!
//! [`replicators_hold`] is the tight form: *every standing leader that could
//! replicate to `n` right now holds `e` at `i`*. No term bound appears in it,
//! because persistence does not need one.
//!
//! [`leaders_within_hold`] is the form the induction supplies: Leader
//! Completeness over the **closed range** `[t0, t1]`.
//! [`lemma_a_bounded_hypothesis_covers_the_replicators`] is where they meet.
//!
//! The upper bound is there because `@codex` found that the first version of
//! this module did not have one, and that an unbounded hypothesis is not what
//! strong induction supplies — see [`replicators_hold`] for the finding, which
//! is the most interesting thing in the module.
//!
//! [`theorem_an_entry_survives_leaders_that_could_reach_it`] consumes the tight
//! form and gives C48's conclusion. [`theorem_a_commit_quorum_still_holds_it`]
//! composes that with the commit-time quorum: **a member of the quorum that
//! committed an entry still holds it at any later point, provided every leader of
//! a term between the commit's and `t1` held it.**
//!
//! # What is left
//!
//! The induction itself, and now only the induction. Its three steps are:
//!
//! 1. a quorum held the entry at commit time —
//!    [`crate::raft::proofs::commit::theorem_a_commit_was_on_a_quorum`] (C45);
//! 2. a member of that quorum still held it when it voted — this module, with the
//!    hypothesis in the form the induction supplies, over a closed range of
//!    terms whose upper endpoint the induction still owes (see
//!    [`theorem_a_commit_quorum_still_holds_it`]);
//! 3. the winner's own log dominates that voter's —
//!    [`crate::raft::proofs::summary::theorem_the_new_leaders_log_dominates_a_judged_voter`]
//!    (C52).
//!
//! All three now speak about the same objects: an entry, an index, a term, and a
//! log. Assembling them is a strong induction over terms and nothing else. That
//! is a claim about shape, not a claim that it is proved — it is not.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::proofs::commit::*;
use crate::raft::proofs::election::*;
use crate::raft::proofs::history::*;
use crate::raft::proofs::summary::*;
use crate::raft::proofs::terms::*;
use crate::raft::proofs::votes::*;

verus! {

// ---------------------------------------------------------------------------
// Terms, across a run
// ---------------------------------------------------------------------------

/// **No server's term ever falls, across a whole run.**
///
/// [`theorem_term_monotone_step`] is about one step. Everything below needs it
/// about a stretch of the run, because the fact being carried — *this server is
/// at term `T` or beyond* — is what stays true while the entry is at risk.
pub proof fn theorem_a_term_never_falls_across_a_run(
    tr: Seq<Cluster>,
    a: int,
    b: int,
    n: ServerId,
)
    requires
        raft_execution(tr),
        0 <= a <= b < tr.len(),
        tr[a].servers.contains_key(n),
    ensures
        tr[b].servers.contains_key(n),
        tr[b].servers[n].current_term >= tr[a].servers[n].current_term,
    decreases b - a,
{
    if a < b {
        theorem_a_term_never_falls_across_a_run(tr, a, b - 1, n);

        // Bound into plain variables before the `choose`: trigger inference for
        // `choose|s| raft_step(p, q, s)` cannot see through sequence indexing.
        // `lemma_raft_next_preserves_hist` documents the same hazard.
        let p = tr[b - 1];
        let q = tr[b];
        assert(raft_next(tr[b - 1], tr[b - 1 + 1]));
        assert(tr[b - 1 + 1] == tr[b]);
        assert(raft_next(p, q));
        let s = choose|s: RaftStep| raft_step(p, q, s);
        theorem_term_monotone_step(p, q, s, n);
    }
}

// ---------------------------------------------------------------------------
// Which leaders can reach a commit quorum at all
// ---------------------------------------------------------------------------

/// **Every member of a commit's quorum is already at the committing leader's
/// term, or past it.**
///
/// Three lines, and it is the fact that bounds the induction's work. The
/// figure-8 guard on [`tr_advance_commit`] says the last entry of the committed
/// prefix carries the leader's own term; a quorum member holds that prefix, so it
/// holds an entry of that term; and [`terms_within`] says no entry's term exceeds
/// its holder's `current_term`.
///
/// Note which guard is doing the work. Without figure 8's restriction — commit
/// only when the newest entry is of your own term — the committed prefix could
/// end in an *old* term and this theorem would be false, and with it the whole
/// reduction below. The restriction is usually explained as ruling out one
/// counterexample; here it is load-bearing for the shape of the argument.
pub proof fn theorem_a_commit_quorum_is_at_or_past_its_term(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
    m: ServerId,
)
    requires
        raft_term_inv(pre),
        tr_advance_commit(pre, post, n, upto),
        replicated_on(pre, pre.servers[n].log, upto).contains(m),
    ensures
        pre.servers.contains_key(m),
        pre.servers[m].current_term >= pre.servers[n].current_term,
{
    // `replicated_on` is a filter, so membership unfolds to the prefix.
    assert(has_prefix(pre.servers[m].log, pre.servers[n].log, upto));

    let k = (upto - 1) as nat;
    assert(upto > 0);
    assert(pre.servers[m].log[k as int] == pre.servers[n].log[k as int]);
    assert(pre.servers[n].log[k as int].term == pre.servers[n].current_term);
    assert(terms_within(pre.servers[m].log, pre.servers[m].current_term));
    assert(k < pre.servers[m].log.len());
    assert(pre.servers[m].log[k as int].term <= pre.servers[m].current_term);
}

/// **A replicating leader is at the follower's own term.**
///
/// [`tr_append_entries`] is the only transition that can shorten a log — that is
/// [`step_replicates_to`]'s whole purpose — and its guard requires the leader's
/// `current_term` to *equal* the follower's.
///
/// This is the step that changes the shape of the argument: C48 quantifies over
/// *steps*, the induction hypothesis is about *leaders*, and this says the steps
/// that could hurt are driven by leaders at one known term — the holder's. What
/// range of terms that is, is [`theorem_a_commit_quorum_is_at_or_past_its_term`]'s
/// business and the induction's, not this lemma's.
pub proof fn theorem_a_replicating_leader_shares_the_followers_term(
    pre: Cluster,
    post: Cluster,
    s: RaftStep,
    n: ServerId,
)
    requires
        raft_step(pre, post, s),
        pre.servers.contains_key(n),
        step_replicates_to(s, n),
    ensures
        pre.servers.contains_key(replicating_leader(s)),
        is_leader(pre.servers[replicating_leader(s)]),
        pre.servers[replicating_leader(s)].current_term == pre.servers[n].current_term,
{
    match s {
        RaftStep::AppendEntries { leader, follower, prefix: _ } => {
            assert(follower == n);
            assert(replicating_leader(s) == leader);
        },
        _ => {
            // `step_replicates_to` is a match on the one variant, so this arm
            // contradicts the hypothesis rather than needing a case of its own.
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------------
// The hypothesis, in the induction's own words
// ---------------------------------------------------------------------------

/// **Every standing leader that could replicate to `n` *right now* holds `e` at
/// index `i`.**
///
/// The tight form, and the only one the persistence argument actually needs.
/// "Could replicate to `n`" is `current_term == n`'s: that is
/// [`tr_append_entries`]' guard, and
/// [`theorem_a_replicating_leader_shares_the_followers_term`] is the proof that
/// nothing else can shorten `n`'s log.
///
/// It says nothing about servers that *have* led and stepped down. It does not
/// need to: a demoted leader cannot replicate, so it cannot take the entry from
/// anyone.
///
/// # This replaced an unbounded predicate, and the difference is the whole point
///
/// The first version of this module quantified over every standing leader of a
/// term **at or past** `t0`, with no upper bound, and claimed that was the
/// strong induction's hypothesis. `@codex` found that it is not, and the finding
/// is exact: strong induction on the election's term `T` supplies Leader
/// Completeness for terms *below* `T`, and an unbounded predicate demands it for
/// terms **above** `T` as well.
///
/// Those leaders exist. Nothing in this model orders terms cluster-wide —
/// [`tr_grant_vote`] only requires the request's term to be at least the voter's
/// own — so a leader of some far higher term can be running elsewhere while a
/// delayed campaign at `T` is still collecting votes. Such a leader is *harmless*
/// to the entry, precisely because it cannot replicate to a voter at a lower
/// term. But the old predicate still demanded that it hold `e`, so C54 could not
/// have been discharged from the induction hypothesis without assuming Leader
/// Completeness for terms the induction had not reached.
///
/// A hypothesis that is stronger than the argument needs is not a safe
/// over-approximation when the hypothesis is what someone else has to supply.
pub open spec fn replicators_hold(c: Cluster, n: ServerId, i: nat, e: Entry) -> bool {
    forall|m: ServerId|
        #![trigger c.servers[m]]
        c.servers.contains_key(m) && is_leader(c.servers[m]) && c.servers[m].current_term
            == c.servers[n].current_term ==> i < c.servers[m].log.len()
            && c.servers[m].log[i as int] == e
}

/// **Leader Completeness over a closed range of terms**, as a predicate on one
/// state — the form the induction supplies.
///
/// Both bounds are load-bearing. `t0` is the commit's term, and
/// [`theorem_a_commit_quorum_is_at_or_past_its_term`] is why the holder is at or
/// past it. `t1` is the election's term, and it is there because strong
/// induction reaches *up to* a term and no further: see
/// [`replicators_hold`] for the finding that put it there.
pub open spec fn leaders_within_hold(c: Cluster, t0: Term, t1: Term, i: nat, e: Entry) -> bool {
    forall|m: ServerId|
        #![trigger c.servers[m]]
        c.servers.contains_key(m) && is_leader(c.servers[m]) && t0 <= c.servers[m].current_term <= t1
            ==> i < c.servers[m].log.len() && c.servers[m].log[i as int] == e
}

/// **A hypothesis bounded by `[t0, t1]` covers every leader that could reach a
/// holder whose own term lies in that range.**
///
/// One line, and it is where the two forms meet: a leader that can replicate to
/// `n` has `n`'s term, so if `n`'s term is in range then so is that leader's.
pub proof fn lemma_a_bounded_hypothesis_covers_the_replicators(
    c: Cluster,
    n: ServerId,
    t0: Term,
    t1: Term,
    i: nat,
    e: Entry,
)
    requires
        c.servers.contains_key(n),
        t0 <= c.servers[n].current_term,
        c.servers[n].current_term <= t1,
        leaders_within_hold(c, t0, t1, i, e),
    ensures
        replicators_hold(c, n, i, e),
{
}

/// **An entry survives on a server for as long as every leader that could reach
/// it holds it.**
///
/// C48 with its hypothesis translated: a quantifier over the leaders that could
/// write to the holder, in place of a quantifier over steps. The proof is the
/// same recursion, with
/// [`theorem_a_replicating_leader_shares_the_followers_term`] discharging
/// [`replication_agrees_at`] at each step — which it can, because the entry is
/// still there one step earlier (the recursion) and the replicating leader holds
/// it too (the hypothesis).
///
/// No term bound appears here at all, which is the shape the fix produced: the
/// bounds belong to what the *induction* can supply, not to what persistence
/// needs, and mixing the two is what made the first version's hypothesis
/// undischargeable.
pub proof fn theorem_an_entry_survives_leaders_that_could_reach_it(
    tr: Seq<Cluster>,
    labels: Seq<RaftStep>,
    a: int,
    b: int,
    n: ServerId,
    i: nat,
    e: Entry,
)
    requires
        raft_labelled_execution(tr, labels),
        0 <= a <= b < tr.len(),
        tr[a].servers.contains_key(n),
        i < tr[a].servers[n].log.len(),
        tr[a].servers[n].log[i as int] == e,
        forall|t: int| a <= t < b ==> #[trigger] replicators_hold(tr[t], n, i, e),
    ensures
        tr[b].servers.contains_key(n),
        i < tr[b].servers[n].log.len(),
        tr[b].servers[n].log[i as int] == e,
    decreases b - a,
{
    if a < b {
        theorem_an_entry_survives_leaders_that_could_reach_it(tr, labels, a, b - 1, n, i, e);
        lemma_a_labelled_execution_is_an_execution(tr, labels);
        lemma_raft_execution_hist_inv(tr, b - 1);

        assert(replicators_hold(tr[b - 1], n, i, e));
        assert(raft_step(tr[b - 1], tr[b - 1 + 1], labels[b - 1]));
        assert(tr[b - 1 + 1] == tr[b]);

        assert(replication_agrees_at(tr[b - 1], labels[b - 1], n, i)) by {
            if step_replicates_to(labels[b - 1], n) {
                theorem_a_replicating_leader_shares_the_followers_term(
                    tr[b - 1],
                    tr[b],
                    labels[b - 1],
                    n,
                );
                let l = replicating_leader(labels[b - 1]);
                // `l` is a standing leader at `n`'s own term, so the hypothesis
                // reaches it — and `n` still holds `e` one step of the recursion
                // ago.
                assert(tr[b - 1].servers[l].log[i as int] == e);
                assert(tr[b - 1].servers[n].log[i as int] == e);
            }
        }

        theorem_an_agreed_entry_survives_any_step(tr[b - 1], tr[b], labels[b - 1], n, i);
    }
}

// ---------------------------------------------------------------------------
// Composed with the commit
// ---------------------------------------------------------------------------

/// **A member of the quorum that committed an entry still holds it at any later
/// point, provided every leader of a term between the commit's and `t1` held
/// it.**
///
/// The induction's steps 1 and 2 joined, and the point of the module. The
/// hypothesis is [`leaders_within_hold`] over `[T, t1]`, where `T` is the
/// committing leader's own term — which is to say, Leader Completeness at the
/// terms between this commit and whatever comes next.
///
/// # Where each bound comes from, and why both are in the signature
///
/// * the **lower** bound is established at the window's start:
///   [`theorem_a_commit_quorum_is_at_or_past_its_term`] puts the quorum at `T` or
///   beyond, and terms never fall;
/// * the **upper** bound is established at the window's **end**, by
///   `tr[later].servers[m].current_term <= t1`, and then holds backwards through
///   the window for the same reason — terms never fall.
///
/// That asymmetry is worth naming. In the use the induction will make of this,
/// the window ends when the voter grants its vote in term `t1`, and
/// [`tr_grant_vote`] requires the request's term to be at least the voter's own —
/// so the voter is at `t1` or below *then*, and monotonicity carries it back over
/// the whole window. The upper bound is not an extra assumption about the run; it
/// is the vote.
///
/// # What it does not say
///
/// It does not say the entry survives *unconditionally*, and the hypothesis is
/// not decoration: an intervening leader that does **not** hold the entry can and
/// will truncate it away, which is faithful Raft and is precisely what the
/// election restriction exists to make impossible. Read
/// `crate::raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`
/// on why a conditional persistence theorem is the honest kind.
///
/// Nor does it say the induction can discharge the hypothesis. It needs Leader
/// Completeness on the *closed* range `[T, t1]`, and the `t1` endpoint is the
/// interesting one: a leader of `t1` may already exist while this voter has not
/// yet voted in `t1`, because winning `t1` needs *a* quorum and not this one. So
/// the induction will have to establish its case at `t1` before it may use this
/// theorem at `t1` — or restrict the window to end strictly before any leader of
/// `t1` exists. That is a real obligation, it is stated here rather than in a
/// paragraph elsewhere, and this PR does not discharge it.
pub proof fn theorem_a_commit_quorum_still_holds_it(
    tr: Seq<Cluster>,
    labels: Seq<RaftStep>,
    at: int,
    later: int,
    n: ServerId,
    upto: nat,
    m: ServerId,
    i: nat,
    t1: Term,
)
    requires
        raft_labelled_execution(tr, labels),
        0 <= at <= later,
        later < tr.len(),
        at < tr.len() - 1,
        labels[at] == (RaftStep::AdvanceCommit { server: n, upto: upto }),
        replicated_on(tr[at], tr[at].servers[n].log, upto).contains(m),
        i < upto,
        tr[later].servers.contains_key(m),
        tr[later].servers[m].current_term <= t1,
        forall|t: int|
            at <= t < later ==> #[trigger] leaders_within_hold(
                tr[t],
                tr[at].servers[n].current_term,
                t1,
                i,
                tr[at].servers[n].log[i as int],
            ),
    ensures
        tr[later].servers.contains_key(m),
        i < tr[later].servers[m].log.len(),
        tr[later].servers[m].log[i as int] == tr[at].servers[n].log[i as int],
{
    lemma_a_labelled_execution_is_an_execution(tr, labels);
    lemma_raft_execution_term_inv(tr, at);
    assert(raft_step(tr[at], tr[at + 1], labels[at]));
    assert(tr_advance_commit(tr[at], tr[at + 1], n, upto));

    let e = tr[at].servers[n].log[i as int];
    let t0 = tr[at].servers[n].current_term;

    theorem_a_commit_quorum_is_at_or_past_its_term(tr[at], tr[at + 1], n, upto, m);
    assert(has_prefix(tr[at].servers[m].log, tr[at].servers[n].log, upto));
    assert(i < upto);
    assert(tr[at].servers[m].log[i as int] == e);

    // The holder's term is inside `[t0, t1]` at every state of the window: at or
    // above `t0` because it was at the commit and terms never fall, and at or
    // below `t1` because it is at `later` and terms never fall.
    assert forall|t: int|
        #![trigger replicators_hold(tr[t], m, i, e)]
        at <= t < later implies replicators_hold(tr[t], m, i, e) by {
        theorem_a_term_never_falls_across_a_run(tr, at, t, m);
        theorem_a_term_never_falls_across_a_run(tr, t, later, m);
        assert(leaders_within_hold(tr[t], t0, t1, i, e));
        lemma_a_bounded_hypothesis_covers_the_replicators(tr[t], m, t0, t1, i, e);
    }

    theorem_an_entry_survives_leaders_that_could_reach_it(tr, labels, at, later, m, i, e);
}

} // verus!
