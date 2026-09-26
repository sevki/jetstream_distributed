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
//! # Therefore only a leader of a term at or past `T` can ever touch it again
//!
//! [`theorem_only_a_leader_at_or_past_can_replicate`]. `tr_append_entries` is the
//! only transition that can shorten a log, and its guard requires the leader's
//! `current_term` to **equal** the follower's. A quorum member is at `T` or
//! beyond, so any leader that can replicate to it is too.
//!
//! That is what turns C48's quantifier over steps into a quantifier over
//! leaders, because it says the steps that could hurt are exactly the ones
//! driven by a leader the induction hypothesis already covers.
//!
//! # The hypothesis, in the induction's own words
//!
//! [`standing_leaders_from_hold`] — *every server that is now a leader of a term
//! at or past `t0` holds `e` at index `i`*. That is Leader Completeness
//! restricted to terms `>= t0`, written as a predicate on one state so it can be
//! quantified over a run.
//!
//! [`theorem_an_entry_survives_leaders_that_hold_it`] consumes it and gives
//! C48's conclusion. [`theorem_a_commit_quorum_still_holds_it`] composes that
//! with the commit-time quorum: **a member of the quorum that committed an entry
//! still holds it at any later point, provided every leader from the commit's
//! term onwards held it.**
//!
//! # What is left
//!
//! The induction itself, and now only the induction. Its three steps are:
//!
//! 1. a quorum held the entry at commit time —
//!    [`crate::raft::proofs::commit::theorem_a_commit_was_on_a_quorum`] (C45);
//! 2. a member of that quorum still held it when it voted — this module, with the
//!    hypothesis in the form the induction supplies;
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

/// **Only a standing leader at or past a server's own term can replicate to
/// it.**
///
/// [`tr_append_entries`] is the only transition that can shorten a log — that is
/// [`step_replicates_to`]'s whole purpose — and its guard requires the leader's
/// `current_term` to *equal* the follower's. So a server at term `t0` or beyond
/// can only be written to by a leader at `t0` or beyond.
///
/// This is the step that changes the shape of the argument: C48 quantifies over
/// *steps*, the induction hypothesis is about *leaders of terms*, and this says
/// the steps that could hurt are driven by exactly the leaders the hypothesis
/// covers.
pub proof fn theorem_only_a_leader_at_or_past_can_replicate(
    pre: Cluster,
    post: Cluster,
    s: RaftStep,
    n: ServerId,
    t0: Term,
)
    requires
        raft_step(pre, post, s),
        pre.servers.contains_key(n),
        pre.servers[n].current_term >= t0,
        step_replicates_to(s, n),
    ensures
        pre.servers.contains_key(replicating_leader(s)),
        is_leader(pre.servers[replicating_leader(s)]),
        pre.servers[replicating_leader(s)].current_term == pre.servers[n].current_term,
        pre.servers[replicating_leader(s)].current_term >= t0,
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

/// **Leader Completeness restricted to terms at or past `t0`**, as a predicate on
/// one state.
///
/// *Every server that is now a leader of a term at or past `t0` holds `e` at
/// index `i`.* This is what the strong induction over terms will have in hand
/// when it reaches term `t0`, and writing it as a predicate on a single state is
/// what lets it be quantified over a stretch of a run.
///
/// It says nothing about servers that *have* led such a term and stepped down.
/// It does not need to: a demoted leader cannot replicate, so it cannot take the
/// entry from anyone.
pub open spec fn standing_leaders_from_hold(c: Cluster, t0: Term, i: nat, e: Entry) -> bool {
    forall|m: ServerId|
        #![trigger c.servers[m]]
        c.servers.contains_key(m) && is_leader(c.servers[m]) && c.servers[m].current_term >= t0
            ==> i < c.servers[m].log.len() && c.servers[m].log[i as int] == e
}

/// **An entry survives on a server at term `t0` or beyond, for as long as every
/// leader from `t0` onwards holds it.**
///
/// C48 with its hypothesis translated: a quantifier over the leaders of a range
/// of terms in place of a quantifier over steps. The proof is the same recursion,
/// with [`theorem_only_a_leader_at_or_past_can_replicate`] discharging
/// [`replication_agrees_at`] at each step — which it can, because the entry is
/// still there one step earlier (the recursion) and the replicating leader holds
/// it too (the hypothesis).
///
/// The `t0` hypothesis on the *holder* is what makes the leader bound available:
/// without it, a leader of some term far below `t0` could be at the follower's
/// term and replicate freely, and nothing would constrain its log.
pub proof fn theorem_an_entry_survives_leaders_that_hold_it(
    tr: Seq<Cluster>,
    labels: Seq<RaftStep>,
    a: int,
    b: int,
    n: ServerId,
    i: nat,
    e: Entry,
    t0: Term,
)
    requires
        raft_labelled_execution(tr, labels),
        0 <= a <= b < tr.len(),
        tr[a].servers.contains_key(n),
        i < tr[a].servers[n].log.len(),
        tr[a].servers[n].log[i as int] == e,
        tr[a].servers[n].current_term >= t0,
        forall|t: int| a <= t < b ==> #[trigger] standing_leaders_from_hold(tr[t], t0, i, e),
    ensures
        tr[b].servers.contains_key(n),
        i < tr[b].servers[n].log.len(),
        tr[b].servers[n].log[i as int] == e,
    decreases b - a,
{
    if a < b {
        theorem_an_entry_survives_leaders_that_hold_it(tr, labels, a, b - 1, n, i, e, t0);
        lemma_a_labelled_execution_is_an_execution(tr, labels);
        lemma_raft_execution_hist_inv(tr, b - 1);
        theorem_a_term_never_falls_across_a_run(tr, a, b - 1, n);

        assert(standing_leaders_from_hold(tr[b - 1], t0, i, e));
        assert(raft_step(tr[b - 1], tr[b - 1 + 1], labels[b - 1]));
        assert(tr[b - 1 + 1] == tr[b]);

        assert(replication_agrees_at(tr[b - 1], labels[b - 1], n, i)) by {
            if step_replicates_to(labels[b - 1], n) {
                theorem_only_a_leader_at_or_past_can_replicate(
                    tr[b - 1],
                    tr[b],
                    labels[b - 1],
                    n,
                    t0,
                );
                let l = replicating_leader(labels[b - 1]);
                // The hypothesis at `l`: it is a standing leader at or past
                // `t0`, so it holds `e` at `i` — and so does `n`, one step of
                // the recursion ago.
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
/// point, provided every leader from the commit's term onwards held it.**
///
/// The induction's steps 1 and 2 joined, and the point of the module. The
/// hypothesis is [`standing_leaders_from_hold`] at the committing leader's own
/// term — which is to say, Leader Completeness at the terms *between* this commit
/// and whatever comes next.
///
/// So the induction's remaining job is exactly this: supply that hypothesis for
/// the terms it has already settled, and instantiate the quorum with the one
/// [`crate::raft::proofs::summary::theorem_the_new_leaders_log_dominates_a_judged_voter`]
/// meets.
///
/// # What it does not say
///
/// It does not say the entry survives *unconditionally*, and the hypothesis is
/// not decoration: an intervening leader that does **not** hold the entry can and
/// will truncate it away, which is faithful Raft and is precisely what the
/// election restriction exists to make impossible. Read
/// `crate::raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`
/// on why a conditional persistence theorem is the honest kind, and on the
/// earlier version of that comment which claimed necessity as well as
/// sufficiency.
pub proof fn theorem_a_commit_quorum_still_holds_it(
    tr: Seq<Cluster>,
    labels: Seq<RaftStep>,
    at: int,
    later: int,
    n: ServerId,
    upto: nat,
    m: ServerId,
    i: nat,
)
    requires
        raft_labelled_execution(tr, labels),
        0 <= at <= later,
        later < tr.len(),
        at < tr.len() - 1,
        labels[at] == (RaftStep::AdvanceCommit { server: n, upto: upto }),
        replicated_on(tr[at], tr[at].servers[n].log, upto).contains(m),
        i < upto,
        forall|t: int|
            at <= t < later ==> #[trigger] standing_leaders_from_hold(
                tr[t],
                tr[at].servers[n].current_term,
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

    theorem_an_entry_survives_leaders_that_hold_it(tr, labels, at, later, m, i, e, t0);
}

} // verus!
