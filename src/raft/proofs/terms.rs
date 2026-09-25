//! **The shape of a log's terms**, and the first half of the election
//! restriction.
//!
//! `crate::raft::proofs::log` and `crate::raft::proofs::history` both end on the
//! same sentence: Leader Completeness needs an induction over terms relating
//! [`at_least_as_up_to_date`] — the guard by which a log restricts elections —
//! to what has been committed. This module is not that induction. It is the
//! ground the induction has to stand on, and each piece of it is a theorem in
//! its own right.
//!
//! # What is proved here
//!
//! **1. A log's terms never decrease, and none of them exceeds its holder's own
//! term** ([`inv_log_shape`]). Two facts in one clause because they are proved
//! together: `tr_client_request` appends at the leader's current term, and the
//! entry is at the end, so it is the largest *because* it is bounded by the
//! term of the server writing it.
//!
//! The replication case is the interesting one, and it is the **consistency
//! check** paying for itself a third time. A follower accepting at `prefix`
//! ends with `follower.take(prefix).push(leader[prefix])`, and for the terms of
//! that to still be sorted the leader's entry has to be at least as late as the
//! follower's last kept one — which is exactly
//! `follower[prefix - 1].term == leader[prefix - 1].term` plus the leader's own
//! sortedness. See [`lemma_accepting_keeps_shape`].
//!
//! **2. The last term is the largest** ([`lemma_the_last_term_is_the_largest`]).
//! One line from sortedness, and the line that turns
//! [`at_least_as_up_to_date`] — which reads only a log's *last* entry — into a
//! statement about every entry in it.
//!
//! **3. A follower that already agrees with the leader at an index keeps its
//! entry there** ([`theorem_a_follower_that_agrees_keeps_the_entry`]). This is
//! the one I would point at. It is the reason the conditional truncation in
//! [`appended_log`] is not merely faithful to figure 2 but *load-bearing*:
//!
//! * if `prefix <= i`, then Log Matching says the follower and the leader agree
//!   at `prefix` as well, so the guard fires and the log is left **completely
//!   alone**;
//! * if `prefix > i`, the truncation is above `i` and index `i` survives it.
//!
//! Under an unconditional truncation the first case is false — a duplicate
//! `AppendEntries` for an early index would delete a committed entry from a
//! follower that already had it — and the induction Leader Completeness needs
//! would have no base to stand on. The model change in this branch's first
//! commit was made to close a gap between model and service; this is the
//! theorem that shows it was the *right* shape rather than merely an honest one.
//!
//! **4. Only replication can remove an entry, and it removes none the leader
//! also holds** ([`theorem_an_agreed_entry_survives_any_step`]). (3) lifted from
//! one transition to the whole relation, which is the form the induction will
//! consume: an entry leaves a log only via an `AppendEntries` from a leader that
//! **disagrees** with it at that index.
//!
//! **5. A candidate behind on terms is refused**
//! ([`theorem_a_candidate_missing_a_term_is_refused`],
//! [`theorem_a_stale_candidate_cannot_collect_that_vote`]). The election
//! restriction, biting: a voter holding *any* entry of term `T` refuses every
//! candidate whose last term is below `T`, and `tr_grant_vote` therefore cannot
//! fire. With (2) this is immediate, and it is half of what Leader Completeness
//! needs — a candidate cannot win on a log that is behind on terms.
//!
//! # What is still missing, exactly
//!
//! Leader Completeness needs the *other* half: the case where the candidate's
//! last term is **at or above** the voter's. There the candidate is not refused,
//! and the entry has to be shown present in its log by a different argument —
//! the candidate's own last entry was created by some leader of a term between
//! the commit's term and this election's, and a strong induction over terms
//! says that leader already held the committed entry.
//!
//! Three things are needed for that and are not here:
//!
//! * a **record of what was committed**, which the state does not keep: `commit`
//!   is a count per server and says nothing about which entry a quorum once
//!   held;
//! * a **record of the voter's log at the moment of the vote**, because
//!   `tr_grant_vote` compares against a log that has since moved on;
//! * the **strong induction over terms** itself, which is the part of Raft that
//!   took Verdi a person-scale Coq development.
//!
//! (4) and (5) are the two lemmas that induction calls; the induction is not
//! written. Read any claim about this module against that line.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::proofs::election::*;
use crate::raft::proofs::history::*;

verus! {

// ---------------------------------------------------------------------------
// The shape of one log
// ---------------------------------------------------------------------------

/// Every entry in `log` carries a term in `1 ..= t`.
///
/// The lower bound matters as much as the upper one: term 0 is [`last_term`]'s
/// answer for an *empty* log, so "no entry is at term 0" is what makes an empty
/// log strictly less up to date than a non-empty one rather than merely
/// incomparable. See [`theorem_an_empty_log_cannot_win_a_vote`].
pub open spec fn terms_within(log: Seq<Entry>, t: Term) -> bool {
    forall|i: nat| #![trigger log[i as int]] i < log.len() ==> 0 < log[i as int].term <= t
}

/// `log`'s terms never decrease.
pub open spec fn terms_sorted(log: Seq<Entry>) -> bool {
    forall|j: nat, k: nat|
        #![trigger log[j as int], log[k as int]]
        j <= k && k < log.len() ==> log[j as int].term <= log[k as int].term
}

/// Raising the bound keeps the entries inside it.
pub proof fn lemma_terms_within_monotone(log: Seq<Entry>, t: Term, u: Term)
    requires
        terms_within(log, t),
        t <= u,
    ensures
        terms_within(log, u),
{
}

/// **The last term is the largest.**
///
/// One line, and the line that makes [`at_least_as_up_to_date`] — a comparison
/// that reads only the last entry — say something about every entry in the log.
pub proof fn lemma_the_last_term_is_the_largest(log: Seq<Entry>, i: nat)
    requires
        terms_sorted(log),
        i < log.len(),
    ensures
        log[i as int].term <= last_term(log),
{
    let k = (log.len() - 1) as nat;
    assert(log[i as int].term <= log[k as int].term);
    assert(last_term(log) == log[k as int].term);
}

/// A leader appending at its own term keeps both facts.
///
/// Sortedness is where the two halves meet: the new entry is last and carries
/// `t`, and every entry already there is bounded by `t`, so it is the largest.
pub proof fn lemma_push_keeps_shape(log: Seq<Entry>, t: Term, value: nat)
    requires
        t > 0,
        terms_within(log, t),
        terms_sorted(log),
    ensures
        terms_within(log.push(Entry { term: t, value: value }), t),
        terms_sorted(log.push(Entry { term: t, value: value })),
{
    let nw = log.push(Entry { term: t, value: value });
    assert forall|i: nat| i < nw.len() implies 0 < nw[i as int].term <= t by {
        if i < log.len() {
            assert(nw[i as int] == log[i as int]);
        }
    }
    assert forall|j: nat, k: nat| j <= k && k < nw.len() implies nw[j as int].term
        <= nw[k as int].term by {
        if k < log.len() {
            assert(nw[j as int] == log[j as int]);
            assert(nw[k as int] == log[k as int]);
            assert(log[j as int].term <= log[k as int].term);
        } else {
            assert(nw[k as int].term == t);
            if j < log.len() {
                assert(nw[j as int] == log[j as int]);
                assert(log[j as int].term <= t);
            }
        }
    }
}

/// A prefix of a well-shaped log is well-shaped.
pub proof fn lemma_take_keeps_shape(log: Seq<Entry>, t: Term, p: nat)
    requires
        terms_within(log, t),
        terms_sorted(log),
        p <= log.len(),
    ensures
        terms_within(log.take(p as int), t),
        terms_sorted(log.take(p as int)),
{
    let nw = log.take(p as int);
    assert forall|i: nat| i < nw.len() implies 0 < nw[i as int].term <= t by {
        assert(nw[i as int] == log[i as int]);
    }
    assert forall|j: nat, k: nat| j <= k && k < nw.len() implies nw[j as int].term
        <= nw[k as int].term by {
        assert(nw[j as int] == log[j as int]);
        assert(nw[k as int] == log[k as int]);
        assert(log[j as int].term <= log[k as int].term);
    }
}

/// **Accepting one entry keeps both facts**, and the consistency check is what
/// pays for sortedness.
///
/// The truncating branch produces `follower.take(prefix).push(leader[prefix])`,
/// whose last entry is the leader's. For the terms of that to be sorted, the
/// leader's entry at `prefix` has to be at least as late as the follower's entry
/// at `prefix - 1` — and the guard says those two logs *agree* at `prefix - 1`,
/// so the question reduces to the leader's own sortedness at `prefix - 1` and
/// `prefix`. Take the guard away and this lemma is false.
pub proof fn lemma_accepting_keeps_shape(
    follower: Seq<Entry>,
    leader: Seq<Entry>,
    p: nat,
    t: Term,
)
    requires
        terms_within(follower, t),
        terms_sorted(follower),
        terms_within(leader, t),
        terms_sorted(leader),
        p < leader.len(),
        p <= follower.len(),
        p > 0 ==> follower[p - 1].term == leader[p - 1].term,
    ensures
        terms_within(appended_log(follower, leader, p), t),
        terms_sorted(appended_log(follower, leader, p)),
{
    let nw = appended_log(follower, leader, p);
    if p < follower.len() && follower[p as int].term == leader[p as int].term {
        assert(nw == follower);
    } else {
        let kept = follower.take(p as int);
        lemma_take_keeps_shape(follower, t, p);
        assert(nw == kept.push(leader[p as int]));
        assert(kept.len() == p);
        assert(0 < leader[p as int].term <= t);

        assert forall|i: nat| i < nw.len() implies 0 < nw[i as int].term <= t by {
            if i < kept.len() {
                assert(nw[i as int] == kept[i as int]);
            } else {
                assert(nw[i as int] == leader[p as int]);
            }
        }
        assert forall|j: nat, k: nat| j <= k && k < nw.len() implies nw[j as int].term
            <= nw[k as int].term by {
            if k < kept.len() {
                assert(nw[j as int] == kept[j as int]);
                assert(nw[k as int] == kept[k as int]);
                assert(kept[j as int].term <= kept[k as int].term);
            } else {
                assert(nw[k as int] == leader[p as int]);
                if j < kept.len() {
                    // `kept.len() == p` and `j` indexes it, so `p > 0` and the
                    // consistency check is available.
                    assert(p > 0);
                    let a = (p - 1) as nat;
                    assert(a as int == p - 1);
                    assert(a < p);
                    assert(j <= a);
                    assert(nw[j as int] == kept[j as int]);
                    assert(kept[j as int] == follower[j as int]);
                    // The new entry is at least as late as the last one kept:
                    // the consistency check, then the leader's own sortedness.
                    assert(follower[j as int].term <= follower[a as int].term);
                    assert(follower[a as int].term == leader[a as int].term);
                    assert(leader[a as int].term <= leader[p as int].term);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// **A candidate or a leader is at a term above 0.**
///
/// [`tr_timeout`] is the only way to stand for election and it increments, and
/// `raft_init` starts everybody a follower. So nothing can be a leader of term
/// 0, which is what lets [`terms_within`]'s lower bound survive
/// [`tr_client_request`].
pub open spec fn inv_standing_term_positive(c: Cluster) -> bool {
    forall|n: ServerId|
        #![trigger c.servers[n]]
        c.servers.contains_key(n) && (is_leader(c.servers[n]) || is_candidate(c.servers[n]))
            ==> c.servers[n].current_term > 0
}

/// **Every log's terms are sorted and bounded by their holder's own term.**
pub open spec fn inv_log_shape(c: Cluster) -> bool {
    forall|n: ServerId|
        #![trigger c.servers[n]]
        c.servers.contains_key(n) ==> terms_within(c.servers[n].log, c.servers[n].current_term)
            && terms_sorted(c.servers[n].log)
}

/// The term-structure invariant, carrying [`raft_hist_inv`] — and so Log
/// Matching — with it, because the durability theorem below needs both.
pub open spec fn raft_term_inv(c: Cluster) -> bool {
    &&& raft_hist_inv(c)
    &&& inv_standing_term_positive(c)
    &&& inv_log_shape(c)
}

/// **A step that leaves every log alone and lowers nobody's term keeps the
/// shape.** Seven of the nine transitions are of that form.
pub proof fn lemma_untouched_logs_keep_shape(pre: Cluster, post: Cluster)
    requires
        inv_log_shape(pre),
        post.servers.dom() == pre.servers.dom(),
        forall|m: ServerId|
            #![trigger post.servers[m]]
            post.servers.contains_key(m) ==> post.servers[m].log == pre.servers[m].log
                && post.servers[m].current_term >= pre.servers[m].current_term,
    ensures
        inv_log_shape(post),
{
    assert forall|m: ServerId| post.servers.contains_key(m) implies terms_within(
        post.servers[m].log,
        post.servers[m].current_term,
    ) && terms_sorted(post.servers[m].log) by {
        assert(pre.servers.contains_key(m));
        assert(post.servers[m].log == pre.servers[m].log);
        lemma_terms_within_monotone(
            pre.servers[m].log,
            pre.servers[m].current_term,
            post.servers[m].current_term,
        );
    }
}

/// **A step that changes no role and no term keeps the standing clause.**
pub proof fn lemma_unchanged_standing_keeps_positive(pre: Cluster, post: Cluster)
    requires
        inv_standing_term_positive(pre),
        post.servers.dom() == pre.servers.dom(),
        forall|m: ServerId|
            #![trigger post.servers[m]]
            post.servers.contains_key(m) ==> post.servers[m].current_term
                >= pre.servers[m].current_term && (is_leader(post.servers[m]) || is_candidate(
                post.servers[m],
            ) ==> is_leader(pre.servers[m]) || is_candidate(pre.servers[m])),
    ensures
        inv_standing_term_positive(post),
{
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        assert(pre.servers.contains_key(m));
        assert(is_leader(pre.servers[m]) || is_candidate(pre.servers[m]));
    }
}

// ---------------------------------------------------------------------------
// Preservation, one transition at a time
// ---------------------------------------------------------------------------

/// Standing for election. The log is untouched and the term goes up by one, so
/// the new candidate is at a term above 0 by arithmetic rather than by
/// induction.
pub proof fn lemma_timeout_preserves_terms(pre: Cluster, post: Cluster, n: ServerId)
    requires
        raft_term_inv(pre),
        tr_timeout(pre, post, n),
    ensures
        raft_term_inv(post),
{
    lemma_timeout_preserves_hist(pre, post, n);
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_shape(pre, post);
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// Granting a vote. The voter becomes a follower, so the standing clause is
/// vacuous for it, and its term only rises.
pub proof fn lemma_grant_vote_preserves_terms(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        raft_term_inv(pre),
        tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
    ensures
        raft_term_inv(post),
{
    lemma_grant_vote_preserves_hist(
        pre,
        post,
        voter,
        cand,
        term,
        cand_last_term,
        cand_last_index,
    );
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_shape(pre, post);
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        if m != voter {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// Winning. The new leader was a candidate at the same term, which was already
/// above 0.
pub proof fn lemma_become_leader_preserves_terms(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
)
    requires
        raft_term_inv(pre),
        tr_become_leader(pre, post, n, term),
    ensures
        raft_term_inv(post),
{
    lemma_become_leader_preserves_hist(pre, post, n, term);
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_shape(pre, post);
    assert(is_candidate(pre.servers[n]));
    assert(pre.servers[n].current_term > 0);
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// Stepping down. A follower, at a strictly higher term.
pub proof fn lemma_step_down_preserves_terms(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
)
    requires
        raft_term_inv(pre),
        tr_step_down(pre, post, n, term),
    ensures
        raft_term_inv(post),
{
    lemma_step_down_preserves_hist(pre, post, n, term);
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_shape(pre, post);
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// **A client command.** The one place a term enters a log from outside a log,
/// and the entry is stamped with the leader's own term — which
/// [`inv_standing_term_positive`] says is above 0 and which bounds everything
/// already there.
pub proof fn lemma_client_request_preserves_terms(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    value: nat,
)
    requires
        raft_term_inv(pre),
        tr_client_request(pre, post, n, value),
    ensures
        raft_term_inv(post),
{
    lemma_client_request_preserves_hist(pre, post, n, value);
    assert(post.servers.dom() =~= pre.servers.dom());

    let t = pre.servers[n].current_term;
    assert(pre.servers.contains_key(n));
    assert(is_leader(pre.servers[n]));
    assert(t > 0);
    lemma_push_keeps_shape(pre.servers[n].log, t, value);

    assert forall|m: ServerId| post.servers.contains_key(m) implies terms_within(
        post.servers[m].log,
        post.servers[m].current_term,
    ) && terms_sorted(post.servers[m].log) by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        } else {
            assert(post.servers[m].current_term == t);
            assert(post.servers[m].log == pre.servers[n].log.push(
                Entry { term: t, value: value },
            ));
        }
    }
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// **Replication.** The follower ends with a prefix of its own log and one entry
/// of the leader's, at a term the transition's guard says equals its own, and
/// [`lemma_accepting_keeps_shape`] is where the consistency check is spent.
pub proof fn lemma_append_entries_preserves_terms(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
)
    requires
        raft_term_inv(pre),
        tr_append_entries(pre, post, leader, follower, prefix),
    ensures
        raft_term_inv(post),
{
    lemma_append_entries_preserves_hist(pre, post, leader, follower, prefix);
    assert(post.servers.dom() =~= pre.servers.dom());

    let t = pre.servers[follower].current_term;
    assert(pre.servers[leader].current_term == t);
    assert(terms_within(pre.servers[follower].log, t));
    assert(terms_within(pre.servers[leader].log, t));
    lemma_accepting_keeps_shape(pre.servers[follower].log, pre.servers[leader].log, prefix, t);

    assert forall|m: ServerId| post.servers.contains_key(m) implies terms_within(
        post.servers[m].log,
        post.servers[m].current_term,
    ) && terms_sorted(post.servers[m].log) by {
        if m != follower {
            assert(post.servers[m] == pre.servers[m]);
        } else {
            assert(post.servers[m].current_term == t);
            assert(post.servers[m].log == appended_log(
                pre.servers[follower].log,
                pre.servers[leader].log,
                prefix,
            ));
        }
    }
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        if m != follower {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// Committing. Nothing but a count moves.
pub proof fn lemma_advance_commit_preserves_terms(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
)
    requires
        raft_term_inv(pre),
        tr_advance_commit(pre, post, n, upto),
    ensures
        raft_term_inv(post),
{
    lemma_advance_commit_preserves_hist(pre, post, n, upto);
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_shape(pre, post);
    assert forall|m: ServerId|
        post.servers.contains_key(m) && (is_leader(post.servers[m]) || is_candidate(
            post.servers[m],
        )) implies post.servers[m].current_term > 0 by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// Replay and stutter: `servers` is unchanged outright.
pub proof fn lemma_quiet_steps_preserve_terms(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_term_inv(pre),
        raft_step(pre, post, s),
        post.servers == pre.servers,
        post.members == pre.members,
        post.votes == pre.votes,
        post.created == pre.created,
        post.led == pre.led,
    ensures
        raft_term_inv(post),
{
    lemma_quiet_steps_preserve_hist(pre, post, s);
    assert(inv_log_shape(post));
    assert(inv_standing_term_positive(post));
}

/// **Every transition preserves the term-structure invariant.**
pub proof fn lemma_raft_step_preserves_terms(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_term_inv(pre),
        raft_step(pre, post, s),
    ensures
        raft_term_inv(post),
{
    match s {
        RaftStep::Timeout { server } => lemma_timeout_preserves_terms(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term, cand_last_term, cand_last_index } =>
            lemma_grant_vote_preserves_terms(
                pre,
                post,
                voter,
                candidate,
                term,
                cand_last_term,
                cand_last_index,
            ),
        RaftStep::BecomeLeader { server, term } => lemma_become_leader_preserves_terms(
            pre,
            post,
            server,
            term,
        ),
        RaftStep::StepDown { server, term } => lemma_step_down_preserves_terms(
            pre,
            post,
            server,
            term,
        ),
        RaftStep::ClientRequest { server, value } => lemma_client_request_preserves_terms(
            pre,
            post,
            server,
            value,
        ),
        RaftStep::AppendEntries { leader, follower, prefix } =>
            lemma_append_entries_preserves_terms(pre, post, leader, follower, prefix),
        RaftStep::AdvanceCommit { server, upto } => lemma_advance_commit_preserves_terms(
            pre,
            post,
            server,
            upto,
        ),
        RaftStep::Replay { msg } => lemma_quiet_steps_preserve_terms(
            pre,
            post,
            RaftStep::Replay { msg: msg },
        ),
        RaftStep::Stutter => lemma_quiet_steps_preserve_terms(pre, post, RaftStep::Stutter),
    }
}

/// An initial cluster satisfies it: every log is empty, so both shape clauses
/// are vacuous, and everybody is a follower.
pub proof fn lemma_init_term_inv(c: Cluster)
    requires
        raft_init(c),
    ensures
        raft_term_inv(c),
{
    lemma_init_hist_inv(c);
    assert forall|m: ServerId| c.servers.contains_key(m) implies terms_within(
        c.servers[m].log,
        c.servers[m].current_term,
    ) && terms_sorted(c.servers[m].log) by {
        assert(c.servers[m].log.len() == 0);
    }
}

/// The unlabelled version. Its own lemma for the trigger-inference reason
/// `lemma_raft_next_preserves_hist` documents.
pub proof fn lemma_raft_next_preserves_terms(pre: Cluster, post: Cluster)
    requires
        raft_term_inv(pre),
        raft_next(pre, post),
    ensures
        raft_term_inv(post),
{
    let s = choose|s: RaftStep| raft_step(pre, post, s);
    lemma_raft_step_preserves_terms(pre, post, s);
}

/// Walking an execution.
pub proof fn lemma_raft_execution_term_inv(tr: Seq<Cluster>, i: int)
    requires
        raft_execution(tr),
        0 <= i < tr.len(),
    ensures
        raft_term_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_init_term_inv(tr[0]);
    } else {
        let j = i - 1;
        lemma_raft_execution_term_inv(tr, j);
        assert(raft_next(tr[j], tr[j + 1]));
        assert(tr[j + 1] == tr[i]);
        lemma_raft_next_preserves_terms(tr[j], tr[i]);
    }
}

/// **The term-structure invariant holds in every reachable state.**
pub proof fn theorem_reachable_term_inv(c: Cluster)
    requires
        raft_reachable(c),
    ensures
        raft_term_inv(c),
{
    let tr = choose|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c;
    lemma_raft_execution_term_inv(tr, tr.len() - 1);
}

// ---------------------------------------------------------------------------
// An entry, once agreed, does not leave
// ---------------------------------------------------------------------------

/// **A follower that already agrees with the leader at index `i` keeps its
/// entry at `i`.**
///
/// The payoff of the conditional truncation, and the base the Leader
/// Completeness induction will stand on. Two cases, and the first is the one
/// that needs Log Matching:
///
/// * `prefix <= i` — the two logs agree at `i`, so by Log Matching they agree at
///   every index at and below it, `prefix` included. The guard in
///   [`appended_log`] therefore fires and the follower's log is not touched at
///   all. Under an unconditional truncation this case is *false*: the log would
///   be cut to `prefix + 1 <= i + 1` and the entry lost.
/// * `prefix > i` — the truncation is strictly above `i`, so `i` survives it.
pub proof fn theorem_a_follower_that_agrees_keeps_the_entry(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
    i: nat,
)
    requires
        raft_hist_inv(pre),
        tr_append_entries(pre, post, leader, follower, prefix),
        i < pre.servers[follower].log.len(),
        i < pre.servers[leader].log.len(),
        pre.servers[follower].log[i as int].term == pre.servers[leader].log[i as int].term,
    ensures
        post.servers.contains_key(follower),
        i < post.servers[follower].log.len(),
        post.servers[follower].log[i as int] == pre.servers[follower].log[i as int],
{
    let f = pre.servers[follower].log;
    let l = pre.servers[leader].log;
    let nw = appended_log(f, l, prefix);
    assert(post.servers[follower].log == nw);

    theorem_log_matching(pre, follower, leader, i);

    if prefix <= i {
        assert(prefix < f.len());
        assert(f[prefix as int] == l[prefix as int]);
        assert(f[prefix as int].term == l[prefix as int].term);
        assert(nw == f);
    } else {
        if prefix < f.len() && f[prefix as int].term == l[prefix as int].term {
            assert(nw == f);
        } else {
            let kept = f.take(prefix as int);
            assert(nw == kept.push(l[prefix as int]));
            assert(nw.len() == prefix + 1);
            assert(nw[i as int] == kept[i as int]);
            assert(kept[i as int] == f[i as int]);
        }
    }
}

/// Does `s` replicate to `n`?
///
/// Written as a match on the one variant rather than with a wildcard, so that a
/// new transition that can shorten a log forces a decision here instead of
/// falling silently into the "cannot touch `n`'s log" case that
/// [`theorem_an_agreed_entry_survives_any_step`] relies on.
pub open spec fn step_replicates_to(s: RaftStep, n: ServerId) -> bool {
    match s {
        RaftStep::AppendEntries { leader: _, follower, prefix: _ } => follower == n,
        _ => false,
    }
}

/// The leader of a replication step. Meaningless, and unused, for every other
/// step.
pub open spec fn replicating_leader(s: RaftStep) -> ServerId {
    match s {
        RaftStep::AppendEntries { leader, follower: _, prefix: _ } => leader,
        _ => 0,
    }
}

/// **An entry leaves a log only to a leader that disagrees with it there.**
///
/// [`theorem_a_follower_that_agrees_keeps_the_entry`] lifted from one transition
/// to the whole relation, which is the shape the Leader Completeness induction
/// needs: it has to rule out an entry vanishing from a voter's log between the
/// moment a quorum stored it and the moment that voter cast its next vote, and
/// the only step that could do it is an `AppendEntries` from a leader whose own
/// log differs at that index.
pub proof fn theorem_an_agreed_entry_survives_any_step(
    pre: Cluster,
    post: Cluster,
    s: RaftStep,
    n: ServerId,
    i: nat,
)
    requires
        raft_hist_inv(pre),
        raft_step(pre, post, s),
        pre.servers.contains_key(n),
        i < pre.servers[n].log.len(),
        step_replicates_to(s, n) ==> pre.servers.contains_key(replicating_leader(s)) && i
            < pre.servers[replicating_leader(s)].log.len()
            && pre.servers[replicating_leader(s)].log[i as int].term
            == pre.servers[n].log[i as int].term,
    ensures
        post.servers.contains_key(n),
        i < post.servers[n].log.len(),
        post.servers[n].log[i as int] == pre.servers[n].log[i as int],
{
    match s {
        RaftStep::AppendEntries { leader, follower, prefix } => {
            if follower == n {
                assert(step_replicates_to(s, n));
                assert(replicating_leader(s) == leader);
                theorem_a_follower_that_agrees_keeps_the_entry(
                    pre,
                    post,
                    leader,
                    n,
                    prefix,
                    i,
                );
            } else {
                assert(post.servers[n] == pre.servers[n]);
            }
        },
        RaftStep::ClientRequest { server, value } => {
            if server == n {
                assert(post.servers[n].log == pre.servers[n].log.push(
                    Entry { term: pre.servers[n].current_term, value: value },
                ));
                assert(post.servers[n].log[i as int] == pre.servers[n].log[i as int]);
            } else {
                assert(post.servers[n] == pre.servers[n]);
            }
        },
        RaftStep::Timeout { server } => {
            if server != n {
                assert(post.servers[n] == pre.servers[n]);
            } else {
                assert(post.servers[n].log == pre.servers[n].log);
            }
        },
        RaftStep::GrantVote { voter, candidate: _, term: _, cand_last_term: _, cand_last_index: _ } => {
            if voter != n {
                assert(post.servers[n] == pre.servers[n]);
            } else {
                assert(post.servers[n].log == pre.servers[n].log);
            }
        },
        RaftStep::BecomeLeader { server, term: _ } => {
            if server != n {
                assert(post.servers[n] == pre.servers[n]);
            } else {
                assert(post.servers[n].log == pre.servers[n].log);
            }
        },
        RaftStep::StepDown { server, term: _ } => {
            if server != n {
                assert(post.servers[n] == pre.servers[n]);
            } else {
                assert(post.servers[n].log == pre.servers[n].log);
            }
        },
        RaftStep::AdvanceCommit { server, upto: _ } => {
            if server != n {
                assert(post.servers[n] == pre.servers[n]);
            } else {
                assert(post.servers[n].log == pre.servers[n].log);
            }
        },
        RaftStep::Replay { msg: _ } => {
            assert(post.servers == pre.servers);
        },
        RaftStep::Stutter => {
            assert(post.servers == pre.servers);
        },
    }
}

// ---------------------------------------------------------------------------
// The election restriction, biting
// ---------------------------------------------------------------------------

/// **A candidate whose last term is behind an entry the voter holds is not up to
/// date.**
///
/// Immediate from [`lemma_the_last_term_is_the_largest`]: the voter's last term
/// is at least the term of the entry it holds, so it is strictly above the
/// candidate's, and both disjuncts of [`at_least_as_up_to_date`] fail.
pub proof fn theorem_a_candidate_missing_a_term_is_refused(
    c: Cluster,
    voter: ServerId,
    i: nat,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        inv_log_shape(c),
        c.servers.contains_key(voter),
        i < c.servers[voter].log.len(),
        cand_last_term < c.servers[voter].log[i as int].term,
    ensures
        !at_least_as_up_to_date(cand_last_term, cand_last_index, c.servers[voter].log),
{
    lemma_the_last_term_is_the_largest(c.servers[voter].log, i);
}

/// **And so that vote cannot be granted.** The refusal as a statement about the
/// transition relation rather than about the guard.
pub proof fn theorem_a_stale_candidate_cannot_collect_that_vote(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
    i: nat,
)
    requires
        inv_log_shape(pre),
        pre.servers.contains_key(voter),
        i < pre.servers[voter].log.len(),
        cand_last_term < pre.servers[voter].log[i as int].term,
    ensures
        !tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
{
    theorem_a_candidate_missing_a_term_is_refused(pre, voter, i, cand_last_term, cand_last_index);
}

/// **An empty log wins no vote from anybody holding an entry.**
///
/// The corollary that makes [`terms_within`]'s *lower* bound worth having: an
/// empty log's last term is 0, no entry is ever at term 0, so
/// `cand_last_term = 0` is strictly below every entry there is.
pub proof fn theorem_an_empty_log_cannot_win_a_vote(
    c: Cluster,
    voter: ServerId,
    cand: ServerId,
    i: nat,
)
    requires
        inv_log_shape(c),
        c.servers.contains_key(voter),
        c.servers.contains_key(cand),
        c.servers[cand].log.len() == 0,
        i < c.servers[voter].log.len(),
    ensures
        !at_least_as_up_to_date(
            last_term(c.servers[cand].log),
            c.servers[cand].log.len(),
            c.servers[voter].log,
        ),
{
    assert(last_term(c.servers[cand].log) == 0);
    assert(c.servers[voter].log[i as int].term > 0);
    theorem_a_candidate_missing_a_term_is_refused(c, voter, i, 0, 0);
}

/// The same, for any reachable cluster: **a candidate behind on terms cannot be
/// elected by a server that is ahead.**
pub proof fn theorem_a_stale_candidate_cannot_collect_that_vote_reachable(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
    i: nat,
)
    requires
        raft_reachable(pre),
        pre.servers.contains_key(voter),
        i < pre.servers[voter].log.len(),
        cand_last_term < pre.servers[voter].log[i as int].term,
    ensures
        !tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
{
    theorem_reachable_term_inv(pre);
    theorem_a_stale_candidate_cannot_collect_that_vote(
        pre,
        post,
        voter,
        cand,
        term,
        cand_last_term,
        cand_last_index,
        i,
    );
}

} // verus!
