//! **What was committed**, as a fact that survives the truncation that erases
//! it from the state.
//!
//! `crate::raft::proofs::terms` ends by naming three things the Leader
//! Completeness induction needs and does not have. This module supplies the
//! first of them, and spends it on the half of **State Machine Safety** that
//! does not need the induction at all.
//!
//! # Why the state could not say it
//!
//! `Server::commit` is a count on one server. Two things are wrong with it as
//! the subject of a safety property:
//!
//! * it says *how much* is committed and not *what*, and Leader Completeness is
//!   a claim about a particular entry at a particular index;
//! * **it retreats.** `crate::raft::proofs::log`'s C38 proves exactly when: a
//!   truncation cutting below the commit point takes it back, and
//!   `theorem_a_commit_retreat_means_a_committed_entry_was_deleted` says that
//!   when it happens a committed entry was deleted. After the retreat *nothing
//!   anywhere in the state records that the entry was ever committed* — so a
//!   theorem about committed entries has nothing left to quantify over in the
//!   one state where it matters most.
//!
//! [`Cluster::committed`] is the record, written at [`tr_advance_commit`] and
//! never removed from. Like the other two ghost fields it is read by no guard,
//! and [`crate::raft::proofs::history::theorem_history_does_not_gate_the_protocol`]
//! now covers it too — for *any* three histories whatsoever, every step is
//! still available from the same real state and lands in the same real state.
//! That theorem is what keeps this an auxiliary variable rather than an
//! assumption in a struct field's clothing.
//!
//! # What is proved here
//!
//! * [`inv_committed_is_created`] — **every committed entry matches the creation
//!   record of its slot.** The bridge from the commit record to the `created`
//!   record Log Matching is stated over. It survives `tr_client_request` for a
//!   reason worth naming: that transition *inserts* into `created`, and an
//!   insert at a slot already written would silently replace a record this
//!   invariant depends on. It cannot, because [`inv_creator_holds`] says a
//!   leader holds every slot already created at its term and the slot being
//!   written is one past the end of its log.
//! * [`inv_committed_within_its_term`] — a committed entry's own term is at
//!   least 1 and at most the term of the leader that committed it. Figure 8's
//!   restriction makes the two *equal* for the newest entry of a commit; below
//!   it they can differ, and this is the bound that always holds.
//! * [`theorem_a_commit_was_on_a_quorum`] — **at the moment of commitment a
//!   majority held that entry at that index**, entry for entry and not merely
//!   as a prefix length. This is the fact the induction's quorum-intersection
//!   step consumes.
//! * [`theorem_two_commits_at_one_slot_agree`] and
//!   [`theorem_state_machine_safety_at_agreeing_terms`] — **two commits at one
//!   index whose entries carry the same term are the same entry.**
//! * [`theorem_a_commit_is_a_commit_for_ever`] — the record only accumulates,
//!   across a whole run.
//! * [`theorem_the_record_covers_the_count`] — the ghost record and the real
//!   `commit` count agree at the moment they are written, so the record is not
//!   a second bookkeeping scheme that could drift from the first.
//!
//! # The gap, stated as sharply as it can now be
//!
//! State Machine Safety is *"if two servers apply the entry at index `i`, they
//! apply the same one"*. [`theorem_state_machine_safety_at_agreeing_terms`] is
//! that sentence **with one hypothesis added**: that the two commits agree on
//! the entry's term. So the whole of the remaining risk is concentrated in a
//! single question — can two leaders commit entries of *different terms* at one
//! index? — and that question is Leader Completeness.
//!
//! It is worth seeing how little is left over. The value half is free: one
//! `(term, index)` names one act of creation by one leader, which Election
//! Safety and the `created` record give unconditionally. Nothing about *values*,
//! *quorums*, or *counting* is missing. What is missing is the argument that a
//! later leader's log cannot have a different term at an index a quorum has
//! already agreed on, and that argument is the strong induction over terms:
//!
//! * the leader of term `T'` won a quorum in `T'`, and that quorum meets the
//!   commit-time quorum of [`theorem_a_commit_was_on_a_quorum`] in some voter;
//! * the voter still held the entry when it voted, by
//!   `crate::raft::proofs::terms::theorem_an_agreed_entry_survives_any_step`;
//! * so the candidate's log was at least as up to date as a log holding that
//!   entry — and `terms`' C43 closes the case where the candidate's last term is
//!   *behind*, while the case where it is at or above needs the induction
//!   hypothesis at the intermediate term.
//!
//! Two of those three bullets are theorems in this repository. The third is
//! not, and the second still needs the voter's log *as it stood at the vote*,
//! which is the remaining ghost record. Nothing here claims otherwise.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::proofs::election::*;
use crate::raft::proofs::history::*;
use crate::raft::proofs::terms::*;

verus! {

// ---------------------------------------------------------------------------
// Membership in the commit record
// ---------------------------------------------------------------------------

/// **What [`committed_by`] contains**, once and for all.
///
/// `committed_by` is built one index at a time rather than as a comprehension —
/// its own docs say why, and the short version is that in this vstd `Set` is the
/// *finite* set type and `Set::new` hands back an `Option`. The cost of that is
/// that membership is no longer something the solver can read off the
/// definition. This is the lemma that pays it, and every theorem below that asks
/// whether an entry is in the record calls it.
pub proof fn lemma_committed_by_members(s: Server, upto: nat, k: Commit)
    ensures
        committed_by(s, upto).contains(k) <==> (k.index < upto && k.index < s.log.len()
            && k.entry == s.log[k.index as int] && k.leader_term == s.current_term),
    decreases upto,
{
    if upto > 0 {
        let below = (upto - 1) as nat;
        lemma_committed_by_members(s, below, k);
        if upto <= s.log.len() {
            let top = Commit {
                leader_term: s.current_term,
                index: below,
                entry: s.log[upto - 1],
            };
            assert(committed_by(s, upto) == committed_by(s, below).insert(top));
            if k.index == below && k.entry == s.log[k.index as int] && k.leader_term
                == s.current_term {
                assert(k == top);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The invariants
// ---------------------------------------------------------------------------

/// **Every committed entry matches the creation record of its slot.**
///
/// The bridge between the commit record and the record Log Matching is stated
/// over. A `Commit` names an entry; `created` names what the leader of that
/// entry's term wrote at that index; this says they are the same thing.
pub open spec fn inv_committed_is_created(c: Cluster) -> bool {
    forall|k: Commit|
        #[trigger]
        c.committed.contains(k) ==> {
            &&& c.created.contains_key(Slot { term: k.entry.term, index: k.index })
            &&& c.created[Slot { term: k.entry.term, index: k.index }].value == k.entry.value
        }
}

/// A committed entry's own term is real, and no later than the term of the
/// leader that committed it.
///
/// Figure 8's restriction makes the two *equal* for the newest entry of a
/// commit. Below it they can differ — a leader commits its own entry and carries
/// everything before it along — and this is the bound that holds for all of it.
pub open spec fn inv_committed_within_its_term(c: Cluster) -> bool {
    forall|k: Commit|
        #[trigger] c.committed.contains(k) ==> 0 < k.entry.term <= k.leader_term
}

/// The commit invariant, carrying [`raft_term_inv`] — and so Log Matching and
/// the term structure — with it.
pub open spec fn raft_commit_inv(c: Cluster) -> bool {
    &&& raft_term_inv(c)
    &&& inv_committed_is_created(c)
    &&& inv_committed_within_its_term(c)
}

/// **A step that writes neither record keeps both clauses.** Seven of the nine
/// transitions are of that shape; the two that are not are the two that write.
pub proof fn lemma_untouched_records_keep_commit(pre: Cluster, post: Cluster)
    requires
        inv_committed_is_created(pre),
        inv_committed_within_its_term(pre),
        post.created == pre.created,
        post.committed == pre.committed,
    ensures
        inv_committed_is_created(post),
        inv_committed_within_its_term(post),
{
}

// ---------------------------------------------------------------------------
// Preservation, one transition at a time
// ---------------------------------------------------------------------------

/// Standing for election.
pub proof fn lemma_timeout_preserves_commit(pre: Cluster, post: Cluster, n: ServerId)
    requires
        raft_commit_inv(pre),
        tr_timeout(pre, post, n),
    ensures
        raft_commit_inv(post),
{
    lemma_timeout_preserves_terms(pre, post, n);
    lemma_untouched_records_keep_commit(pre, post);
}

/// Granting a vote.
pub proof fn lemma_grant_vote_preserves_commit(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        raft_commit_inv(pre),
        tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
    ensures
        raft_commit_inv(post),
{
    lemma_grant_vote_preserves_terms(
        pre,
        post,
        voter,
        cand,
        term,
        cand_last_term,
        cand_last_index,
    );
    lemma_untouched_records_keep_commit(pre, post);
}

/// Winning.
pub proof fn lemma_become_leader_preserves_commit(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
)
    requires
        raft_commit_inv(pre),
        tr_become_leader(pre, post, n, term),
    ensures
        raft_commit_inv(post),
{
    lemma_become_leader_preserves_terms(pre, post, n, term);
    lemma_untouched_records_keep_commit(pre, post);
}

/// Stepping down.
pub proof fn lemma_step_down_preserves_commit(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
)
    requires
        raft_commit_inv(pre),
        tr_step_down(pre, post, n, term),
    ensures
        raft_commit_inv(post),
{
    lemma_step_down_preserves_terms(pre, post, n, term);
    lemma_untouched_records_keep_commit(pre, post);
}

/// **A client command**, and the one place [`inv_committed_is_created`] could
/// have been quietly broken.
///
/// `committed` does not change, but `created` does: this transition *inserts*.
/// An insert at a slot already written would replace the record a committed
/// entry is matched against, and the invariant would become false without any
/// commit having happened.
///
/// It cannot, and the reason is already in the repository.
/// [`inv_creator_holds`] says a leader of term `t` holds every slot created at
/// `t` inside its own log; the slot being written is at index
/// `leader.log.len()`, which is not inside it. So the slot is fresh and every
/// other record is untouched.
pub proof fn lemma_client_request_preserves_commit(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    value: nat,
)
    requires
        raft_commit_inv(pre),
        tr_client_request(pre, post, n, value),
    ensures
        raft_commit_inv(post),
{
    lemma_client_request_preserves_terms(pre, post, n, value);

    let t = pre.servers[n].current_term;
    let fresh = Slot { term: t, index: pre.servers[n].log.len() };

    // The slot about to be written has never been written. `inv_creator_holds`
    // would otherwise place it inside the leader's own log.
    assert(!pre.created.contains_key(fresh)) by {
        if pre.created.contains_key(fresh) {
            assert(is_leader(pre.servers[n]));
            assert(pre.servers[n].current_term == fresh.term);
            assert(fresh.index < pre.servers[n].log.len());
        }
    }

    assert(post.committed == pre.committed);
    assert forall|k: Commit| post.committed.contains(k) implies {
        &&& post.created.contains_key(Slot { term: k.entry.term, index: k.index })
        &&& post.created[Slot { term: k.entry.term, index: k.index }].value == k.entry.value
    } by {
        let sl = Slot { term: k.entry.term, index: k.index };
        assert(pre.committed.contains(k));
        assert(pre.created.contains_key(sl));
        assert(sl != fresh);
        assert(post.created[sl] == pre.created[sl]);
    }
}

/// **Committing** — the transition that writes the record.
///
/// Every index below `upto` that the leader holds becomes a `Commit`, and the
/// two clauses come from facts already available about the leader's own log:
/// [`inv_logs_follow_created`] matches the entry to its creation record, and
/// [`inv_log_shape`] bounds its term by the leader's own.
pub proof fn lemma_advance_commit_preserves_commit(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
)
    requires
        raft_commit_inv(pre),
        tr_advance_commit(pre, post, n, upto),
    ensures
        raft_commit_inv(post),
{
    lemma_advance_commit_preserves_terms(pre, post, n, upto);

    let log = pre.servers[n].log;
    let t = pre.servers[n].current_term;
    assert(post.created == pre.created);
    assert(post.committed == pre.committed.union(committed_by(pre.servers[n], upto)));

    assert forall|k: Commit| post.committed.contains(k) implies {
        &&& post.created.contains_key(Slot { term: k.entry.term, index: k.index })
        &&& post.created[Slot { term: k.entry.term, index: k.index }].value == k.entry.value
    } by {
        if pre.committed.contains(k) {
        } else {
            assert(committed_by(pre.servers[n], upto).contains(k));
            lemma_committed_by_members(pre.servers[n], upto, k);
            assert(k.index < log.len());
            assert(k.entry == log[k.index as int]);
            assert(slot_of(log, k.index) == Slot { term: k.entry.term, index: k.index });
            assert(pre.created.contains_key(slot_of(log, k.index)));
        }
    }

    assert forall|k: Commit| post.committed.contains(k) implies 0 < k.entry.term
        <= k.leader_term by {
        if pre.committed.contains(k) {
        } else {
            assert(committed_by(pre.servers[n], upto).contains(k));
            lemma_committed_by_members(pre.servers[n], upto, k);
            assert(k.index < log.len());
            assert(k.entry == log[k.index as int]);
            assert(k.leader_term == t);
            assert(terms_within(log, t));
        }
    }
}

/// Replay and stutter.
pub proof fn lemma_quiet_steps_preserve_commit(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_commit_inv(pre),
        raft_step(pre, post, s),
        post.servers == pre.servers,
        post.members == pre.members,
        post.votes == pre.votes,
        post.created == pre.created,
        post.led == pre.led,
        post.committed == pre.committed,
    ensures
        raft_commit_inv(post),
{
    lemma_quiet_steps_preserve_terms(pre, post, s);
    lemma_untouched_records_keep_commit(pre, post);
}

/// **Every transition preserves the commit invariant.**
pub proof fn lemma_raft_step_preserves_commit(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_commit_inv(pre),
        raft_step(pre, post, s),
    ensures
        raft_commit_inv(post),
{
    match s {
        RaftStep::Timeout { server } => lemma_timeout_preserves_commit(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term, cand_last_term, cand_last_index } =>
            lemma_grant_vote_preserves_commit(
                pre,
                post,
                voter,
                candidate,
                term,
                cand_last_term,
                cand_last_index,
            ),
        RaftStep::BecomeLeader { server, term } => lemma_become_leader_preserves_commit(
            pre,
            post,
            server,
            term,
        ),
        RaftStep::StepDown { server, term } => lemma_step_down_preserves_commit(
            pre,
            post,
            server,
            term,
        ),
        RaftStep::ClientRequest { server, value } => lemma_client_request_preserves_commit(
            pre,
            post,
            server,
            value,
        ),
        RaftStep::AppendEntries { leader, follower, prefix } => {
            lemma_append_entries_preserves_terms(pre, post, leader, follower, prefix);
            lemma_untouched_records_keep_commit(pre, post);
        },
        RaftStep::AdvanceCommit { server, upto } => lemma_advance_commit_preserves_commit(
            pre,
            post,
            server,
            upto,
        ),
        RaftStep::Replay { msg } => lemma_quiet_steps_preserve_commit(
            pre,
            post,
            RaftStep::Replay { msg: msg },
        ),
        RaftStep::Stutter => lemma_quiet_steps_preserve_commit(pre, post, RaftStep::Stutter),
    }
}

/// An initial cluster satisfies it: nothing has been committed, so both clauses
/// are vacuous.
pub proof fn lemma_init_commit_inv(c: Cluster)
    requires
        raft_init(c),
    ensures
        raft_commit_inv(c),
{
    lemma_init_term_inv(c);
}

/// The unlabelled version. Its own lemma for the trigger-inference reason
/// `lemma_raft_next_preserves_hist` documents.
pub proof fn lemma_raft_next_preserves_commit(pre: Cluster, post: Cluster)
    requires
        raft_commit_inv(pre),
        raft_next(pre, post),
    ensures
        raft_commit_inv(post),
{
    let s = choose|s: RaftStep| raft_step(pre, post, s);
    lemma_raft_step_preserves_commit(pre, post, s);
}

/// Walking an execution.
pub proof fn lemma_raft_execution_commit_inv(tr: Seq<Cluster>, i: int)
    requires
        raft_execution(tr),
        0 <= i < tr.len(),
    ensures
        raft_commit_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_init_commit_inv(tr[0]);
    } else {
        let j = i - 1;
        lemma_raft_execution_commit_inv(tr, j);
        assert(raft_next(tr[j], tr[j + 1]));
        assert(tr[j + 1] == tr[i]);
        lemma_raft_next_preserves_commit(tr[j], tr[i]);
    }
}

/// **The commit invariant holds in every reachable state.**
pub proof fn theorem_reachable_commit_inv(c: Cluster)
    requires
        raft_reachable(c),
    ensures
        raft_commit_inv(c),
{
    let tr = choose|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c;
    lemma_raft_execution_commit_inv(tr, tr.len() - 1);
}

// ---------------------------------------------------------------------------
// What the record buys
// ---------------------------------------------------------------------------

/// **The ghost record covers the real count.**
///
/// Every index the committing leader's own `commit` now names is in the record,
/// with the entry that was there. Without this the record would be a second
/// bookkeeping scheme that could drift from the first — a hazard this repository
/// has already been bitten by once, in `records_fit`.
pub proof fn theorem_the_record_covers_the_count(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
)
    requires
        tr_advance_commit(pre, post, n, upto),
    ensures
        post.servers[n].commit == upto,
        forall|i: nat|
            #![trigger pre.servers[n].log[i as int]]
            i < post.servers[n].commit ==> post.committed.contains(
                Commit {
                    leader_term: pre.servers[n].current_term,
                    index: i,
                    entry: pre.servers[n].log[i as int],
                },
            ),
{
    assert forall|i: nat| i < upto implies post.committed.contains(
        Commit {
            leader_term: pre.servers[n].current_term,
            index: i,
            entry: pre.servers[n].log[i as int],
        },
    ) by {
        assert(i < pre.servers[n].log.len());
        lemma_committed_by_members(
            pre.servers[n],
            upto,
            Commit {
                leader_term: pre.servers[n].current_term,
                index: i,
                entry: pre.servers[n].log[i as int],
            },
        );
    }
}

/// **At the moment of commitment a majority held that entry at that index.**
///
/// Not "held a prefix of that length" — held *that entry*, entry for entry. The
/// difference is the whole point: quorum intersection gives a voter, and what
/// the induction needs from that voter is the entry in its log, not a count.
///
/// This is the one fact about commitment that is genuinely about a moment rather
/// than about a state, which is why it is stated over the transition.
pub proof fn theorem_a_commit_was_on_a_quorum(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
    k: Commit,
)
    requires
        tr_advance_commit(pre, post, n, upto),
        committed_by(pre.servers[n], upto).contains(k),
    ensures
        is_quorum(pre, replicated_on(pre, pre.servers[n].log, upto)),
        forall|m: ServerId|
            #![trigger pre.servers[m].log]
            replicated_on(pre, pre.servers[n].log, upto).contains(m) ==> pre.servers.contains_key(m)
                && k.index < pre.servers[m].log.len() && pre.servers[m].log[k.index as int]
                == k.entry,
{
    let held = replicated_on(pre, pre.servers[n].log, upto);
    lemma_committed_by_members(pre.servers[n], upto, k);
    assert(k.index < upto);
    assert(k.entry == pre.servers[n].log[k.index as int]);

    assert forall|m: ServerId| held.contains(m) implies pre.servers.contains_key(m) && k.index
        < pre.servers[m].log.len() && pre.servers[m].log[k.index as int] == k.entry by {
        assert(has_prefix(pre.servers[m].log, pre.servers[n].log, upto));
        assert(pre.servers[m].log[k.index as int] == pre.servers[n].log[k.index as int]);
    }
}

/// **Two commits at one index whose entries carry the same term are the same
/// entry.**
///
/// One `(term, index)` names one act of creation by one leader — Election Safety
/// and the `created` record — so both commits are reading the same record.
pub proof fn theorem_two_commits_at_one_slot_agree(c: Cluster, k1: Commit, k2: Commit)
    requires
        inv_committed_is_created(c),
        c.committed.contains(k1),
        c.committed.contains(k2),
        k1.index == k2.index,
        k1.entry.term == k2.entry.term,
    ensures
        k1.entry == k2.entry,
{
    let sl = Slot { term: k1.entry.term, index: k1.index };
    assert(sl == Slot { term: k2.entry.term, index: k2.index });
    assert(k1.entry.value == c.created[sl].value);
    assert(k2.entry.value == c.created[sl].value);
    assert(k1.entry =~= k2.entry);
}

/// **State Machine Safety, with the one hypothesis that is still missing.**
///
/// *If two servers apply the entry at index `i`, they apply the same one* — on
/// the assumption that the two commits agree on the entry's **term**. So the
/// whole of the remaining risk sits in one question: can two leaders commit
/// entries of different terms at one index? That question is Leader
/// Completeness, and this theorem is what closing it would buy.
///
/// Read this against the module docs, which say what is left over and what is
/// not: nothing about values, quorums or counting is missing.
pub proof fn theorem_state_machine_safety_at_agreeing_terms(
    c: Cluster,
    k1: Commit,
    k2: Commit,
)
    requires
        raft_reachable(c),
        c.committed.contains(k1),
        c.committed.contains(k2),
        k1.index == k2.index,
        k1.entry.term == k2.entry.term,
    ensures
        k1.entry == k2.entry,
{
    theorem_reachable_commit_inv(c);
    theorem_two_commits_at_one_slot_agree(c, k1, k2);
}

/// **A commit is a commit for ever**, across a whole run.
///
/// The record never shrinks, which is what makes "has ever been committed" the
/// right reading of it — and what makes it usable where `Server::commit`, which
/// retreats, is not.
pub proof fn theorem_a_commit_is_a_commit_for_ever(tr: Seq<Cluster>, i: int, j: int)
    requires
        raft_execution(tr),
        0 <= i <= j < tr.len(),
    ensures
        tr[i].committed.subset_of(tr[j].committed),
    decreases j - i,
{
    if i < j {
        theorem_a_commit_is_a_commit_for_ever(tr, i, j - 1);

        // Bound into plain variables before the `choose`: trigger inference for
        // `choose|s| raft_step(a, b, s)` cannot see through sequence indexing.
        // `lemma_raft_next_preserves_hist` documents the same hazard.
        let a = tr[j - 1];
        let b = tr[j];
        assert(raft_next(tr[j - 1], tr[j - 1 + 1]));
        assert(tr[j - 1 + 1] == tr[j]);
        assert(raft_next(a, b));
        let s = choose|s: RaftStep| raft_step(a, b, s);
        theorem_history_is_monotone(a, b, s);

        assert forall|k: Commit| tr[i].committed.contains(k) implies tr[j].committed.contains(
            k,
        ) by {
            assert(a.committed.contains(k));
            assert(b.committed.contains(k));
        }
        assert(tr[i].committed.subset_of(tr[j].committed));
    }
}

} // verus!
