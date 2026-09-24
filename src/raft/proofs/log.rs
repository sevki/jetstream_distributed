//! What the log guarantees, and — stated as plainly — what it does not yet.
//!
//! # What is proved here
//!
//! * **Leader Append-Only** — a leader's log only ever grows, and its existing
//!   entries never change. This one is a genuine payoff from Election Safety
//!   rather than a structural fact: the only transition that can truncate a log
//!   is `tr_append_entries`, whose receiver is a follower afterwards, so a
//!   server that is a leader on both sides of a step cannot have been that
//!   receiver.
//! * **Entries are never invented.** A new entry enters a log in exactly two
//!   ways: a leader appends one stamped with its own term, or a follower copies
//!   one from a leader's log at the same index. No other transition touches a
//!   log at all.
//! * **A follower agrees before it accepts** — the consistency check, as a
//!   named theorem rather than a guard someone has to go and read.
//! * **Commitment needs a majority *and* an entry of the committing leader's
//!   own term** — figure 8 of the Raft paper, made citable.
//!
//! # What is not proved *here*, and where it went
//!
//! **Log Matching is not in this module, and it is not missing** — it is in
//! [`crate::raft::proofs::history`], because it needed something this module
//! does not have.
//!
//! The reasoning is worth keeping, since the shape of the answer came out of
//! it. The natural statement of Log Matching — *if two logs hold entries with
//! the same term at the same index, their prefixes up to that index are
//! identical* — **is not inductive over this model's state alone**. Consider
//! `tr_client_request`: a leader `L` appends an entry at index `k` with term
//! `T`. To know that no other server already holds a *different* entry at
//! `(k, T)`, you have to know that no leader of term `T` ever appended at index
//! `k` before — and by Election Safety the only leader of `T` is `L` itself, so
//! the question is whether `L` has ever had a log shorter than it has now. That
//! is a fact about the *history* of the run, and the state does not record it.
//!
//! So the state records it now. `Cluster` carries ghost history, and the chain
//! of auxiliary invariants this module predicted it would need turned out to be
//! very nearly the chain it does need: a candidate or leader has voted in its
//! own term; at most one server is *ever* leader of a term, not merely at one
//! moment; having led a term you are either still leading it or past it; and a
//! leader holds everything created at its term.
//!
//! **Leader Completeness and State Machine Safety are still absent**, and still
//! for a stated reason rather than an unstated one: they need an induction over
//! terms relating [`at_least_as_up_to_date`] to what has been committed. This is
//! the part of Raft that took Verdi a person-scale Coq development, and writing
//! something that merely *looks* like it — or assuming the missing lemma and
//! calling the rest proved — is the failure mode this repository exists to
//! avoid.
//!
//! So the honest position is: the log is modelled faithfully, the properties
//! that follow from one step are proved here, Log Matching is proved next door,
//! and the two that need an induction over terms are named, located, and left
//! undone.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::proofs::election::*;

verus! {

/// The steps that cannot touch any log: the four election transitions, plus
/// replay and stutter.
///
/// Written out variant by variant rather than with a wildcard, so that adding a
/// transition to the model forces a decision here instead of silently falling
/// into the "does not touch a log" case.
pub open spec fn is_election_step(s: RaftStep) -> bool {
    match s {
        RaftStep::Timeout { server: _ } => true,
        RaftStep::GrantVote {
            voter: _,
            candidate: _,
            term: _,
            cand_last_term: _,
            cand_last_index: _,
        } => true,
        RaftStep::BecomeLeader { server: _, term: _ } => true,
        RaftStep::StepDown { server: _, term: _ } => true,
        RaftStep::Replay { msg: _ } => true,
        RaftStep::Stutter => true,
        RaftStep::ClientRequest { server: _, value: _ } => false,
        RaftStep::AppendEntries { leader: _, follower: _, prefix: _ } => false,
        RaftStep::AdvanceCommit { server: _, upto: _ } => false,
    }
}

/// **Elections do not touch logs.** Standing, voting, winning and standing down
/// change who a server thinks it is, not what it has recorded.
pub proof fn theorem_elections_do_not_touch_logs(
    pre: Cluster,
    post: Cluster,
    s: RaftStep,
    n: ServerId,
)
    requires
        raft_step(pre, post, s),
        is_election_step(s),
        pre.servers.contains_key(n),
    ensures
        post.servers.contains_key(n),
        post.servers[n].log == pre.servers[n].log,
{
}

/// **Advancing the commit point does not touch the log either.** It is a claim
/// about how much of the log is decided, not a change to the log.
pub proof fn theorem_committing_does_not_touch_the_log(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
    m: ServerId,
)
    requires
        tr_advance_commit(pre, post, n, upto),
        pre.servers.contains_key(m),
    ensures
        post.servers[m].log == pre.servers[m].log,
{
}

/// **Leader Append-Only.** A server that is a leader before and after a step
/// has only gained entries: everything it had, it still has, in the same
/// places.
///
/// This is where Election Safety earns something concrete. The only transition
/// that can shorten a log is `tr_append_entries`, and its receiver is a
/// follower once it has accepted — so a server that is a leader on both sides
/// of the step was not the receiver, and nothing else can have touched it.
pub proof fn theorem_leader_append_only(
    pre: Cluster,
    post: Cluster,
    s: RaftStep,
    n: ServerId,
)
    requires
        raft_step(pre, post, s),
        pre.servers.contains_key(n),
        is_leader(pre.servers[n]),
        post.servers.contains_key(n),
        is_leader(post.servers[n]),
    ensures
        has_prefix(post.servers[n].log, pre.servers[n].log, pre.servers[n].log.len()),
{
    match s {
        RaftStep::ClientRequest { server, value: _ } => {
            if server == n {
                assert forall|i: int| 0 <= i < pre.servers[n].log.len() implies
                post.servers[n].log[i] == pre.servers[n].log[i] by {}
            }
        },
        RaftStep::AppendEntries { leader: _, follower, prefix: _ } => {
            // `n` cannot be the follower: the follower is not a leader after
            // the step, and `n` is.
            assert(follower != n);
        },
        _ => {},
    }
}

/// **A client command is stamped with the term of the leader that accepted
/// it**, and appended at the end.
///
/// The term on an entry names the leader that made it, because Election Safety
/// says there was only one leader of that term. That is the fact any future
/// Log Matching proof is built on.
pub proof fn theorem_client_request_stamps_the_leaders_term(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    value: nat,
)
    requires
        tr_client_request(pre, post, n, value),
    ensures
        is_leader(pre.servers[n]),
        post.servers[n].log.len() == pre.servers[n].log.len() + 1,
        post.servers[n].log[pre.servers[n].log.len() as int].term
            == pre.servers[n].current_term,
        post.servers[n].log[pre.servers[n].log.len() as int].value == value,
        has_prefix(post.servers[n].log, pre.servers[n].log, pre.servers[n].log.len()),
{
    assert forall|i: int| 0 <= i < pre.servers[n].log.len() implies post.servers[n].log[i]
        == pre.servers[n].log[i] by {}
}

/// **A follower agrees before it accepts.** The consistency check, named.
///
/// A follower takes an entry at `prefix` only if it already holds an entry at
/// `prefix - 1` with the same term as the leader's. Everything it had beyond
/// `prefix` is dropped — including, as far as this model is concerned, entries
/// it had committed. That truncation is faithful Raft and is deliberately not
/// guarded against: safety against it is supposed to come from the election
/// restriction, which is exactly the theorem this module does not have.
pub proof fn theorem_a_follower_agrees_before_it_accepts(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
)
    requires
        tr_append_entries(pre, post, leader, follower, prefix),
    ensures
        is_leader(pre.servers[leader]),
        leader != follower,
        pre.servers[follower].current_term == pre.servers[leader].current_term,
        // The check itself.
        prefix > 0 ==> pre.servers[follower].log[prefix as int - 1].term
            == pre.servers[leader].log[prefix as int - 1].term,
        // What it ends up with: its own agreed prefix, then the leader's entry,
        // and nothing else.
        post.servers[follower].log.len() == prefix + 1,
        post.servers[follower].log[prefix as int] == pre.servers[leader].log[prefix as int],
        has_prefix(post.servers[follower].log, pre.servers[follower].log, prefix),
{
    assert forall|i: int| 0 <= i < prefix implies post.servers[follower].log[i]
        == pre.servers[follower].log[i] by {}
}

/// **Entries are never invented.** A follower's new entry is the leader's
/// entry, at the same index — copied, not constructed.
pub proof fn theorem_replication_copies_the_leaders_entry(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
)
    requires
        tr_append_entries(pre, post, leader, follower, prefix),
    ensures
        prefix < pre.servers[leader].log.len(),
        post.servers[follower].log[prefix as int] == pre.servers[leader].log[prefix as int],
{
}

/// **Commitment needs a majority, and the entry has to belong to the
/// committing leader's own term.**
///
/// The second half is figure 8 of the Raft paper. A majority *holding* an entry
/// is not a majority having *voted* on it, so a leader that committed an older
/// entry on replica count alone could have it overwritten by a later leader
/// whose votes never depended on that entry. Counting replicas is not enough;
/// the entry has to belong to the term doing the counting.
pub proof fn theorem_commit_needs_a_majority_of_its_own_term(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
)
    requires
        tr_advance_commit(pre, post, n, upto),
    ensures
        is_leader(pre.servers[n]),
        is_quorum(pre, replicated_on(pre, pre.servers[n].log, upto)),
        pre.servers[n].log[upto as int - 1].term == pre.servers[n].current_term,
        post.servers[n].commit == upto,
        upto > pre.servers[n].commit,
{
}

/// A majority of the cluster really does hold the committed prefix — so two
/// commits of the same length, by any two leaders, were each backed by a
/// majority, and those majorities share a member.
///
/// This is as far as quorum intersection reaches without Log Matching: it
/// produces a server holding *both* prefixes, which is the first line of a
/// Leader Completeness proof and not a substitute for one.
pub proof fn theorem_two_commits_share_a_holder(
    c: Cluster,
    log1: Seq<Entry>,
    log2: Seq<Entry>,
    n: nat,
)
    requires
        is_quorum(c, replicated_on(c, log1, n)),
        is_quorum(c, replicated_on(c, log2, n)),
    ensures
        exists|s: ServerId|
            replicated_on(c, log1, n).contains(s) && replicated_on(c, log2, n).contains(s),
{
    lemma_quorums_intersect(c, replicated_on(c, log1, n), replicated_on(c, log2, n));
}

/// **The leader of a term is unique, so there is one log being extended at that
/// term.** A corollary of Election Safety, stated because it is the shape every
/// later log argument leans on.
pub proof fn theorem_one_log_is_extended_per_term(c: Cluster, n1: ServerId, n2: ServerId)
    requires
        raft_inv(c),
        c.servers.contains_key(n1),
        c.servers.contains_key(n2),
        is_leader(c.servers[n1]),
        is_leader(c.servers[n2]),
        c.servers[n1].current_term == c.servers[n2].current_term,
    ensures
        n1 == n2,
        c.servers[n1].log == c.servers[n2].log,
{
    theorem_election_safety(c, n1, n2);
}

} // verus!
