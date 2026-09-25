//! **Ghost history**: the facts about a run that no single state records.
//!
//! `crate::raft::proofs::log`'s module docs say where the log argument stops,
//! and they are precise about why. Log Matching needs to rule out a second
//! entry at the same `(term, index)`, and at `tr_client_request` the leader
//! appends at the end of its own log with nothing in the *state* saying whether
//! a leader of that term ever appended there before. That is a fact about the
//! run, not about the state, and no invariant over `Cluster` as it was could
//! express it.
//!
//! So `Cluster` carries ghost fields — [`Cluster::created`], [`Cluster::led`] and
//! [`Cluster::committed`] — and this module is what the first two buy. The third
//! is spent in [`crate::raft::proofs::commit`]; it is maintained here only in
//! the sense that [`theorem_history_does_not_gate_the_protocol`] covers it too.
//!
//! # Why this is not an escape hatch
//!
//! The obvious worry about adding state to a model in order to prove something
//! about it is that the addition does the proving. It does not, and that is a
//! theorem rather than a promise:
//! [`theorem_history_does_not_gate_the_protocol`] says that for **any** history
//! whatsoever, every step still available before is still available after and
//! lands in the same real state. The history is written and never read — no
//! guard mentions it — so it cannot enable a transition, cannot disable one,
//! and cannot make the protocol behave in a way it otherwise would not. It is
//! an auxiliary variable in the standard sense, and that theorem is the
//! standard soundness condition for one.
//!
//! The repository's rule against verification escape hatches is about not
//! asserting what you have not proved. A history variable asserts nothing:
//! every clause that maintains it is discharged below like any other. (The rule
//! is enforced by a grep over `src/`, which is why this paragraph names no
//! hatch: the check cannot tell a use from a mention, and it is a better check
//! for not trying.)
//!
//! # What this module proves
//!
//! The election half of the chain. Four invariants, each of which is the
//! missing sentence for the next:
//!
//! 1. [`inv_standing_implies_voted`] — a candidate or leader has voted in its
//!    own term. True because [`tr_timeout`] is the only way to become a
//!    candidate and it casts a self-vote.
//! 2. [`inv_leader_is_led`] — a leader is on the record as having led its term.
//! 3. [`inv_led_implies_won`] — having led a term means having won it, which
//!    survives stepping down because votes are never retracted.
//! 4. [`inv_led_means_at_or_past`] — **having led a term you are still leading
//!    it or you have moved past it.** This is the one that does the work, and
//!    the one that needs (1): a leader of term `t` cannot grant a vote in term
//!    `t`, because it has already spent that vote on itself.
//!
//! Together with Election Safety they give
//! [`theorem_at_most_one_server_ever_leads_a_term`]: not merely that two
//! servers do not lead a term *at once*, but that across the whole run only one
//! server ever holds it. That is the sentence the log argument needs, and it is
//! strictly stronger than the state-only version — which is exactly why it
//! needed history to state.
//!
//! Then the `created` half, which is what the record was for. Three more
//! invariants:
//!
//! 5. [`inv_created_implies_led`] — nothing is created at a term nobody led.
//! 6. [`inv_creator_holds`] — **a leader of a term holds everything created at
//!    that term.** The freshness clause: a leader appends at the end of its own
//!    log, and this says every slot already written at its term is inside that
//!    log, so the slot it is about to write is not one of them.
//! 7. [`inv_logs_follow_created`] — every entry in every log agrees with the
//!    record of its creation: its value, and the term of the entry before it.
//!
//! and out of them [`theorem_log_matching`]: **two logs that agree on an
//! entry's term at an index agree on every entry at and below it.**
//!
//! Two moments in that are worth pointing at. At `tr_become_leader` the
//! freshness clause holds because a term being won now has never been led —
//! which takes all four election invariants and is the first place the history
//! actually earns its keep. And at `tr_append_entries` the record survives
//! because the follower's entry at `prefix - 1` has the same term as the
//! leader's; that is the **consistency check**, already in the protocol, and it
//! turns out to be exactly the guard the proof needs rather than something
//! added for it.
//!
//! Leader Completeness and State Machine Safety are still not proved. They need
//! this plus an induction over terms relating the up-to-date vote guard to what
//! has been committed, and that is the next piece of work rather than this one.
//! [`crate::raft::proofs::terms`] is the half of it that needs no further ghost
//! state — including the one theorem that most directly depends on Log Matching
//! proved here: **a follower that already agrees with the leader at an index
//! keeps its entry there**, which is what will rule out a committed entry
//! vanishing from a voter's log between the commit and the next election.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::proofs::election::*;

verus! {

// ---------------------------------------------------------------------------
// The history is written and never read
// ---------------------------------------------------------------------------

/// The same cluster with a different history.
pub open spec fn with_history(
    c: Cluster,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
) -> Cluster {
    Cluster {
        members: c.members,
        servers: c.servers,
        votes: c.votes,
        messages: c.messages,
        created: cr,
        led: l,
        committed: cm,
    }
}

/// What a step does to `created` — a function of the pre-state and the step,
/// with no choice in it.
pub open spec fn created_after(
    pre: Cluster,
    cr: Map<Slot, Creation>,
    s: RaftStep,
) -> Map<Slot, Creation> {
    match s {
        RaftStep::ClientRequest { server, value } => cr.insert(
            Slot {
                term: pre.servers[server].current_term,
                index: pre.servers[server].log.len(),
            },
            Creation {
                value: value,
                prev_term: term_before(
                    pre.servers[server].log,
                    pre.servers[server].log.len(),
                ),
            },
        ),
        _ => cr,
    }
}

/// What a step does to `led`. Likewise.
pub open spec fn led_after(pre: Cluster, l: Set<Led>, s: RaftStep) -> Set<Led> {
    match s {
        RaftStep::BecomeLeader { server, term } => l.insert(
            Led { server: server, term: term },
        ),
        _ => l,
    }
}

/// What a step does to `committed`. Likewise — and note it is a *function of the
/// pre-state*, so no step has any choice about it either.
pub open spec fn committed_after(pre: Cluster, cm: Set<Commit>, s: RaftStep) -> Set<Commit> {
    match s {
        RaftStep::AdvanceCommit { server, upto } => cm.union(
            committed_by(pre.servers[server], upto),
        ),
        _ => cm,
    }
}

/// Changing the history leaves the set of voters alone.
///
/// Needed, and not obvious. `voters_for` is `members.filter(..)` and the
/// closure it filters by **captures the cluster**, so the two sides are
/// `filter(m, f_1)` and `filter(m, f_2)` for two closure terms the solver has
/// no reason to identify — even though `f_1` and `f_2` test the same votes.
/// Set equality across them is extensional, which Verus does not apply on its
/// own, so it is applied here.
pub proof fn lemma_history_keeps_voters(
    c: Cluster,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
    cand: ServerId,
    term: Term,
)
    ensures
        voters_for(with_history(c, cr, l, cm), cand, term) == voters_for(c, cand, term),
        won_election(with_history(c, cr, l, cm), cand, term) == won_election(c, cand, term),
{
    assert(voters_for(with_history(c, cr, l, cm), cand, term) =~= voters_for(c, cand, term));
}

/// The same for `replicated_on`, which is the same shape for the same reason:
/// a filter of the membership by a closure over the cluster's logs.
pub proof fn lemma_history_keeps_replication(
    c: Cluster,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
    log: Seq<Entry>,
    n: nat,
)
    ensures
        replicated_on(with_history(c, cr, l, cm), log, n) == replicated_on(c, log, n),
{
    assert(replicated_on(with_history(c, cr, l, cm), log, n) =~= replicated_on(c, log, n));
}

/// The nine below are one per transition, and they exist in that shape for a
/// reason worth recording: proved as a single theorem over `raft_step` the
/// failure message says only "postcondition not satisfied" and names the whole
/// match, which is no help at all when eight arms are fine. Split, a failure
/// names the transition.

/// Standing for election.
pub proof fn lemma_timeout_ignores_history(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_timeout(pre, post, n),
    ensures
        tr_timeout(with_history(pre, cr, l, cm), with_history(post, cr, l, cm), n),
{
}

/// Granting a vote. `has_voted` is an existential over `votes`, which
/// `with_history` carries across whole.
pub proof fn lemma_grant_vote_ignores_history(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
    ensures
        tr_grant_vote(
            with_history(pre, cr, l, cm),
            with_history(post, cr, l, cm),
            voter,
            cand,
            term,
            cand_last_term,
            cand_last_index,
        ),
{
    assert forall|c0: ServerId| !with_history(pre, cr, l, cm).votes.contains(
        Vote { voter: voter, term: term, candidate: c0 },
    ) by {
        assert(!pre.votes.contains(Vote { voter: voter, term: term, candidate: c0 }));
    }
}

/// Taking the term. `won_election` is a filter; see `lemma_history_keeps_voters`.
pub proof fn lemma_become_leader_ignores_history(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_become_leader(pre, post, n, term),
    ensures
        tr_become_leader(
            with_history(pre, cr, l, cm),
            with_history(post, cr, l.insert(Led { server: n, term: term }), cm),
            n,
            term,
        ),
{
    lemma_history_keeps_voters(pre, cr, l, cm, n, term);
}

/// Stepping down. `carries_term` is an existential over `messages`.
pub proof fn lemma_step_down_ignores_history(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_step_down(pre, post, n, term),
    ensures
        tr_step_down(with_history(pre, cr, l, cm), with_history(post, cr, l, cm), n, term),
{
    assert(with_history(pre, cr, l, cm).messages =~= pre.messages);
}

/// Appending a client command — the one transition that writes `created`.
pub proof fn lemma_client_request_ignores_history(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    value: nat,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_client_request(pre, post, n, value),
    ensures
        tr_client_request(
            with_history(pre, cr, l, cm),
            with_history(
                post,
                cr.insert(
                    Slot {
                        term: pre.servers[n].current_term,
                        index: pre.servers[n].log.len(),
                    },
                    Creation {
                        value: value,
                        prev_term: term_before(pre.servers[n].log, pre.servers[n].log.len()),
                    },
                ),
                l,
                cm,
            ),
            n,
            value,
        ),
{
}

/// Replication.
pub proof fn lemma_append_entries_ignores_history(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_append_entries(pre, post, leader, follower, prefix),
    ensures
        tr_append_entries(
            with_history(pre, cr, l, cm),
            with_history(post, cr, l, cm),
            leader,
            follower,
            prefix,
        ),
{
}

/// Committing — the one transition that writes `committed`, so the only one
/// whose post-state carries a *different* history from its pre-state's here.
///
/// `replicated_on` is a filter; see `lemma_history_keeps_replication`.
pub proof fn lemma_advance_commit_ignores_history(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_advance_commit(pre, post, n, upto),
    ensures
        tr_advance_commit(
            with_history(pre, cr, l, cm),
            with_history(post, cr, l, cm.union(committed_by(pre.servers[n], upto))),
            n,
            upto,
        ),
{
    lemma_history_keeps_replication(pre, cr, l, cm, pre.servers[n].log, upto);
}

/// Replay.
pub proof fn lemma_replay_ignores_history(
    pre: Cluster,
    post: Cluster,
    m: RaftMessage,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_replay(pre, post, m),
    ensures
        tr_replay(with_history(pre, cr, l, cm), with_history(post, cr, l, cm), m),
{
}

/// Stutter.
pub proof fn lemma_stutter_ignores_history(
    pre: Cluster,
    post: Cluster,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        tr_stutter(pre, post),
    ensures
        tr_stutter(with_history(pre, cr, l, cm), with_history(post, cr, l, cm)),
{
}

/// **The history neither enables nor disables anything.**
///
/// For *any* `cr`, `l` and `cm` — not the ones the run actually produced, any at
/// all — the same step is available from the same real state and lands in the
/// same real state. A guard that read the history could not satisfy this: it
/// would be a step available under one history and not under another.
///
/// This is what makes `created`, `led` and `committed` auxiliary variables
/// rather than an assumption wearing a struct field's clothes. Everything else
/// in this module rests on it, and so does the right to say the model is still
/// Raft.
pub proof fn theorem_history_does_not_gate_the_protocol(
    pre: Cluster,
    post: Cluster,
    s: RaftStep,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
    cm: Set<Commit>,
)
    requires
        raft_step(pre, post, s),
    ensures
        raft_step(
            with_history(pre, cr, l, cm),
            with_history(
                post,
                created_after(pre, cr, s),
                led_after(pre, l, s),
                committed_after(pre, cm, s),
            ),
            s,
        ),
{
    // The lemmas are stated over the history each step actually produces; the
    // postcondition is stated over `created_after`, `led_after` and
    // `committed_after`. Each arm says what those three come to there, which is
    // the bridge between them.
    match s {
        RaftStep::Timeout { server } => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm);
            lemma_timeout_ignores_history(pre, post, server, cr, l, cm);
        },
        RaftStep::GrantVote { voter, candidate, term, cand_last_term, cand_last_index } => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm);
            lemma_grant_vote_ignores_history(
                pre,
                post,
                voter,
                candidate,
                term,
                cand_last_term,
                cand_last_index,
                cr,
                l,
                cm,
            );
        },
        RaftStep::BecomeLeader { server, term } => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l.insert(Led { server: server, term: term }));
            assert(committed_after(pre, cm, s) == cm);
            lemma_become_leader_ignores_history(pre, post, server, term, cr, l, cm);
        },
        RaftStep::StepDown { server, term } => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm);
            lemma_step_down_ignores_history(pre, post, server, term, cr, l, cm);
        },
        RaftStep::ClientRequest { server, value } => {
            assert(created_after(pre, cr, s) == cr.insert(
                Slot {
                    term: pre.servers[server].current_term,
                    index: pre.servers[server].log.len(),
                },
                Creation {
                    value: value,
                    prev_term: term_before(
                        pre.servers[server].log,
                        pre.servers[server].log.len(),
                    ),
                },
            ));
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm);
            lemma_client_request_ignores_history(pre, post, server, value, cr, l, cm);
        },
        RaftStep::AppendEntries { leader, follower, prefix } => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm);
            lemma_append_entries_ignores_history(pre, post, leader, follower, prefix, cr, l, cm);
        },
        RaftStep::AdvanceCommit { server, upto } => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm.union(
                committed_by(pre.servers[server], upto),
            ));
            lemma_advance_commit_ignores_history(pre, post, server, upto, cr, l, cm);
        },
        RaftStep::Replay { msg } => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm);
            lemma_replay_ignores_history(pre, post, msg, cr, l, cm);
        },
        RaftStep::Stutter => {
            assert(created_after(pre, cr, s) == cr);
            assert(led_after(pre, l, s) == l);
            assert(committed_after(pre, cm, s) == cm);
            lemma_stutter_ignores_history(pre, post, cr, l, cm);
        },
    }
}

/// History only ever grows. Neither field has a transition that removes from it,
/// which is what makes "has ever" the right reading of both.
pub proof fn theorem_history_is_monotone(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_step(pre, post, s),
    ensures
        pre.led.subset_of(post.led),
        pre.committed.subset_of(post.committed),
        forall|sl: Slot| #[trigger] pre.created.contains_key(sl) ==> post.created.contains_key(sl),
{
    match s {
        RaftStep::BecomeLeader { server: _, term: _ } => {},
        RaftStep::ClientRequest { server: _, value: _ } => {},
        RaftStep::AdvanceCommit { server, upto } => {
            assert(post.committed == pre.committed.union(
                committed_by(pre.servers[server], upto),
            ));
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// The invariants
// ---------------------------------------------------------------------------

/// **A candidate or a leader has voted in its own term.**
///
/// [`tr_timeout`] is the only way to become a candidate and it casts the
/// self-vote in the same step, so standing at all means having spent that
/// term's vote. Unremarkable on its own; it is what makes
/// [`inv_led_means_at_or_past`] survive [`tr_grant_vote`], because a leader of
/// term `t` asked for its vote in term `t` is refused by the guard rather than
/// quietly demoted.
pub open spec fn inv_standing_implies_voted(c: Cluster) -> bool {
    forall|n: ServerId|
        #![trigger c.servers[n]]
        c.servers.contains_key(n) && (is_leader(c.servers[n]) || is_candidate(c.servers[n]))
            ==> has_voted(c, n, c.servers[n].current_term)
}

/// A leader is on the record as having led its own term.
pub open spec fn inv_leader_is_led(c: Cluster) -> bool {
    forall|n: ServerId|
        #![trigger c.servers[n]]
        c.servers.contains_key(n) && is_leader(c.servers[n]) ==> c.led.contains(
            Led { server: n, term: c.servers[n].current_term },
        )
}

/// **Having led a term means having won it**, still, now.
///
/// The counterpart of `inv_leader_quorum` for a leadership that is over. It
/// survives because `votes` never shrinks: a majority, once won, stays won, and
/// a server that stepped down in term 7 is still the server that won term 7.
pub open spec fn inv_led_implies_won(c: Cluster) -> bool {
    forall|l: Led| #[trigger] c.led.contains(l) ==> won_election(c, l.server, l.term)
}

/// **Having led a term, you are still leading it or you have moved past it.**
///
/// The load-bearing one. What it rules out is a server that led term `t`,
/// stopped leading it, and is still *at* term `t` — because the only ways to
/// stop being a leader either raise the term ([`tr_timeout`],
/// [`tr_step_down`], [`tr_grant_vote`] at a higher term) or cannot fire at all:
///
/// * [`tr_grant_vote`] at term `t` itself needs `!has_voted(voter, t)`, and by
///   [`inv_standing_implies_voted`] a leader of `t` has already voted in `t`;
/// * [`tr_append_entries`] demotes its receiver at an equal term, and a leader
///   of `t` receiving one from a leader of `t` is two leaders in one term,
///   which Election Safety rules out.
///
/// Both exclusions are why this invariant needs `raft_inv` alongside it, and
/// why the second one is the same fact the service's `follow_step` leans on
/// from the other side.
pub open spec fn inv_led_means_at_or_past(c: Cluster) -> bool {
    forall|l: Led|
        #![trigger c.led.contains(l)]
        c.led.contains(l) && c.servers.contains_key(l.server) ==> {
            &&& c.servers[l.server].current_term >= l.term
            &&& (c.servers[l.server].current_term == l.term ==> is_leader(c.servers[l.server]))
        }
}

/// The slot naming the entry at `i`.
pub open spec fn slot_of(log: Seq<Entry>, i: nat) -> Slot {
    Slot { term: log[i as int].term, index: i }
}

/// Nothing is created at a term nobody has led.
pub open spec fn inv_created_implies_led(c: Cluster) -> bool {
    forall|s: Slot|
        #[trigger]
        c.created.contains_key(s) ==> exists|n: ServerId|
            #[trigger] c.led.contains(Led { server: n, term: s.term })
}

/// **A leader of a term holds everything created at that term.**
///
/// The freshness clause, in the only form that is inductive, and the reason
/// `tr_client_request` cannot quietly overwrite a record. A leader of `t`
/// appends at the end of its own log; this says every slot already created at
/// `t` is *inside* that log, so the slot about to be written is not one of
/// them. Without it a second append at one slot would overwrite the record and
/// every log still holding the old entry would stop agreeing with it — which is
/// to say, Log Matching would be false.
pub open spec fn inv_creator_holds(c: Cluster) -> bool {
    forall|n: ServerId, s: Slot|
        #![trigger c.servers[n], c.created.contains_key(s)]
        c.servers.contains_key(n) && is_leader(c.servers[n]) && c.servers[n].current_term == s.term
            && c.created.contains_key(s) ==> s.index < c.servers[n].log.len()
}

/// **Every entry in every log agrees with the record of its creation** — its
/// value, and the term of the entry before it.
///
/// This is the whole of Log Matching in one clause. Two servers whose entries
/// at index `i` carry the same term are reading the same slot, so they agree on
/// the value; and they agree on the *term before*, which is the same question
/// one index down. Repeat to zero.
pub open spec fn inv_logs_follow_created(c: Cluster) -> bool {
    forall|n: ServerId, i: nat|
        #![trigger c.servers[n].log[i as int]]
        c.servers.contains_key(n) && i < c.servers[n].log.len() ==> {
            &&& c.created.contains_key(slot_of(c.servers[n].log, i))
            &&& c.created[slot_of(c.servers[n].log, i)].value == c.servers[n].log[i as int].value
            &&& c.created[slot_of(c.servers[n].log, i)].prev_term == term_before(
                c.servers[n].log,
                i,
            )
        }
}

/// The history invariant, which carries `raft_inv` with it because several of
/// its clauses need Election Safety to survive a step.
pub open spec fn raft_hist_inv(c: Cluster) -> bool {
    &&& raft_inv(c)
    &&& inv_standing_implies_voted(c)
    &&& inv_leader_is_led(c)
    &&& inv_led_implies_won(c)
    &&& inv_led_means_at_or_past(c)
    &&& inv_created_implies_led(c)
    &&& inv_creator_holds(c)
    &&& inv_logs_follow_created(c)
}

/// **The three log-side clauses survive any step that touches no log, adds
/// nothing to the record, and promotes nobody to leader.**
///
/// Six of the nine transitions are of that shape. The last hypothesis is the
/// one with content: `inv_creator_holds` is a statement about leaders, so a
/// step that *demotes* one only makes it weaker — but a step that promotes one
/// has to show the new leader holds everything already created at its term, and
/// that is `tr_become_leader`'s own business below.
pub proof fn lemma_untouched_logs_keep_log_hist(pre: Cluster, post: Cluster)
    requires
        inv_created_implies_led(pre),
        inv_creator_holds(pre),
        inv_logs_follow_created(pre),
        post.created == pre.created,
        pre.led.subset_of(post.led),
        post.servers.dom() == pre.servers.dom(),
        forall|m: ServerId|
            #![trigger post.servers[m]]
            post.servers.contains_key(m) ==> post.servers[m].log == pre.servers[m].log && (
            is_leader(post.servers[m]) ==> is_leader(pre.servers[m])
                && pre.servers[m].current_term == post.servers[m].current_term),
    ensures
        inv_created_implies_led(post),
        inv_creator_holds(post),
        inv_logs_follow_created(post),
{
    assert forall|s: Slot| post.created.contains_key(s) implies exists|n: ServerId|
        #[trigger] post.led.contains(Led { server: n, term: s.term }) by {
        let w = choose|w: ServerId| pre.led.contains(Led { server: w, term: s.term });
        assert(post.led.contains(Led { server: w, term: s.term }));
    }
}

// ---------------------------------------------------------------------------
// Election Safety, over `won_election` rather than over roles
// ---------------------------------------------------------------------------

/// **At most one server wins a term.**
///
/// `theorem_election_safety` stated over two current leaders; this states the
/// same counting argument over the winning itself, which is what a record of a
/// finished leadership gives. The proof is the same three sentences: two
/// majorities share a voter, and that voter voted once.
pub proof fn lemma_one_winner_per_term(c: Cluster, n1: ServerId, n2: ServerId, term: Term)
    requires
        inv_votes_unique(c),
        won_election(c, n1, term),
        won_election(c, n2, term),
    ensures
        n1 == n2,
{
    lemma_quorums_intersect(c, voters_for(c, n1, term), voters_for(c, n2, term));
    let v = choose|v: ServerId|
        voters_for(c, n1, term).contains(v) && voters_for(c, n2, term).contains(v);

    // `voters_for` is a filter, so membership unfolds straight to the vote.
    assert(c.votes.contains(Vote { voter: v, term: term, candidate: n1 }));
    assert(c.votes.contains(Vote { voter: v, term: term, candidate: n2 }));
}

/// **At most one server *ever* leads a term** — across the whole run, not
/// merely at one instant.
///
/// This is the sentence the log argument needs and the one the state alone
/// cannot say. `theorem_election_safety` compares two servers that are leaders
/// *now*; a leader that stepped down an hour ago is not covered by it, and an
/// entry it created is still in logs. Recording the leadership is what makes
/// the stronger statement available, and the strengthening is entirely in the
/// ghost field: the counting argument underneath is unchanged.
pub proof fn theorem_at_most_one_server_ever_leads_a_term(
    c: Cluster,
    n1: ServerId,
    n2: ServerId,
    term: Term,
)
    requires
        raft_hist_inv(c),
        c.led.contains(Led { server: n1, term: term }),
        c.led.contains(Led { server: n2, term: term }),
    ensures
        n1 == n2,
{
    lemma_one_winner_per_term(c, n1, n2, term);
}

/// The same, for any reachable cluster.
pub proof fn theorem_at_most_one_server_ever_leads_a_term_reachable(
    c: Cluster,
    n1: ServerId,
    n2: ServerId,
    term: Term,
)
    requires
        raft_reachable(c),
        c.led.contains(Led { server: n1, term: term }),
        c.led.contains(Led { server: n2, term: term }),
    ensures
        n1 == n2,
{
    theorem_reachable_hist_inv(c);
    theorem_at_most_one_server_ever_leads_a_term(c, n1, n2, term);
}

// ---------------------------------------------------------------------------
// Preservation, one transition at a time
// ---------------------------------------------------------------------------

/// Standing for election. The term goes up and a self-vote goes with it, so
/// every recorded leadership is now strictly in the past.
pub proof fn lemma_timeout_preserves_hist(pre: Cluster, post: Cluster, n: ServerId)
    requires
        raft_hist_inv(pre),
        tr_timeout(pre, post, n),
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(pre, post, RaftStep::Timeout { server: n });

    assert forall|m: ServerId| post.servers.contains_key(m) && (is_leader(post.servers[m])
        || is_candidate(post.servers[m])) implies has_voted(
        post,
        m,
        post.servers[m].current_term,
    ) by {
        if m == n {
            // The self-vote this very step cast.
            assert(post.votes.contains(
                Vote {
                    voter: n,
                    term: pre.servers[n].current_term + 1,
                    candidate: n,
                },
            ));
        } else {
            assert(post.servers[m] == pre.servers[m]);
            let cand = choose|cand: ServerId|
                pre.votes.contains(
                    Vote { voter: m, term: pre.servers[m].current_term, candidate: cand },
                );
            assert(post.votes.contains(
                Vote { voter: m, term: post.servers[m].current_term, candidate: cand },
            ));
        }
    }

    assert forall|m: ServerId| post.servers.contains_key(m) && is_leader(
        post.servers[m],
    ) implies post.led.contains(
        Led { server: m, term: post.servers[m].current_term },
    ) by {
        // `n` is a candidate afterwards, so the only leaders are untouched.
        assert(m != n);
        assert(post.servers[m] == pre.servers[m]);
    }

    assert forall|l: Led| post.led.contains(l) implies won_election(
        post,
        l.server,
        l.term,
    ) by {
        lemma_quorum_survives(pre, post, l.server, l.term);
    }

    assert forall|l: Led| post.led.contains(l) && post.servers.contains_key(
        l.server,
    ) implies post.servers[l.server].current_term >= l.term && (post.servers[l.server].current_term
        == l.term ==> is_leader(post.servers[l.server])) by {
        if l.server == n {
            // The term strictly rose, so the `== l.term` case cannot arise.
            assert(pre.servers[n].current_term >= l.term);
        } else {
            assert(post.servers[l.server] == pre.servers[l.server]);
        }
    }

    // No log moved and nothing was created; `n` became a candidate, not a
    // leader.
    // `insert` over a key the map already has, so the domains match —
    // extensionally, which is not a step Verus takes on its own.
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_log_hist(pre, post);
}

/// Granting a vote. **The interesting case**: a leader of `term` cannot reach
/// this transition at `term`, because it spent that vote on itself.
pub proof fn lemma_grant_vote_preserves_hist(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        raft_hist_inv(pre),
        tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(
        pre,
        post,
        RaftStep::GrantVote {
            voter: voter,
            candidate: cand,
            term: term,
            cand_last_term: cand_last_term,
            cand_last_index: cand_last_index,
        },
    );

    assert forall|m: ServerId| post.servers.contains_key(m) && (is_leader(post.servers[m])
        || is_candidate(post.servers[m])) implies has_voted(
        post,
        m,
        post.servers[m].current_term,
    ) by {
        // The voter becomes a follower, so it is not one of these.
        assert(m != voter);
        assert(post.servers[m] == pre.servers[m]);
        let c0 = choose|c0: ServerId|
            pre.votes.contains(
                Vote { voter: m, term: pre.servers[m].current_term, candidate: c0 },
            );
        assert(post.votes.contains(
            Vote { voter: m, term: post.servers[m].current_term, candidate: c0 },
        ));
    }

    assert forall|m: ServerId| post.servers.contains_key(m) && is_leader(
        post.servers[m],
    ) implies post.led.contains(
        Led { server: m, term: post.servers[m].current_term },
    ) by {
        assert(m != voter);
        assert(post.servers[m] == pre.servers[m]);
    }

    assert forall|l: Led| post.led.contains(l) implies won_election(
        post,
        l.server,
        l.term,
    ) by {
        lemma_quorum_survives(pre, post, l.server, l.term);
    }

    assert forall|l: Led| post.led.contains(l) && post.servers.contains_key(
        l.server,
    ) implies post.servers[l.server].current_term >= l.term && (post.servers[l.server].current_term
        == l.term ==> is_leader(post.servers[l.server])) by {
        if l.server == voter {
            assert(pre.servers[voter].current_term >= l.term);
            if term == l.term {
                // Then the voter's term was already `l.term`, so by the
                // invariant it was leading `l.term` — and by
                // `inv_standing_implies_voted` it had voted in `l.term`, which
                // is exactly what this transition's guard forbids.
                assert(pre.servers[voter].current_term == l.term);
                assert(is_leader(pre.servers[voter]));
                assert(has_voted(pre, voter, l.term));
                assert(false);
            }
        } else {
            assert(post.servers[l.server] == pre.servers[l.server]);
        }
    }

    // The voter became a follower, so no log moved and nobody was promoted.
    // `insert` over a key the map already has, so the domains match —
    // extensionally, which is not a step Verus takes on its own.
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_log_hist(pre, post);
}

/// Taking the term. The new leadership is recorded in the same step.
pub proof fn lemma_become_leader_preserves_hist(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
)
    requires
        raft_hist_inv(pre),
        tr_become_leader(pre, post, n, term),
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(pre, post, RaftStep::BecomeLeader { server: n, term: term });

    assert forall|m: ServerId| post.servers.contains_key(m) && (is_leader(post.servers[m])
        || is_candidate(post.servers[m])) implies has_voted(
        post,
        m,
        post.servers[m].current_term,
    ) by {
        // `n` was a candidate at this very term, so it had already voted.
        let c0 = choose|c0: ServerId|
            pre.votes.contains(
                Vote { voter: m, term: pre.servers[m].current_term, candidate: c0 },
            );
        assert(post.votes.contains(
            Vote { voter: m, term: post.servers[m].current_term, candidate: c0 },
        ));
    }

    assert forall|m: ServerId| post.servers.contains_key(m) && is_leader(
        post.servers[m],
    ) implies post.led.contains(
        Led { server: m, term: post.servers[m].current_term },
    ) by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }

    assert forall|l: Led| post.led.contains(l) implies won_election(
        post,
        l.server,
        l.term,
    ) by {
        if l != (Led { server: n, term: term }) {
            lemma_quorum_survives(pre, post, l.server, l.term);
        }
    }

    assert forall|l: Led| post.led.contains(l) && post.servers.contains_key(
        l.server,
    ) implies post.servers[l.server].current_term >= l.term && (post.servers[l.server].current_term
        == l.term ==> is_leader(post.servers[l.server])) by {
        if l.server == n {
            assert(post.servers[n].current_term == term);
            assert(is_leader(post.servers[n]));
            // The recorded leadership is this one, or an older one at a term
            // this server has already reached.
            assert(pre.servers[n].current_term == term);
        } else {
            assert(post.servers[l.server] == pre.servers[l.server]);
        }
    }

    lemma_become_leader_finds_its_term_unwritten(pre, post, n, term);
}

/// **A server taking a term finds nothing created at it.**
///
/// The clause `inv_creator_holds` needs at the one transition that promotes a
/// leader, and the first place the history actually earns its keep. The
/// argument is a chain of three of the invariants above, and every link needs
/// the *record* rather than the state:
///
/// 1. if something was created at `term`, somebody led `term`
///    ([`inv_created_implies_led`]) — and that somebody may have stepped down
///    long ago, which is exactly what the state does not say;
/// 2. whoever led it won it ([`inv_led_implies_won`]), and this server is
///    winning it now, so by [`lemma_one_winner_per_term`] they are the same
///    server;
/// 3. so this server led `term` — and by [`inv_led_means_at_or_past`] it would
///    still be leading it, because its term has not moved. It is a candidate.
///
/// A contradiction, so nothing was created at `term`, so the clause holds
/// vacuously for the new leader.
pub proof fn lemma_become_leader_finds_its_term_unwritten(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
)
    requires
        raft_hist_inv(pre),
        tr_become_leader(pre, post, n, term),
    ensures
        inv_created_implies_led(post),
        inv_creator_holds(post),
        inv_logs_follow_created(post),
{
    assert forall|s: Slot| post.created.contains_key(s) implies exists|w: ServerId|
        #[trigger] post.led.contains(Led { server: w, term: s.term }) by {
        let w = choose|w: ServerId| pre.led.contains(Led { server: w, term: s.term });
        assert(post.led.contains(Led { server: w, term: s.term }));
    }

    assert forall|m: ServerId, s: Slot|
        post.servers.contains_key(m) && is_leader(post.servers[m]) && post.servers[m].current_term
            == s.term && post.created.contains_key(s) implies s.index
        < post.servers[m].log.len() by {
        if m == n {
            // `s.term == term`, and the three steps above.
            let w = choose|w: ServerId| pre.led.contains(Led { server: w, term: s.term });
            lemma_one_winner_per_term(pre, w, n, s.term);
            assert(pre.led.contains(Led { server: n, term: s.term }));
            assert(is_leader(pre.servers[n]));
            assert(false);
        } else {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// Stepping down. Strictly higher, so every record stays strictly in the past.
pub proof fn lemma_step_down_preserves_hist(pre: Cluster, post: Cluster, n: ServerId, term: Term)
    requires
        raft_hist_inv(pre),
        tr_step_down(pre, post, n, term),
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(pre, post, RaftStep::StepDown { server: n, term: term });

    assert forall|m: ServerId| post.servers.contains_key(m) && (is_leader(post.servers[m])
        || is_candidate(post.servers[m])) implies has_voted(
        post,
        m,
        post.servers[m].current_term,
    ) by {
        assert(m != n);
        assert(post.servers[m] == pre.servers[m]);
        let c0 = choose|c0: ServerId|
            pre.votes.contains(
                Vote { voter: m, term: pre.servers[m].current_term, candidate: c0 },
            );
        assert(post.votes.contains(
            Vote { voter: m, term: post.servers[m].current_term, candidate: c0 },
        ));
    }

    assert forall|m: ServerId| post.servers.contains_key(m) && is_leader(
        post.servers[m],
    ) implies post.led.contains(
        Led { server: m, term: post.servers[m].current_term },
    ) by {
        assert(m != n);
        assert(post.servers[m] == pre.servers[m]);
    }

    assert forall|l: Led| post.led.contains(l) implies won_election(
        post,
        l.server,
        l.term,
    ) by {
        lemma_quorum_survives(pre, post, l.server, l.term);
    }

    assert forall|l: Led| post.led.contains(l) && post.servers.contains_key(
        l.server,
    ) implies post.servers[l.server].current_term >= l.term && (post.servers[l.server].current_term
        == l.term ==> is_leader(post.servers[l.server])) by {
        if l.server == n {
            assert(pre.servers[n].current_term >= l.term);
            assert(term > pre.servers[n].current_term);
        } else {
            assert(post.servers[l.server] == pre.servers[l.server]);
        }
    }

    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_log_hist(pre, post);
}

/// Appending a client command. Roles, terms, votes and `led` are all untouched.
pub proof fn lemma_client_request_preserves_hist(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    value: nat,
)
    requires
        raft_hist_inv(pre),
        tr_client_request(pre, post, n, value),
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(
        pre,
        post,
        RaftStep::ClientRequest { server: n, value: value },
    );
    assert(post.servers.dom() =~= pre.servers.dom());
    assert forall|m: ServerId|
        #![trigger post.servers[m]]
        post.servers.contains_key(m) implies post.servers[m].role == pre.servers[m].role
        && post.servers[m].current_term == pre.servers[m].current_term by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
    lemma_roles_and_terms_unchanged_keep_hist(pre, post, n);
    lemma_client_request_writes_a_fresh_slot(pre, post, n, value);
}

/// **The slot a leader appends at has never been written.**
///
/// `inv_creator_holds` says every slot already created at this leader's term is
/// *inside* its log; the leader appends at the end of that log; so the slot it
/// is about to write is not one of them. One line of arithmetic, and the whole
/// reason the creation record is a function rather than a pile of claims.
///
/// What follows is the other half: no *other* server's log can hold an entry at
/// that slot either, because by [`inv_logs_follow_created`] every entry's slot
/// is in the record and this one is not. So inserting it disturbs nothing, and
/// every log that agreed with the record before still agrees with it.
pub proof fn lemma_client_request_writes_a_fresh_slot(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    value: nat,
)
    requires
        raft_hist_inv(pre),
        tr_client_request(pre, post, n, value),
    ensures
        inv_created_implies_led(post),
        inv_creator_holds(post),
        inv_logs_follow_created(post),
{
    let t = pre.servers[n].current_term;
    let len = pre.servers[n].log.len();
    let fresh = Slot { term: t, index: len };

    // The slot is new: if the record already had it, `inv_creator_holds` would
    // put it strictly inside a log of exactly that length.
    assert(!pre.created.contains_key(fresh));

    assert forall|s: Slot| post.created.contains_key(s) implies exists|w: ServerId|
        #[trigger] post.led.contains(Led { server: w, term: s.term }) by {
        if s == fresh {
            // The leader of `t` is on the record as having led `t`.
            assert(pre.led.contains(Led { server: n, term: t }));
            assert(post.led.contains(Led { server: n, term: t }));
        } else {
            // `post.created` is `pre.created` plus the one fresh slot, so any
            // other slot was already there — which is what lets
            // `inv_created_implies_led` be instantiated at it at all. Without
            // this the `choose` below has no existential to choose from and
            // picks an arbitrary server.
            assert(pre.created.contains_key(s));
            let w = choose|w: ServerId| pre.led.contains(Led { server: w, term: s.term });
            assert(post.led.contains(Led { server: w, term: s.term }));
        }
    }

    assert forall|m: ServerId, s: Slot|
        post.servers.contains_key(m) && is_leader(post.servers[m]) && post.servers[m].current_term
            == s.term && post.created.contains_key(s) implies s.index
        < post.servers[m].log.len() by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
            if s == fresh {
                // Two leaders of `t`, which Election Safety rules out.
                theorem_election_safety(pre, m, n);
                assert(false);
            }
        }
    }

    assert forall|m: ServerId, i: nat|
        post.servers.contains_key(m) && i < post.servers[m].log.len() implies {
        &&& post.created.contains_key(slot_of(post.servers[m].log, i))
        &&& post.created[slot_of(post.servers[m].log, i)].value
            == post.servers[m].log[i as int].value
        &&& post.created[slot_of(post.servers[m].log, i)].prev_term == term_before(
            post.servers[m].log,
            i,
        )
    } by {
        if m == n {
            if i < len {
                assert(post.servers[n].log[i as int] == pre.servers[n].log[i as int]);
                assert(slot_of(post.servers[n].log, i) != fresh);
            }
        } else {
            assert(post.servers[m] == pre.servers[m]);
            // An entry at the fresh slot would have put it in the record.
            assert(slot_of(post.servers[m].log, i) != fresh);
        }
    }
}

/// Advancing the commit point. Likewise.
pub proof fn lemma_advance_commit_preserves_hist(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    upto: nat,
)
    requires
        raft_hist_inv(pre),
        tr_advance_commit(pre, post, n, upto),
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(pre, post, RaftStep::AdvanceCommit { server: n, upto: upto });
    assert(post.servers.dom() =~= pre.servers.dom());
    lemma_untouched_logs_keep_log_hist(pre, post);
    assert forall|m: ServerId|
        #![trigger post.servers[m]]
        post.servers.contains_key(m) implies post.servers[m].role == pre.servers[m].role
        && post.servers[m].current_term == pre.servers[m].current_term by {
        if m != n {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
    lemma_roles_and_terms_unchanged_keep_hist(pre, post, n);
}

/// The shared shape of the two transitions that rewrite one server's *log* and
/// nothing else about it: the role and the term survive, so every clause holds
/// for the same reason it held before.
pub proof fn lemma_roles_and_terms_unchanged_keep_hist(pre: Cluster, post: Cluster, n: ServerId)
    requires
        raft_hist_inv(pre),
        post.members == pre.members,
        post.votes == pre.votes,
        post.led == pre.led,
        pre.servers.contains_key(n),
        post.servers.dom() == pre.servers.dom(),
        forall|m: ServerId|
            #![trigger post.servers[m]]
            post.servers.contains_key(m) ==> post.servers[m].role == pre.servers[m].role
                && post.servers[m].current_term == pre.servers[m].current_term,
    ensures
        inv_standing_implies_voted(post),
        inv_leader_is_led(post),
        inv_led_implies_won(post),
        inv_led_means_at_or_past(post),
{
    assert forall|m: ServerId| post.servers.contains_key(m) && (is_leader(post.servers[m])
        || is_candidate(post.servers[m])) implies has_voted(
        post,
        m,
        post.servers[m].current_term,
    ) by {
        let c0 = choose|c0: ServerId|
            pre.votes.contains(
                Vote { voter: m, term: pre.servers[m].current_term, candidate: c0 },
            );
        assert(post.votes.contains(
            Vote { voter: m, term: post.servers[m].current_term, candidate: c0 },
        ));
    }

    assert forall|l: Led| post.led.contains(l) implies won_election(
        post,
        l.server,
        l.term,
    ) by {
        lemma_quorum_survives(pre, post, l.server, l.term);
    }
}

/// Replication. The receiver becomes a follower, which is the case
/// `inv_led_means_at_or_past` has to work for — and two leaders of one term is
/// what rules out its receiver having been one.
pub proof fn lemma_append_entries_preserves_hist(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
)
    requires
        raft_hist_inv(pre),
        tr_append_entries(pre, post, leader, follower, prefix),
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(
        pre,
        post,
        RaftStep::AppendEntries { leader: leader, follower: follower, prefix: prefix },
    );

    assert forall|m: ServerId| post.servers.contains_key(m) && (is_leader(post.servers[m])
        || is_candidate(post.servers[m])) implies has_voted(
        post,
        m,
        post.servers[m].current_term,
    ) by {
        assert(m != follower);
        assert(post.servers[m] == pre.servers[m]);
        let c0 = choose|c0: ServerId|
            pre.votes.contains(
                Vote { voter: m, term: pre.servers[m].current_term, candidate: c0 },
            );
        assert(post.votes.contains(
            Vote { voter: m, term: post.servers[m].current_term, candidate: c0 },
        ));
    }

    assert forall|m: ServerId| post.servers.contains_key(m) && is_leader(
        post.servers[m],
    ) implies post.led.contains(
        Led { server: m, term: post.servers[m].current_term },
    ) by {
        assert(m != follower);
        assert(post.servers[m] == pre.servers[m]);
    }

    assert forall|l: Led| post.led.contains(l) implies won_election(
        post,
        l.server,
        l.term,
    ) by {
        lemma_quorum_survives(pre, post, l.server, l.term);
    }

    assert forall|l: Led| post.led.contains(l) && post.servers.contains_key(
        l.server,
    ) implies post.servers[l.server].current_term >= l.term && (post.servers[l.server].current_term
        == l.term ==> is_leader(post.servers[l.server])) by {
        if l.server == follower {
            // The term does not move, so what has to be ruled out is the
            // follower having been a leader of it — which would be two leaders
            // of one term, since the sender is one.
            assert(post.servers[follower].current_term == pre.servers[follower].current_term);
            if pre.servers[follower].current_term == l.term {
                assert(is_leader(pre.servers[follower]));
                theorem_election_safety(pre, leader, follower);
                assert(leader == follower);
                assert(false);
            }
        } else {
            assert(post.servers[l.server] == pre.servers[l.server]);
        }
    }

    lemma_the_consistency_check_preserves_the_record(pre, post, leader, follower, prefix);
}

/// **The consistency check is exactly the guard that keeps the record true.**
///
/// The one place in this development where a thing already in the protocol
/// turns out to be precisely what the proof needs, rather than something added
/// for it. A follower accepts the leader's entry at `prefix` and keeps its own
/// first `prefix` entries. For the record to stay true of the result:
///
/// * below `prefix` the entries are the follower's own and so is the term
///   before each of them, so nothing changed;
/// * **at `prefix` the entry is the leader's**, so its value and its slot come
///   from the leader's log, where the record already holds — but the *term
///   before it* is now the follower's entry at `prefix - 1`, not the leader's.
///   Those have to agree, or the record would claim a predecessor the follower
///   does not have.
///
/// And they do agree, because `tr_append_entries` will not fire unless
/// `follower.log[prefix - 1].term == leader.log[prefix - 1].term`. That is the
/// consistency check, and this is what it is for.
pub proof fn lemma_the_consistency_check_preserves_the_record(
    pre: Cluster,
    post: Cluster,
    leader: ServerId,
    follower: ServerId,
    prefix: nat,
)
    requires
        raft_hist_inv(pre),
        tr_append_entries(pre, post, leader, follower, prefix),
    ensures
        inv_created_implies_led(post),
        inv_creator_holds(post),
        inv_logs_follow_created(post),
{
    let fl = pre.servers[follower].log;
    let ll = pre.servers[leader].log;
    let nl = appended_log(fl, ll, prefix);

    assert(post.servers[follower].log == nl);
    // Only the conflicting branch fixes the length; the other keeps whatever
    // the follower had, which the guard says is at least `prefix`.
    assert(nl.len() >= prefix + 1);

    assert forall|s: Slot| post.created.contains_key(s) implies exists|w: ServerId|
        #[trigger] post.led.contains(Led { server: w, term: s.term }) by {
        let w = choose|w: ServerId| pre.led.contains(Led { server: w, term: s.term });
        assert(post.led.contains(Led { server: w, term: s.term }));
    }

    assert forall|m: ServerId, s: Slot|
        post.servers.contains_key(m) && is_leader(post.servers[m]) && post.servers[m].current_term
            == s.term && post.created.contains_key(s) implies s.index
        < post.servers[m].log.len() by {
        // The receiver is a follower afterwards, so it is not one of these.
        assert(m != follower);
        assert(post.servers[m] == pre.servers[m]);
    }

    assert forall|m: ServerId, i: nat|
        post.servers.contains_key(m) && i < post.servers[m].log.len() implies {
        &&& post.created.contains_key(slot_of(post.servers[m].log, i))
        &&& post.created[slot_of(post.servers[m].log, i)].value
            == post.servers[m].log[i as int].value
        &&& post.created[slot_of(post.servers[m].log, i)].prev_term == term_before(
            post.servers[m].log,
            i,
        )
    } by {
        if m == follower {
            if prefix < fl.len() && fl[prefix as int].term == ll[prefix as int].term {
                // **No conflict, so nothing was written.** The record held of
                // this log before and holds of it now, because it is the same
                // log. Note what this branch does *not* do: appeal to Log
                // Matching. That would be circular, since Log Matching is what
                // this invariant gives.
                assert(nl == fl);
            } else if i < prefix {
                // The follower's own entries, and its own predecessors.
                assert(nl[i as int] == fl[i as int]);
                assert(term_before(nl, i) == term_before(fl, i));
            } else {
                assert(i == prefix);
                // The leader's entry, where the record already holds.
                assert(nl[prefix as int] == ll[prefix as int]);
                assert(slot_of(nl, prefix) == slot_of(ll, prefix));
                // And the predecessors agree — the consistency check.
                assert(term_before(nl, prefix) == term_before(ll, prefix));
            }
        } else {
            assert(post.servers[m] == pre.servers[m]);
        }
    }
}

/// Replay and stutter. Nothing about a server or the history moves.
pub proof fn lemma_quiet_steps_preserve_hist(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_hist_inv(pre),
        raft_step(pre, post, s),
        post.members == pre.members,
        post.servers == pre.servers,
        post.votes == pre.votes,
        post.created == pre.created,
        post.led == pre.led,
    ensures
        raft_hist_inv(post),
{
    lemma_raft_step_preserves_inv(pre, post, s);
    assert forall|l: Led| post.led.contains(l) implies won_election(
        post,
        l.server,
        l.term,
    ) by {
        lemma_quorum_survives(pre, post, l.server, l.term);
    }
    lemma_untouched_logs_keep_log_hist(pre, post);
}

/// **Every transition preserves the history invariant.**
pub proof fn lemma_raft_step_preserves_hist(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_hist_inv(pre),
        raft_step(pre, post, s),
    ensures
        raft_hist_inv(post),
{
    match s {
        RaftStep::Timeout { server } => lemma_timeout_preserves_hist(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term, cand_last_term, cand_last_index } =>
            lemma_grant_vote_preserves_hist(
                pre,
                post,
                voter,
                candidate,
                term,
                cand_last_term,
                cand_last_index,
            ),
        RaftStep::BecomeLeader { server, term } => lemma_become_leader_preserves_hist(
            pre,
            post,
            server,
            term,
        ),
        RaftStep::StepDown { server, term } => lemma_step_down_preserves_hist(
            pre,
            post,
            server,
            term,
        ),
        RaftStep::ClientRequest { server, value } => lemma_client_request_preserves_hist(
            pre,
            post,
            server,
            value,
        ),
        RaftStep::AppendEntries { leader, follower, prefix } =>
            lemma_append_entries_preserves_hist(pre, post, leader, follower, prefix),
        RaftStep::AdvanceCommit { server, upto } => lemma_advance_commit_preserves_hist(
            pre,
            post,
            server,
            upto,
        ),
        RaftStep::Replay { msg } => lemma_quiet_steps_preserve_hist(
            pre,
            post,
            RaftStep::Replay { msg: msg },
        ),
        RaftStep::Stutter => lemma_quiet_steps_preserve_hist(pre, post, RaftStep::Stutter),
    }
}

/// An initial cluster satisfies it: nothing has been led, so three of the four
/// clauses are vacuous and the fourth is `raft_inv`'s.
pub proof fn lemma_init_hist_inv(c: Cluster)
    requires
        raft_init(c),
    ensures
        raft_hist_inv(c),
{
    lemma_raft_init_inv(c);
}

/// The unlabelled version, which is where the step is chosen.
///
/// Its own lemma rather than a `choose` inside the walk below, for the reason
/// `lemma_raft_next_preserves_inv` is: trigger inference for
/// `choose|s: RaftStep| raft_step(a, b, s)` needs `a` and `b` to be plain
/// variables. Written inline over `tr[i - 1]` and `tr[i]` the sequence
/// indexing gets in the way and Verus cannot infer a trigger at all.
pub proof fn lemma_raft_next_preserves_hist(pre: Cluster, post: Cluster)
    requires
        raft_hist_inv(pre),
        raft_next(pre, post),
    ensures
        raft_hist_inv(post),
{
    let s = choose|s: RaftStep| raft_step(pre, post, s);
    lemma_raft_step_preserves_hist(pre, post, s);
}

/// Walking an execution.
pub proof fn lemma_raft_execution_hist_inv(tr: Seq<Cluster>, i: int)
    requires
        raft_execution(tr),
        0 <= i < tr.len(),
    ensures
        raft_hist_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_init_hist_inv(tr[0]);
    } else {
        let j = i - 1;
        lemma_raft_execution_hist_inv(tr, j);
        // `raft_execution`'s multi-trigger needs a `tr[_ + 1]` term, which
        // `tr[i]` on its own does not provide.
        assert(raft_next(tr[j], tr[j + 1]));
        assert(tr[j + 1] == tr[i]);
        lemma_raft_next_preserves_hist(tr[j], tr[i]);
    }
}

/// **The history invariant holds in every reachable state.**
pub proof fn theorem_reachable_hist_inv(c: Cluster)
    requires
        raft_reachable(c),
    ensures
        raft_hist_inv(c),
{
    let tr = choose|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c;
    lemma_raft_execution_hist_inv(tr, tr.len() - 1);
}

// ---------------------------------------------------------------------------
// Log Matching
// ---------------------------------------------------------------------------

/// Two logs that agree on an entry's term at an index agree on its value.
///
/// Both are reading the same slot of the same record, so this is one step, and
/// it is the easy half.
pub proof fn theorem_log_matching_values(c: Cluster, a: ServerId, b: ServerId, i: nat)
    requires
        inv_logs_follow_created(c),
        c.servers.contains_key(a),
        c.servers.contains_key(b),
        i < c.servers[a].log.len(),
        i < c.servers[b].log.len(),
        c.servers[a].log[i as int].term == c.servers[b].log[i as int].term,
    ensures
        c.servers[a].log[i as int].value == c.servers[b].log[i as int].value,
{
    assert(slot_of(c.servers[a].log, i) == slot_of(c.servers[b].log, i));
}

/// **Log Matching.** Two logs that agree on an entry's term at an index agree
/// on every entry at and below it.
///
/// The hard half, and the induction the `prev_term` component of a creation
/// record exists to carry: the same slot gives the same recorded predecessor,
/// so the terms one index down agree — which is this theorem's own hypothesis,
/// one smaller.
pub proof fn theorem_log_matching(c: Cluster, a: ServerId, b: ServerId, i: nat)
    requires
        inv_logs_follow_created(c),
        c.servers.contains_key(a),
        c.servers.contains_key(b),
        i < c.servers[a].log.len(),
        i < c.servers[b].log.len(),
        c.servers[a].log[i as int].term == c.servers[b].log[i as int].term,
    ensures
        forall|j: int| 0 <= j <= i ==> c.servers[a].log[j] == c.servers[b].log[j],
    decreases i,
{
    theorem_log_matching_values(c, a, b, i);
    assert(slot_of(c.servers[a].log, i) == slot_of(c.servers[b].log, i));

    if i > 0 {
        assert(term_before(c.servers[a].log, i) == term_before(c.servers[b].log, i));
        theorem_log_matching(c, a, b, (i - 1) as nat);
    }

    assert forall|j: int| 0 <= j <= i implies c.servers[a].log[j] == c.servers[b].log[j] by {
        if j == i {
            assert(c.servers[a].log[j].term == c.servers[b].log[j].term);
            assert(c.servers[a].log[j].value == c.servers[b].log[j].value);
        }
    }
}

/// The same on prefixes, which is how the paper states it.
pub proof fn theorem_log_matching_prefixes(c: Cluster, a: ServerId, b: ServerId, i: nat)
    requires
        inv_logs_follow_created(c),
        c.servers.contains_key(a),
        c.servers.contains_key(b),
        i < c.servers[a].log.len(),
        i < c.servers[b].log.len(),
        c.servers[a].log[i as int].term == c.servers[b].log[i as int].term,
    ensures
        c.servers[a].log.take((i + 1) as int) == c.servers[b].log.take((i + 1) as int),
{
    theorem_log_matching(c, a, b, i);
    assert(c.servers[a].log.take((i + 1) as int) =~= c.servers[b].log.take((i + 1) as int));
}

/// **Log Matching, in any reachable cluster.**
pub proof fn theorem_log_matching_reachable(c: Cluster, a: ServerId, b: ServerId, i: nat)
    requires
        raft_reachable(c),
        c.servers.contains_key(a),
        c.servers.contains_key(b),
        i < c.servers[a].log.len(),
        i < c.servers[b].log.len(),
        c.servers[a].log[i as int].term == c.servers[b].log[i as int].term,
    ensures
        c.servers[a].log.take((i + 1) as int) == c.servers[b].log.take((i + 1) as int),
{
    theorem_reachable_hist_inv(c);
    theorem_log_matching_prefixes(c, a, b, i);
}

} // verus!
