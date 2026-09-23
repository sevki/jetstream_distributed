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
//! So `Cluster` now carries two ghost fields — [`Cluster::created`] and
//! [`Cluster::led`] — and this module is what they buy.
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
//! The `created` half — and Log Matching with it — is the next piece of work.
//! The record is kept here; the theorems about it are not yet written, and this
//! module claims nothing about it.
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
pub open spec fn with_history(c: Cluster, cr: Map<Slot, Creation>, l: Set<Led>) -> Cluster {
    Cluster {
        members: c.members,
        servers: c.servers,
        votes: c.votes,
        messages: c.messages,
        created: cr,
        led: l,
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

/// **The history neither enables nor disables anything.**
///
/// For *any* `cr` and `l` — not the ones the run actually produced, any at all
/// — the same step is available from the same real state and lands in the same
/// real state. A guard that read the history could not satisfy this: it would
/// be a step available under one history and not under another.
///
/// This is what makes `created` and `led` auxiliary variables rather than an
/// assumption wearing a struct field's clothes. Everything else in this module
/// rests on it, and so does the right to say the model is still Raft.
pub proof fn theorem_history_does_not_gate_the_protocol(
    pre: Cluster,
    post: Cluster,
    s: RaftStep,
    cr: Map<Slot, Creation>,
    l: Set<Led>,
)
    requires
        raft_step(pre, post, s),
    ensures
        raft_step(
            with_history(pre, cr, l),
            with_history(post, created_after(pre, cr, s), led_after(pre, l, s)),
            s,
        ),
{
    match s {
        RaftStep::Timeout { server: _ } => {},
        RaftStep::GrantVote {
            voter: _,
            candidate: _,
            term: _,
            cand_last_term: _,
            cand_last_index: _,
        } => {},
        RaftStep::BecomeLeader { server: _, term: _ } => {},
        RaftStep::StepDown { server: _, term: _ } => {},
        RaftStep::ClientRequest { server: _, value: _ } => {},
        RaftStep::AppendEntries { leader: _, follower: _, prefix: _ } => {},
        RaftStep::AdvanceCommit { server: _, upto: _ } => {},
        RaftStep::Replay { msg: _ } => {},
        RaftStep::Stutter => {},
    }
}

/// History only ever grows. Neither field has a transition that removes from it,
/// which is what makes "has ever" the right reading of both.
pub proof fn theorem_history_is_monotone(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_step(pre, post, s),
    ensures
        pre.led.subset_of(post.led),
        forall|sl: Slot| #[trigger] pre.created.contains_key(sl) ==> post.created.contains_key(sl),
{
    match s {
        RaftStep::BecomeLeader { server: _, term: _ } => {},
        RaftStep::ClientRequest { server: _, value: _ } => {},
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

/// The history invariant, which carries `raft_inv` with it because two of its
/// clauses need Election Safety to survive a step.
pub open spec fn raft_hist_inv(c: Cluster) -> bool {
    &&& raft_inv(c)
    &&& inv_standing_implies_voted(c)
    &&& inv_leader_is_led(c)
    &&& inv_led_implies_won(c)
    &&& inv_led_means_at_or_past(c)
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
}

/// Replay and stutter. Nothing about a server or the history moves.
pub proof fn lemma_quiet_steps_preserve_hist(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_hist_inv(pre),
        raft_step(pre, post, s),
        post.members == pre.members,
        post.servers == pre.servers,
        post.votes == pre.votes,
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
        lemma_raft_execution_hist_inv(tr, i - 1);
        assert(raft_next(tr[i - 1], tr[i]));
        let s = choose|s: RaftStep| raft_step(tr[i - 1], tr[i], s);
        lemma_raft_step_preserves_hist(tr[i - 1], tr[i], s);
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

} // verus!
