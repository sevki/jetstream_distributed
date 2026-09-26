//! **The summary a voter judged, tied back to the log it summarised.**
//!
//! # The hole this closes
//!
//! `crate::raft::proofs::votes` ends with
//! [`theorem_a_winner_shares_a_judged_voter_with_any_quorum`], which hands the
//! Leader Completeness induction a voter, that voter's log as it stood, and
//! `at_least_as_up_to_date(ct, ci, lg)`. Read the conclusion closely: `ct` and
//! `ci` are **two numbers**. Nothing in that theorem, or anywhere before it,
//! says they have anything to do with the winner's log.
//!
//! So the induction's third step — *the winner's log dominates what the voter
//! had* — was not available. What was available was *the winner's summary
//! dominates what the voter had*, which is a statement about a pair of integers
//! that arrived over the network. As far as any theorem in this repository said,
//! a candidate could have been elected on a summary it made up.
//!
//! That is the same class of gap as the one `@codex` found on #9: a conclusion
//! whose name promises more than its text. The difference is where it lived —
//! not in a wrapper's `ensures`, but in the *absence* of a link between two
//! parts of the model that the surrounding prose had been quietly assuming.
//!
//! # No fourth ghost record: the network is already a history variable
//!
//! The first three records exist because the state throws information away:
//! `created` because a log can be overwritten, `led` because a leader steps
//! down, `committed` because `Server::commit` retreats, `voted_with` because a
//! voter's log moves on. The obvious fourth would be *the candidate's log at
//! the moment it asked*.
//!
//! It is not needed, and the reason is worth naming: **`Cluster::messages` never
//! shrinks.** The `RequestVote` a candidate sent is still there, and it carries
//! the summary. So the link can be proved rather than recorded:
//!
//! * [`inv_a_recorded_summary_was_on_the_wire`] — every judgement on the record
//!   quotes a `RequestVote` that is still on the wire. Both writing transitions
//!   make this true by construction: [`tr_timeout`] sends the message it
//!   records, and [`tr_grant_vote`] is *guarded* by the message whose summary it
//!   copies.
//! * [`inv_a_requestvote_summarises_a_candidate`] — while its sender is still a
//!   standing candidate of that term, a `RequestVote`'s summary **is** a
//!   snapshot of the sender's log. It cannot have gone stale, because nothing
//!   that changes a server's log leaves it a candidate: [`tr_append_entries`]
//!   demotes its receiver and [`tr_client_request`] needs a leader.
//! * [`inv_a_requestvote_is_not_ahead_of_its_sender`] — a `RequestVote` never
//!   names a term its sender has not reached.
//!
//! # Why the third clause is what makes the second inductive
//!
//! The awkward case in preserving the second is [`tr_timeout`] itself. A server
//! stepping up to term `t` becomes a candidate of `t`, so every `RequestVote`
//! for `(t, n)` on the wire suddenly has to summarise its *new* log. The one it
//! just sent does. An **older** one would not have to, and would sink the
//! invariant — so the proof needs there to be no older one, which is exactly
//! the third clause: before the step the sender was at `t - 1`, and a
//! `RequestVote` for `t` from it would have named a term it had not reached.
//!
//! Put the other way round: a server enters a term once, because terms only
//! rise, and *that* is why one snapshot per `(sender, term)` is all there ever
//! is. The third clause is how that sentence becomes machine-checked.
//!
//! # What is proved here
//!
//! * [`theorem_a_candidate_is_judged_on_its_own_log`] — the summary a recorded
//!   vote was judged against is the candidate's real last term and real length.
//! * [`theorem_a_candidate_dominates_its_judged_voter`] — therefore **the
//!   candidate's own log** is at least as up to date as the voter's was.
//! * [`theorem_a_candidates_log_is_the_latest_its_voters_saw`] — and its last
//!   term dominates every entry those voters held. C43 and C50 again, with the
//!   winner's log in place of the pair of numbers.
//! * [`theorem_the_new_leaders_log_dominates_a_judged_voter`] — the same at the
//!   instant of [`tr_become_leader`], quantified over *any* quorum. This is the
//!   form Leader Completeness consumes: instantiate the quorum with the one that
//!   held a committed entry, and the conclusion is about the new leader's log,
//!   which is the object the property is about.
//!
//! # What is still missing
//!
//! The induction's second step — *the voter still held the entry when it voted*
//! — and it is still
//! [`crate::raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`]
//! with a hypothesis only the induction discharges. This module does not touch
//! it. What it does is make the third step a statement about a log instead of
//! about a pair of integers, so that when the second lands there is something
//! for it to meet.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::model::*;
use crate::raft::proofs::commit::*;
use crate::raft::proofs::election::*;
use crate::raft::proofs::history::*;
use crate::raft::proofs::terms::*;
use crate::raft::proofs::votes::*;

verus! {

// ---------------------------------------------------------------------------
// The invariants
// ---------------------------------------------------------------------------

/// Is this message a `RequestVote`?
///
/// A `match` with every field spelled out rather than `..` or an `is` test, for
/// the reason [`is_leader`] gives: nothing here should depend on which
/// enum-test syntax a Verus release happens to offer.
pub open spec fn is_request_vote(m: RaftMessage) -> bool {
    match m {
        RaftMessage::RequestVote { term: _, candidate: _, last_term: _, last_index: _ } => true,
        RaftMessage::VoteGranted { term: _, voter: _, candidate: _ } => false,
        RaftMessage::Heartbeat { term: _, leader: _ } => false,
    }
}

/// One message's worth of [`inv_a_requestvote_is_not_ahead_of_its_sender`].
///
/// Split out so that the invariant is a one-line quantifier and every proof
/// obligation about it is a named predicate rather than an inlined `match`.
pub open spec fn a_request_vote_is_not_ahead(c: Cluster, m: RaftMessage) -> bool {
    match m {
        RaftMessage::RequestVote { term: t, candidate: cand, last_term: _, last_index: _ } => {
            c.servers.contains_key(cand) ==> c.servers[cand].current_term >= t
        },
        RaftMessage::VoteGranted { term: _, voter: _, candidate: _ } => true,
        RaftMessage::Heartbeat { term: _, leader: _ } => true,
    }
}

/// One message's worth of [`inv_a_requestvote_summarises_a_candidate`].
pub open spec fn a_request_vote_summarises_its_sender(c: Cluster, m: RaftMessage) -> bool {
    match m {
        RaftMessage::RequestVote { term: t, candidate: cand, last_term: lt, last_index: li } => {
            c.servers.contains_key(cand) && is_candidate(c.servers[cand])
                && c.servers[cand].current_term == t ==> lt == last_term(c.servers[cand].log) && li
                == c.servers[cand].log.len()
        },
        RaftMessage::VoteGranted { term: _, voter: _, candidate: _ } => true,
        RaftMessage::Heartbeat { term: _, leader: _ } => true,
    }
}

/// One server's worth of the server-side obligation below: **it still exists, its
/// term did not fall, and it is not newly a candidate of the term it is at.**
///
/// Named rather than inlined because it appears in a `requires` and in two
/// `assert forall` blocks, and a hypothesis written out three times is a
/// hypothesis that can differ in one of them.
pub open spec fn candidacy_is_not_new(pre: Cluster, post: Cluster, k: ServerId) -> bool {
    &&& pre.servers.contains_key(k)
    &&& post.servers[k].current_term >= pre.servers[k].current_term
    &&& (is_candidate(post.servers[k]) && post.servers[k].current_term
        == pre.servers[k].current_term ==> is_candidate(pre.servers[k])
        && post.servers[k].log == pre.servers[k].log)
}

/// **Every judgement on the record quotes a `RequestVote` that is still on the
/// wire.**
///
/// The clause that makes the record and the network one story rather than two.
/// It is true by construction at both writing transitions — [`tr_timeout`] sends
/// the message it records, and [`tr_grant_vote`]'s *guard* is the message whose
/// summary it copies — and it survives everywhere else because `messages` never
/// shrinks.
pub open spec fn inv_a_recorded_summary_was_on_the_wire(c: Cluster) -> bool {
    forall|r: VoteLog|
        #[trigger]
        c.voted_with.contains(r) ==> c.messages.contains(
            RaftMessage::RequestVote {
                term: r.term,
                candidate: r.candidate,
                last_term: r.cand_last_term,
                last_index: r.cand_last_index,
            },
        )
}

/// **A `RequestVote` never names a term its sender has not reached.**
///
/// On its own this says little. What it buys is the preservation of the clause
/// below through [`tr_timeout`]: it is what rules out a *second, older*
/// `RequestVote` for the term a server is only now entering. See the module
/// docs — this is the machine-checked form of "a server enters a term once".
pub open spec fn inv_a_requestvote_is_not_ahead_of_its_sender(c: Cluster) -> bool {
    forall|m: RaftMessage| #[trigger] c.messages.contains(m) ==> a_request_vote_is_not_ahead(c, m)
}

/// **While its sender is still a standing candidate of that term, a
/// `RequestVote`'s summary is a snapshot of the sender's log.**
///
/// The load-bearing clause, and the whole content of this module. It is
/// inductive because nothing that can change a server's log leaves it a
/// candidate:
///
/// * [`tr_append_entries`] is the only transition that can truncate, and it
///   makes its receiver a `Follower`;
/// * [`tr_client_request`] is the only transition that can extend, and it needs
///   a `Leader`;
/// * [`tr_timeout`] does change who is a candidate, and it sends the matching
///   message as it does — see the module docs for why no stale one can be lying
///   around.
///
/// The restriction to a *standing* candidate is not a weakness. The only thing
/// the induction asks of a summary is what it meant while the winner was still a
/// candidate, which is the instant [`tr_become_leader`] fires. Afterwards the
/// log grows and the summary is genuinely stale, which is faithful: a leader's
/// `RequestVote` is spent.
pub open spec fn inv_a_requestvote_summarises_a_candidate(c: Cluster) -> bool {
    forall|m: RaftMessage|
        #[trigger]
        c.messages.contains(m) ==> a_request_vote_summarises_its_sender(c, m)
}

/// The three clauses together.
///
/// No other invariant bundle is carried: none of the three needs Election
/// Safety, Log Matching or the term shape. That is unusual here and worth
/// noticing — the argument is entirely about the network and one server's role,
/// so it stands on its own.
pub open spec fn raft_summary_inv(c: Cluster) -> bool {
    &&& inv_a_recorded_summary_was_on_the_wire(c)
    &&& inv_a_requestvote_is_not_ahead_of_its_sender(c)
    &&& inv_a_requestvote_summarises_a_candidate(c)
}

// ---------------------------------------------------------------------------
// Preservation
// ---------------------------------------------------------------------------

/// **A wire that only grows keeps the record's side of the bargain.**
///
/// Eight of the nine transitions record nothing, and for them this is the whole
/// of the first clause.
pub proof fn lemma_a_growing_wire_keeps_the_record(pre: Cluster, post: Cluster)
    requires
        inv_a_recorded_summary_was_on_the_wire(pre),
        post.voted_with == pre.voted_with,
        pre.messages.subset_of(post.messages),
    ensures
        inv_a_recorded_summary_was_on_the_wire(post),
{
    assert forall|r: VoteLog| post.voted_with.contains(r) implies post.messages.contains(
        RaftMessage::RequestVote {
            term: r.term,
            candidate: r.candidate,
            last_term: r.cand_last_term,
            last_index: r.cand_last_index,
        },
    ) by {
        assert(pre.voted_with.contains(r));
    }
}

/// **The two wire clauses survive any step that sends no `RequestVote` and makes
/// nobody a candidate of a term they were not a candidate of already.**
///
/// The second hypothesis is where the work is. Read it as three obligations on
/// every server: it still exists, its term did not fall, and if it is a
/// candidate *at the same term as before* then it was one before and its log is
/// untouched. That middle clause together with
/// [`inv_a_requestvote_is_not_ahead_of_its_sender`] is what collapses the
/// remaining case — a message's term cannot exceed its sender's before the step,
/// so a candidate at that term after the step was at it before too.
pub proof fn lemma_a_wire_that_gains_no_request_vote_keeps_the_summary(
    pre: Cluster,
    post: Cluster,
)
    requires
        inv_a_requestvote_is_not_ahead_of_its_sender(pre),
        inv_a_requestvote_summarises_a_candidate(pre),
        forall|m: RaftMessage|
            #![trigger post.messages.contains(m)]
            post.messages.contains(m) && is_request_vote(m) ==> pre.messages.contains(m),
        forall|k: ServerId|
            #![trigger post.servers.contains_key(k)]
            post.servers.contains_key(k) ==> candidacy_is_not_new(pre, post, k),
    ensures
        inv_a_requestvote_is_not_ahead_of_its_sender(post),
        inv_a_requestvote_summarises_a_candidate(post),
{
    assert forall|m: RaftMessage| post.messages.contains(m) implies a_request_vote_is_not_ahead(
        post,
        m,
    ) by {
        match m {
            RaftMessage::RequestVote { term: t, candidate: cand, last_term: _, last_index: _ } => {
                assert(is_request_vote(m));
                assert(pre.messages.contains(m));
                if post.servers.contains_key(cand) {
                    assert(candidacy_is_not_new(pre, post, cand));
                    assert(pre.servers.contains_key(cand));
                    assert(a_request_vote_is_not_ahead(pre, m));
                    assert(pre.servers[cand].current_term >= t);
                }
            },
            RaftMessage::VoteGranted { term: _, voter: _, candidate: _ } => {},
            RaftMessage::Heartbeat { term: _, leader: _ } => {},
        }
    }

    assert forall|m: RaftMessage|
        post.messages.contains(m) implies a_request_vote_summarises_its_sender(post, m) by {
        match m {
            RaftMessage::RequestVote { term: t, candidate: cand, last_term: lt, last_index: li } => {
                assert(is_request_vote(m));
                assert(pre.messages.contains(m));
                if post.servers.contains_key(cand) && is_candidate(post.servers[cand])
                    && post.servers[cand].current_term == t {
                    assert(candidacy_is_not_new(pre, post, cand));
                    assert(pre.servers.contains_key(cand));
                    // The message cannot name a term its sender had not
                    // reached, and the sender's term cannot have fallen — so
                    // the two terms are equal and the candidacy is not new.
                    assert(a_request_vote_is_not_ahead(pre, m));
                    assert(pre.servers[cand].current_term >= t);
                    assert(post.servers[cand].current_term >= pre.servers[cand].current_term);
                    assert(pre.servers[cand].current_term == post.servers[cand].current_term);
                    assert(is_candidate(pre.servers[cand]));
                    assert(post.servers[cand].log == pre.servers[cand].log);
                    assert(a_request_vote_summarises_its_sender(pre, m));
                    assert(lt == last_term(pre.servers[cand].log));
                    assert(li == pre.servers[cand].log.len());
                }
            },
            RaftMessage::VoteGranted { term: _, voter: _, candidate: _ } => {},
            RaftMessage::Heartbeat { term: _, leader: _ } => {},
        }
    }
}

/// The server-side hypothesis of the lemma above, discharged for a step that
/// replaces one server with something that is **not a candidate**.
///
/// Six of the nine transitions are of that shape: they demote their subject
/// ([`tr_grant_vote`], [`tr_step_down`], [`tr_append_entries`]), promote it past
/// candidacy ([`tr_become_leader`]), or leave a leader a leader
/// ([`tr_client_request`], [`tr_advance_commit`]).
pub proof fn lemma_a_step_that_makes_no_candidate_keeps_the_summary(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    replacement: Server,
)
    requires
        inv_a_requestvote_is_not_ahead_of_its_sender(pre),
        inv_a_requestvote_summarises_a_candidate(pre),
        pre.servers.contains_key(n),
        post.servers == pre.servers.insert(n, replacement),
        !is_candidate(replacement),
        replacement.current_term >= pre.servers[n].current_term,
        forall|m: RaftMessage|
            #![trigger post.messages.contains(m)]
            post.messages.contains(m) && is_request_vote(m) ==> pre.messages.contains(m),
    ensures
        inv_a_requestvote_is_not_ahead_of_its_sender(post),
        inv_a_requestvote_summarises_a_candidate(post),
{
    assert forall|k: ServerId|
        #![trigger post.servers.contains_key(k)]
        post.servers.contains_key(k) implies candidacy_is_not_new(pre, post, k) by {
        if k == n {
            assert(post.servers[k] == replacement);
        } else {
            assert(post.servers[k] == pre.servers[k]);
        }
    }
    lemma_a_wire_that_gains_no_request_vote_keeps_the_summary(pre, post);
}

/// The same for a step that touches no server at all — [`tr_replay`] and
/// [`tr_stutter`].
pub proof fn lemma_untouched_servers_keep_the_summary(pre: Cluster, post: Cluster)
    requires
        inv_a_requestvote_is_not_ahead_of_its_sender(pre),
        inv_a_requestvote_summarises_a_candidate(pre),
        post.servers == pre.servers,
        forall|m: RaftMessage|
            #![trigger post.messages.contains(m)]
            post.messages.contains(m) && is_request_vote(m) ==> pre.messages.contains(m),
    ensures
        inv_a_requestvote_is_not_ahead_of_its_sender(post),
        inv_a_requestvote_summarises_a_candidate(post),
{
    assert forall|k: ServerId|
        #![trigger post.servers.contains_key(k)]
        post.servers.contains_key(k) implies candidacy_is_not_new(pre, post, k) by {
        assert(post.servers[k] == pre.servers[k]);
    }
    lemma_a_wire_that_gains_no_request_vote_keeps_the_summary(pre, post);
}

/// **Standing for election** — the one transition that sends a `RequestVote`,
/// and the only interesting case.
///
/// The new message summarises the candidate's log by construction. The case with
/// content is an *older* `RequestVote` for the same `(sender, term)`: it would
/// now have to summarise the log too, and it need not. There is none, because
/// before the step the sender was at `term - 1` and
/// [`inv_a_requestvote_is_not_ahead_of_its_sender`] says no message names a term
/// its sender has not reached.
pub proof fn lemma_timeout_preserves_the_summary(pre: Cluster, post: Cluster, n: ServerId)
    requires
        raft_summary_inv(pre),
        tr_timeout(pre, post, n),
    ensures
        raft_summary_inv(post),
{
    let lg = pre.servers[n].log;
    let t = (pre.servers[n].current_term + 1) as nat;
    let sent = RaftMessage::RequestVote {
        term: t,
        candidate: n,
        last_term: last_term(lg),
        last_index: lg.len(),
    };
    let fresh = VoteLog {
        voter: n,
        term: t,
        candidate: n,
        voter_log: lg,
        cand_last_term: last_term(lg),
        cand_last_index: lg.len(),
    };
    assert(post.messages == pre.messages.insert(sent));
    assert(post.voted_with == pre.voted_with.insert(fresh));
    assert(post.servers[n].log == lg);
    assert(post.servers[n].current_term == t);

    // The record.
    assert forall|r: VoteLog| post.voted_with.contains(r) implies post.messages.contains(
        RaftMessage::RequestVote {
            term: r.term,
            candidate: r.candidate,
            last_term: r.cand_last_term,
            last_index: r.cand_last_index,
        },
    ) by {
        if r == fresh {
            assert(post.messages.contains(sent));
        } else {
            assert(pre.voted_with.contains(r));
        }
    }

    // No message names a term its sender has not reached.
    assert forall|m: RaftMessage| post.messages.contains(m) implies a_request_vote_is_not_ahead(
        post,
        m,
    ) by {
        match m {
            RaftMessage::RequestVote { term: mt, candidate: cand, last_term: _, last_index: _ } => {
                if post.servers.contains_key(cand) {
                    if m == sent {
                        assert(cand == n);
                        assert(mt == t);
                    } else {
                        assert(pre.messages.contains(m));
                        assert(pre.servers.contains_key(cand));
                        assert(a_request_vote_is_not_ahead(pre, m));
                        assert(pre.servers[cand].current_term >= mt);
                        if cand == n {
                            assert(post.servers[cand].current_term == t);
                        } else {
                            assert(post.servers[cand] == pre.servers[cand]);
                        }
                    }
                }
            },
            RaftMessage::VoteGranted { term: _, voter: _, candidate: _ } => {},
            RaftMessage::Heartbeat { term: _, leader: _ } => {},
        }
    }

    // The snapshot.
    assert forall|m: RaftMessage|
        post.messages.contains(m) implies a_request_vote_summarises_its_sender(post, m) by {
        match m {
            RaftMessage::RequestVote { term: mt, candidate: cand, last_term: lt, last_index: li } => {
                if post.servers.contains_key(cand) && is_candidate(post.servers[cand])
                    && post.servers[cand].current_term == mt {
                    if m == sent {
                        assert(cand == n);
                        assert(lt == last_term(lg));
                        assert(li == lg.len());
                        assert(post.servers[cand].log == lg);
                    } else {
                        assert(pre.messages.contains(m));
                        if cand == n {
                            // `mt == t == pre + 1`, and before the step no
                            // message on the wire named a term above `pre`.
                            assert(post.servers[cand].current_term == t);
                            assert(pre.servers.contains_key(cand));
                            assert(a_request_vote_is_not_ahead(pre, m));
                            assert(pre.servers[cand].current_term >= mt);
                            assert(false);
                        } else {
                            assert(post.servers[cand] == pre.servers[cand]);
                            assert(a_request_vote_summarises_its_sender(pre, m));
                            assert(lt == last_term(pre.servers[cand].log));
                            assert(li == pre.servers[cand].log.len());
                        }
                    }
                }
            },
            RaftMessage::VoteGranted { term: _, voter: _, candidate: _ } => {},
            RaftMessage::Heartbeat { term: _, leader: _ } => {},
        }
    }
}

/// **Granting a vote**, which records a judgement but sends no `RequestVote`.
///
/// The record it writes quotes the message its own guard required, so the first
/// clause is immediate. The rest is the demotion case of the helper above.
pub proof fn lemma_grant_vote_preserves_the_summary(
    pre: Cluster,
    post: Cluster,
    voter: ServerId,
    cand: ServerId,
    term: Term,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        raft_summary_inv(pre),
        tr_grant_vote(pre, post, voter, cand, term, cand_last_term, cand_last_index),
    ensures
        raft_summary_inv(post),
{
    let asked = RaftMessage::RequestVote {
        term: term,
        candidate: cand,
        last_term: cand_last_term,
        last_index: cand_last_index,
    };
    let granted = RaftMessage::VoteGranted { term: term, voter: voter, candidate: cand };
    let fresh = VoteLog {
        voter: voter,
        term: term,
        candidate: cand,
        voter_log: pre.servers[voter].log,
        cand_last_term: cand_last_term,
        cand_last_index: cand_last_index,
    };
    assert(pre.messages.contains(asked));
    assert(post.messages == pre.messages.insert(granted));
    assert(post.voted_with == pre.voted_with.insert(fresh));

    assert forall|r: VoteLog| post.voted_with.contains(r) implies post.messages.contains(
        RaftMessage::RequestVote {
            term: r.term,
            candidate: r.candidate,
            last_term: r.cand_last_term,
            last_index: r.cand_last_index,
        },
    ) by {
        if r == fresh {
            assert(post.messages.contains(asked));
        } else {
            assert(pre.voted_with.contains(r));
        }
    }

    assert forall|m: RaftMessage|
        #![trigger post.messages.contains(m)]
        post.messages.contains(m) && is_request_vote(m) implies pre.messages.contains(m) by {
        assert(m != granted);
    }
    let replacement = Server {
        role: Role::Follower,
        current_term: term,
        log: pre.servers[voter].log,
        commit: pre.servers[voter].commit,
    };
    assert(post.servers == pre.servers.insert(voter, replacement));
    assert(!is_candidate(replacement));
    lemma_a_step_that_makes_no_candidate_keeps_the_summary(pre, post, voter, replacement);
}

/// **Every transition preserves the summary invariant.**
pub proof fn lemma_raft_step_preserves_the_summary(pre: Cluster, post: Cluster, s: RaftStep)
    requires
        raft_summary_inv(pre),
        raft_step(pre, post, s),
    ensures
        raft_summary_inv(post),
{
    match s {
        RaftStep::Timeout { server } => lemma_timeout_preserves_the_summary(pre, post, server),
        RaftStep::GrantVote { voter, candidate, term, cand_last_term, cand_last_index } =>
            lemma_grant_vote_preserves_the_summary(
                pre,
                post,
                voter,
                candidate,
                term,
                cand_last_term,
                cand_last_index,
            ),
        RaftStep::BecomeLeader { server, term } => {
            let beat = RaftMessage::Heartbeat { term: term, leader: server };
            assert(post.messages == pre.messages.insert(beat));
            assert(pre.messages.subset_of(post.messages));
            lemma_a_growing_wire_keeps_the_record(pre, post);
            assert forall|m: RaftMessage|
                #![trigger post.messages.contains(m)]
                post.messages.contains(m) && is_request_vote(m) implies pre.messages.contains(
                m,
            ) by {
                assert(m != beat);
            }
            let replacement = Server {
                role: Role::Leader,
                current_term: term,
                log: pre.servers[server].log,
                commit: pre.servers[server].commit,
            };
            assert(!is_candidate(replacement));
            lemma_a_step_that_makes_no_candidate_keeps_the_summary(
                pre,
                post,
                server,
                replacement,
            );
        },
        RaftStep::StepDown { server, term } => {
            assert(pre.messages.subset_of(post.messages));
            lemma_a_growing_wire_keeps_the_record(pre, post);
            let replacement = Server {
                role: Role::Follower,
                current_term: term,
                log: pre.servers[server].log,
                commit: pre.servers[server].commit,
            };
            assert(!is_candidate(replacement));
            lemma_a_step_that_makes_no_candidate_keeps_the_summary(
                pre,
                post,
                server,
                replacement,
            );
        },
        RaftStep::ClientRequest { server, value } => {
            assert(pre.messages.subset_of(post.messages));
            lemma_a_growing_wire_keeps_the_record(pre, post);
            assert(is_leader(pre.servers[server]));
            let replacement = Server {
                role: pre.servers[server].role,
                current_term: pre.servers[server].current_term,
                log: pre.servers[server].log.push(
                    Entry { term: pre.servers[server].current_term, value: value },
                ),
                commit: pre.servers[server].commit,
            };
            assert(!is_candidate(replacement));
            lemma_a_step_that_makes_no_candidate_keeps_the_summary(
                pre,
                post,
                server,
                replacement,
            );
        },
        RaftStep::AppendEntries { leader, follower, prefix } => {
            assert(pre.messages.subset_of(post.messages));
            lemma_a_growing_wire_keeps_the_record(pre, post);
            let grown = appended_log(pre.servers[follower].log, pre.servers[leader].log, prefix);
            let replacement = Server {
                role: Role::Follower,
                current_term: pre.servers[follower].current_term,
                log: grown,
                commit: accepted_commit(
                    pre.servers[follower].commit,
                    pre.servers[leader].commit,
                    grown.len(),
                ),
            };
            assert(!is_candidate(replacement));
            lemma_a_step_that_makes_no_candidate_keeps_the_summary(
                pre,
                post,
                follower,
                replacement,
            );
        },
        RaftStep::AdvanceCommit { server, upto } => {
            assert(pre.messages.subset_of(post.messages));
            lemma_a_growing_wire_keeps_the_record(pre, post);
            assert(is_leader(pre.servers[server]));
            let replacement = Server {
                role: pre.servers[server].role,
                current_term: pre.servers[server].current_term,
                log: pre.servers[server].log,
                commit: upto,
            };
            assert(!is_candidate(replacement));
            lemma_a_step_that_makes_no_candidate_keeps_the_summary(
                pre,
                post,
                server,
                replacement,
            );
        },
        RaftStep::Replay { msg } => {
            assert(pre.messages.subset_of(post.messages));
            lemma_a_growing_wire_keeps_the_record(pre, post);
            assert forall|m: RaftMessage|
                #![trigger post.messages.contains(m)]
                post.messages.contains(m) && is_request_vote(m) implies pre.messages.contains(
                m,
            ) by {
                if m == msg {
                    assert(pre.messages.contains(msg));
                }
            }
            lemma_untouched_servers_keep_the_summary(pre, post);
        },
        RaftStep::Stutter => {
            assert(pre.messages.subset_of(post.messages));
            lemma_a_growing_wire_keeps_the_record(pre, post);
            assert forall|m: RaftMessage|
                #![trigger post.messages.contains(m)]
                post.messages.contains(m) && is_request_vote(m) implies pre.messages.contains(
                m,
            ) by {
            }
            lemma_untouched_servers_keep_the_summary(pre, post);
        },
    }
}

/// An initial cluster satisfies it: nothing has been sent and nothing recorded.
pub proof fn lemma_init_summary_inv(c: Cluster)
    requires
        raft_init(c),
    ensures
        raft_summary_inv(c),
{
}

/// The unlabelled version. Its own lemma for the trigger-inference reason
/// `lemma_raft_next_preserves_hist` documents.
pub proof fn lemma_raft_next_preserves_the_summary(pre: Cluster, post: Cluster)
    requires
        raft_summary_inv(pre),
        raft_next(pre, post),
    ensures
        raft_summary_inv(post),
{
    let s = choose|s: RaftStep| raft_step(pre, post, s);
    lemma_raft_step_preserves_the_summary(pre, post, s);
}

/// Walking an execution.
pub proof fn lemma_raft_execution_summary_inv(tr: Seq<Cluster>, i: int)
    requires
        raft_execution(tr),
        0 <= i < tr.len(),
    ensures
        raft_summary_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_init_summary_inv(tr[0]);
    } else {
        let j = i - 1;
        lemma_raft_execution_summary_inv(tr, j);
        assert(raft_next(tr[j], tr[j + 1]));
        assert(tr[j + 1] == tr[i]);
        lemma_raft_next_preserves_the_summary(tr[j], tr[i]);
    }
}

/// **The summary invariant holds in every reachable state.**
pub proof fn theorem_reachable_summary_inv(c: Cluster)
    requires
        raft_reachable(c),
    ensures
        raft_summary_inv(c),
{
    let tr = choose|tr: Seq<Cluster>| raft_execution(tr) && tr[tr.len() - 1] == c;
    lemma_raft_execution_summary_inv(tr, tr.len() - 1);
}

// ---------------------------------------------------------------------------
// What the link buys
// ---------------------------------------------------------------------------

/// **A standing candidate was judged on its own log** — its real last term and
/// its real length, not a pair of numbers that arrived from nowhere.
///
/// Two steps: the record quotes a message that is still on the wire, and while
/// its sender is still a candidate of that term the message summarises the
/// sender's log.
pub proof fn theorem_a_candidate_is_judged_on_its_own_log(c: Cluster, r: VoteLog)
    requires
        raft_summary_inv(c),
        c.voted_with.contains(r),
        c.servers.contains_key(r.candidate),
        is_candidate(c.servers[r.candidate]),
        c.servers[r.candidate].current_term == r.term,
    ensures
        r.cand_last_term == last_term(c.servers[r.candidate].log),
        r.cand_last_index == c.servers[r.candidate].log.len(),
{
    let m = RaftMessage::RequestVote {
        term: r.term,
        candidate: r.candidate,
        last_term: r.cand_last_term,
        last_index: r.cand_last_index,
    };
    assert(c.messages.contains(m));
    assert(a_request_vote_summarises_its_sender(c, m));
}

/// **A standing candidate's own log is at least as up to date as the log any of
/// its voters judged it against.**
///
/// [`inv_a_vote_was_up_to_date`] with the summary replaced by the thing it
/// summarises. This is the sentence the Leader Completeness roadmap has been
/// written as though it had all along.
pub proof fn theorem_a_candidate_dominates_its_judged_voter(c: Cluster, r: VoteLog)
    requires
        raft_summary_inv(c),
        inv_a_vote_was_up_to_date(c),
        c.voted_with.contains(r),
        c.servers.contains_key(r.candidate),
        is_candidate(c.servers[r.candidate]),
        c.servers[r.candidate].current_term == r.term,
    ensures
        at_least_as_up_to_date(
            last_term(c.servers[r.candidate].log),
            c.servers[r.candidate].log.len(),
            r.voter_log,
        ),
{
    theorem_a_candidate_is_judged_on_its_own_log(c, r);
}

/// **A standing candidate's log is at least as late, in terms, as every entry
/// any of its voters held.**
///
/// C43 and C50's term bound, restated about the candidate's log. This is the
/// form the induction's third step consumes: it rules out a winner whose log
/// stops before a term one of its voters had already seen.
pub proof fn theorem_a_candidates_log_is_the_latest_its_voters_saw(
    c: Cluster,
    r: VoteLog,
    i: nat,
)
    requires
        raft_summary_inv(c),
        inv_a_vote_was_up_to_date(c),
        inv_a_recorded_log_is_shaped(c),
        c.voted_with.contains(r),
        c.servers.contains_key(r.candidate),
        is_candidate(c.servers[r.candidate]),
        c.servers[r.candidate].current_term == r.term,
        i < r.voter_log.len(),
    ensures
        r.voter_log[i as int].term <= last_term(c.servers[r.candidate].log),
{
    theorem_a_voter_saw_nothing_later_than_the_candidate(c, r, i);
    theorem_a_candidate_is_judged_on_its_own_log(c, r);
}

/// **At the instant it wins, a new leader's own log dominates the log of a voter
/// it shares with any quorum whatsoever.**
///
/// The form Leader Completeness consumes, and the point of the module. C50
/// produced a shared voter and a pair of numbers; this produces a shared voter
/// and a statement about `post.servers[n].log` — the new leader's log, which is
/// the object Leader Completeness is about.
///
/// Instantiate `q` with the quorum
/// [`crate::raft::proofs::commit::theorem_a_commit_was_on_a_quorum`] produces,
/// and the shared voter both held the committed entry at commit time and judged
/// this leader's log at least as up to date as its own. What is still missing is
/// the step between those two moments —
/// [`crate::raft::proofs::commit::theorem_an_entry_persists_while_leaders_agree`]
/// and its hypothesis.
///
/// [`tr_become_leader`] is the right place to state it because it is the last
/// instant at which the winner is still a candidate, and therefore the last
/// instant at which its summary is its log. Afterwards the log grows and the
/// `RequestVote` is spent.
pub proof fn theorem_the_new_leaders_log_dominates_a_judged_voter(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
    q: Set<ServerId>,
) -> (shared: ServerId)
    requires
        raft_summary_inv(pre),
        raft_vote_inv(pre),
        tr_become_leader(pre, post, n, term),
        is_quorum(pre, q),
    ensures
        q.contains(shared),
        pre.votes.contains(Vote { voter: shared, term: term, candidate: n }),
        post.servers.contains_key(n),
        exists|lg: Seq<Entry>|
            #[trigger]
            pre.voted_with.contains(
                VoteLog {
                    voter: shared,
                    term: term,
                    candidate: n,
                    voter_log: lg,
                    cand_last_term: last_term(post.servers[n].log),
                    cand_last_index: post.servers[n].log.len(),
                },
            ) && at_least_as_up_to_date(
                last_term(post.servers[n].log),
                post.servers[n].log.len(),
                lg,
            ),
{
    let shared = theorem_a_winner_shares_a_judged_voter_with_any_quorum(pre, n, term, q);
    let w = choose|lg: Seq<Entry>, ct: Term, ci: nat|
        pre.voted_with.contains(
            VoteLog {
                voter: shared,
                term: term,
                candidate: n,
                voter_log: lg,
                cand_last_term: ct,
                cand_last_index: ci,
            },
        ) && at_least_as_up_to_date(ct, ci, lg);
    let r = VoteLog {
        voter: shared,
        term: term,
        candidate: n,
        voter_log: w.0,
        cand_last_term: w.1,
        cand_last_index: w.2,
    };
    assert(pre.voted_with.contains(r));
    assert(at_least_as_up_to_date(r.cand_last_term, r.cand_last_index, r.voter_log));
    theorem_a_candidate_is_judged_on_its_own_log(pre, r);
    assert(post.servers[n].log == pre.servers[n].log);
    assert(pre.voted_with.contains(
        VoteLog {
            voter: shared,
            term: term,
            candidate: n,
            voter_log: w.0,
            cand_last_term: last_term(post.servers[n].log),
            cand_last_index: post.servers[n].log.len(),
        },
    ));
    assert(at_least_as_up_to_date(
        last_term(post.servers[n].log),
        post.servers[n].log.len(),
        w.0,
    ));
    shared
}

/// The same for any reachable cluster, **with the existential repeated** — the
/// rule `theorem_a_winner_shares_a_judged_voter_with_any_quorum_reachable`
/// learned the hard way: a wrapper's contract is written, not inherited.
pub proof fn theorem_the_new_leaders_log_dominates_a_judged_voter_reachable(
    pre: Cluster,
    post: Cluster,
    n: ServerId,
    term: Term,
    q: Set<ServerId>,
) -> (shared: ServerId)
    requires
        raft_reachable(pre),
        tr_become_leader(pre, post, n, term),
        is_quorum(pre, q),
    ensures
        q.contains(shared),
        pre.votes.contains(Vote { voter: shared, term: term, candidate: n }),
        post.servers.contains_key(n),
        exists|lg: Seq<Entry>|
            #[trigger]
            pre.voted_with.contains(
                VoteLog {
                    voter: shared,
                    term: term,
                    candidate: n,
                    voter_log: lg,
                    cand_last_term: last_term(post.servers[n].log),
                    cand_last_index: post.servers[n].log.len(),
                },
            ) && at_least_as_up_to_date(
                last_term(post.servers[n].log),
                post.servers[n].log.len(),
                lg,
            ),
{
    theorem_reachable_summary_inv(pre);
    theorem_reachable_vote_inv(pre);
    theorem_the_new_leaders_log_dominates_a_judged_voter(pre, post, n, term, q)
}

} // verus!
