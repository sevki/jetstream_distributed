//! The election record is the model.
//!
//! [`crate::raft::exec::ElectionCore`] keeps a server's role and term, whom it
//! voted for in that term, and the votes it has counted. These theorems say what
//! its contracts come to against [`crate::raft::model`]: given a cluster the core
//! stands for, a core that takes an election step stands for the cluster the
//! model's transition leads to.
//!
//! # The relation
//!
//! [`stands_for`] has four parts, and the second and third are the ones
//! [`crate::raft::proofs::refinement`] names as hypotheses of its step theorems:
//!
//! * the role and term are the cluster's;
//! * **the vote**: if the core says it voted for `x` in its term, the cluster
//!   holds that vote; if it says it has not voted, the cluster holds none by this
//!   server in that term. That is `already_voted == has_voted(c, n, term)` as an
//!   equality, and `grant_vote_step` is only as good as it;
//! * **the tally** is a subset of the voters for this server's candidacy:
//!   every vote it counted was cast. That is `has_quorum ⇒ won_election`;
//! * no vote by this server is ahead of its term — an invariant of the model
//!   (a vote is cast in the voter's own term), which is what makes a vote in a
//!   higher term impossible to have already given.
//!
//! # What is not here
//!
//! The log, the commit point, the roster, the lock and the durable store. A
//! ballot is counted only if it was *granted for this term*; the theorems take
//! "the vote was cast" as a hypothesis, which is what receiving a `Granted`
//! reply supplies.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;
use vstd::set_lib::*;

use crate::raft::exec::*;
use crate::raft::model::*;
use crate::raft::proofs::refinement::*;
use crate::raft::steps::*;

verus! {

/// Every vote by `n` is in a term no later than `n`'s own.
pub open spec fn no_vote_ahead(c: Cluster, n: Id) -> bool {
    forall|v: Vote| #[trigger] c.votes.contains(v) && v.voter == n ==> v.term <= c.servers[n].current_term
}

/// The core stands for server `n` of the cluster.
pub open spec fn stands_for(core: ElectionCore, c: Cluster, n: Id) -> bool {
    &&& c.servers.contains_key(n)
    &&& c.servers[n].role == core.server.role.view()
    &&& c.servers[n].current_term == core.server.current_term as nat
    &&& (core.voted_for matches Some(x) ==> c.votes.contains(
        Vote { voter: n, term: core.server.current_term as nat, candidate: x },
    ))
    &&& (core.voted_for is None ==> !has_voted(c, n, core.server.current_term as nat))
    &&& core.tally@.subset_of(voters_for(c, n, core.server.current_term as nat))
    &&& no_vote_ahead(c, n)
}

/// **A vote not yet given in a term is not given by the cluster either**, in any
/// term at or ahead of the server's own — which is why the core's
/// `already_voted` is the model's `has_voted`.
pub proof fn lemma_already_voted_is_has_voted(core: ElectionCore, c: Cluster, n: Id, term: nat)
    requires
        stands_for(core, c, n),
        term >= core.server.current_term as nat,
    ensures
        (core.server.current_term as nat == term && core.voted_for is Some) == has_voted(c, n, term),
{
    let cur = core.server.current_term as nat;
    if cur == term {
        if core.voted_for is Some {
            let x = core.voted_for.unwrap();
            assert(c.votes.contains(Vote { voter: n, term: term, candidate: x }));
        }
    } else {
        if has_voted(c, n, term) {
            let cand = choose|cand: Id|
                c.votes.contains(Vote { voter: n, term: term, candidate: cand });
            let v = Vote { voter: n, term: term, candidate: cand };
            assert(c.votes.contains(v) && v.voter == n);
            assert(v.term <= cur);
        }
    }
}

/// **`stand` is `tr_timeout`**: the next term, a self-vote on the network's
/// books, and a tally of one that is the cluster's.
pub proof fn theorem_stand_is_tr_timeout(
    core: ElectionCore,
    core2: ElectionCore,
    c: Cluster,
    n: Id,
)
    requires
        stands_for(core, c, n),
        c.members.contains(n),
        timeout_fires(core.server.role.view()),
        core2.server.role.view() == Role::Candidate,
        core2.server.current_term as nat == core.server.current_term as nat + 1,
        core2.voted_for == Some(n),
        core2.tally@ == Set::<Id>::empty().insert(n),
    ensures
        tr_timeout(c, timeout_post(c, n), n),
        stands_for(core2, timeout_post(c, n), n),
{
    theorem_timeout_step_refines_tr_timeout(c, n);
    let post = timeout_post(c, n);
    let t = core2.server.current_term as nat;
    let v = Vote { voter: n, term: t, candidate: n };
    assert(post.votes.contains(v));
    assert(voters_for(post, n, t).contains(n)) by {
        assert(post.members.contains(n));
    }
    assert(core2.tally@.subset_of(voters_for(post, n, t)));
    assert forall|w: Vote| #[trigger] post.votes.contains(w) && w.voter == n implies w.term
        <= post.servers[n].current_term by {
        if w != v {
            assert(c.votes.contains(w));
        }
    }
}

/// **A refused `stand` is a step the model could not take.**
pub proof fn theorem_refused_stand_is_disabled(
    core: ElectionCore,
    c: Cluster,
    post: Cluster,
    n: Id,
)
    requires
        stands_for(core, c, n),
        !timeout_fires(core.server.role.view()),
    ensures
        !tr_timeout(c, post, n),
{
    theorem_timeout_step_refuses_exactly_when_disabled(c, post, n);
}

/// **A fresh `grant` is `tr_grant_vote`**, for a request on the network from a
/// candidate whose log is at least as up to date as ours.
pub proof fn theorem_grant_is_tr_grant_vote(
    core: ElectionCore,
    core2: ElectionCore,
    c: Cluster,
    voter: Id,
    cand: Id,
    term: nat,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        stands_for(core, c, voter),
        c.members.contains(voter),
        c.members.contains(cand),
        c.messages.contains(
            RaftMessage::RequestVote {
                term: term,
                candidate: cand,
                last_term: cand_last_term,
                last_index: cand_last_index,
            },
        ),
        at_least_as_up_to_date(cand_last_term, cand_last_index, c.servers[voter].log),
        grant_vote_fires(
            core.server.current_term as nat,
            term,
            core.server.current_term as nat == term && core.voted_for is Some,
        ),
        core2.server.role.view() == Role::Follower,
        core2.server.current_term as nat == term,
        core2.voted_for == Some(cand),
        core.server.current_term as nat == term ==> core2.tally@ == core.tally@,
        core.server.current_term as nat != term ==> forall|m: Id| !core2.tally@.contains(m),
    ensures
        tr_grant_vote(
            c,
            grant_vote_post(c, voter, cand, term, cand_last_term, cand_last_index),
            voter,
            cand,
            term,
            cand_last_term,
            cand_last_index,
        ),
        stands_for(core2, grant_vote_post(c, voter, cand, term, cand_last_term, cand_last_index), voter),
{
    lemma_already_voted_is_has_voted(core, c, voter, term);
    theorem_grant_vote_step_refines_tr_grant_vote(
        c,
        voter,
        cand,
        term,
        cand_last_term,
        cand_last_index,
    );
    let post = grant_vote_post(c, voter, cand, term, cand_last_term, cand_last_index);
    let v = Vote { voter: voter, term: term, candidate: cand };
    assert(post.votes.contains(v));
    assert forall|m: Id| core2.tally@.contains(m) implies voters_for(
        post,
        voter,
        term,
    ).contains(m) by {
        if core.server.current_term as nat == term {
            assert(voters_for(c, voter, term).contains(m));
            assert(c.members.contains(m) && c.votes.contains(Vote { voter: m, term: term, candidate: voter }));
            assert(post.votes.contains(Vote { voter: m, term: term, candidate: voter }));
        }
    }
    assert forall|w: Vote| #[trigger] post.votes.contains(w) && w.voter == voter implies w.term
        <= post.servers[voter].current_term by {
        if w != v {
            assert(c.votes.contains(w));
            assert(w.term <= c.servers[voter].current_term);
        }
    }
}

/// **A refused `grant` — a request the vote guard forbids — is a step the model
/// could not take.** A refusal for a log that is behind is a refusal of the
/// model's `at_least_as_up_to_date`, the other half of the same guard.
pub proof fn theorem_refused_grant_is_disabled(
    core: ElectionCore,
    c: Cluster,
    post: Cluster,
    voter: Id,
    cand: Id,
    term: nat,
    cand_last_term: Term,
    cand_last_index: nat,
)
    requires
        stands_for(core, c, voter),
        term >= core.server.current_term as nat,
        !grant_vote_fires(
            core.server.current_term as nat,
            term,
            core.server.current_term as nat == term && core.voted_for is Some,
        ),
    ensures
        !tr_grant_vote(c, post, voter, cand, term, cand_last_term, cand_last_index),
{
    lemma_already_voted_is_has_voted(core, c, voter, term);
    theorem_grant_vote_step_refuses_exactly_when_disabled(
        c,
        post,
        voter,
        cand,
        term,
        cand_last_term,
        cand_last_index,
    );
}

/// **A refusal for a log that is behind is a step the model could not take**,
/// provided the caller's `up_to_date` is the model's comparison of the
/// candidate's last entry with the voter's own log. `grant` takes the verdict as
/// an argument; this is the statement of what the verdict has to be, and the
/// caller supplying it is the hypothesis.
pub proof fn theorem_refused_stale_log_is_disabled(
    core: ElectionCore,
    c: Cluster,
    post: Cluster,
    voter: Id,
    cand: Id,
    term: nat,
    cand_last_term: Term,
    cand_last_index: nat,
    up_to_date: bool,
)
    requires
        stands_for(core, c, voter),
        up_to_date == at_least_as_up_to_date(cand_last_term, cand_last_index, c.servers[voter].log),
        !up_to_date,
    ensures
        !tr_grant_vote(c, post, voter, cand, term, cand_last_term, cand_last_index),
{
}

/// **Taking the term on a majority is `tr_become_leader`.** The tally is a set of
/// voters who each voted, so a majority of it is a quorum of the cluster's votes.
pub proof fn theorem_a_won_count_is_tr_become_leader(
    core: ElectionCore,
    core2: ElectionCore,
    c: Cluster,
    n: Id,
    term: nat,
    members: u64,
)
    requires
        stands_for(core, c, n),
        members as nat == c.members.len(),
        core.server.current_term as nat == term,
        core.tally@.len() + core.tally@.len() > members as nat,
        core.tally@.len() <= members as nat,
        become_leader_fires(core.server.role.view(), term, term, true),
        core2.server.role.view() == Role::Leader,
        core2.server.current_term == core.server.current_term,
        core2.voted_for == core.voted_for,
        core2.tally@ == core.tally@,
    ensures
        tr_become_leader(c, become_leader_post(c, n, term), n, term),
        stands_for(core2, become_leader_post(c, n, term), n),
{
    let voters = voters_for(c, n, term);
    assert(core.tally@.subset_of(voters));
    lemma_len_subset(core.tally@, voters);
    assert(voters.subset_of(c.members));
    assert(is_quorum(c, voters));
    assert(won_election(c, n, term));
    theorem_become_leader_step_refines_tr_become_leader(c, n, term);
    let post = become_leader_post(c, n, term);
    assert(post.votes == c.votes);
    assert(voters_for(post, n, term) == voters);
}

/// **A count that does not win is not a win the model would allow** — if the
/// tally is not a majority of what the cluster actually voted, the election is
/// not won; the other direction, "the tally undercounts", is the model's to be
/// slow about, not unsound.
pub proof fn theorem_a_lost_count_is_disabled(
    core: ElectionCore,
    c: Cluster,
    post: Cluster,
    n: Id,
    term: nat,
)
    requires
        stands_for(core, c, n),
        !become_leader_fires(
            c.servers[n].role,
            c.servers[n].current_term,
            term,
            won_election(c, n, term),
        ),
    ensures
        !tr_become_leader(c, post, n, term),
{
    theorem_become_leader_step_refuses_exactly_when_disabled(c, post, n, term);
}

/// **`step_down` is `tr_step_down`**, and the vote and tally go with the old term.
pub proof fn theorem_step_down_is_tr_step_down(
    core: ElectionCore,
    core2: ElectionCore,
    c: Cluster,
    n: Id,
    term: nat,
)
    requires
        stands_for(core, c, n),
        carries_term(c, term),
        step_down_fires(core.server.current_term as nat, term),
        core2.server.role.view() == Role::Follower,
        core2.server.current_term as nat == term,
        core2.voted_for is None,
        forall|m: Id| !core2.tally@.contains(m),
    ensures
        tr_step_down(c, step_down_post(c, n, term), n, term),
        stands_for(core2, step_down_post(c, n, term), n),
{
    theorem_step_down_step_refines_tr_step_down(c, n, term);
    let post = step_down_post(c, n, term);
    assert(post.votes == c.votes);
    assert(!has_voted(post, n, term)) by {
        if has_voted(post, n, term) {
            let cand = choose|cand: Id|
                post.votes.contains(Vote { voter: n, term: term, candidate: cand });
            let v = Vote { voter: n, term: term, candidate: cand };
            assert(c.votes.contains(v) && v.voter == n);
            assert(v.term <= c.servers[n].current_term);
        }
    }
    assert forall|w: Vote| #[trigger] post.votes.contains(w) && w.voter == n implies w.term
        <= post.servers[n].current_term by {
        assert(c.votes.contains(w));
        assert(w.term <= c.servers[n].current_term);
    }
    assert forall|m: Id| core2.tally@.contains(m) implies voters_for(post, n, term).contains(m) by {}
}

/// **A `step_down` to a term that is not ahead is not the model's either.**
pub proof fn theorem_a_refused_step_down_is_disabled(
    core: ElectionCore,
    c: Cluster,
    post: Cluster,
    n: Id,
    term: nat,
)
    requires
        stands_for(core, c, n),
        !step_down_fires(core.server.current_term as nat, term),
    ensures
        !tr_step_down(c, post, n, term),
{
    theorem_step_down_step_refuses_exactly_when_disabled(c, post, n, term);
}

/// **`yield_to` is the role change `tr_append_entries` makes on its follower**,
/// at an equal term; term, vote and (now empty) tally are kept consistent.
pub proof fn theorem_yield_is_the_append_role_change(
    core: ElectionCore,
    core2: ElectionCore,
    c: Cluster,
    post: Cluster,
    leader: Id,
    n: Id,
    prefix: nat,
)
    requires
        stands_for(core, c, n),
        tr_append_entries(c, post, leader, n, prefix),
        core2.server.role.view() == Role::Follower,
        core2.server.current_term == core.server.current_term,
        core2.voted_for == core.voted_for,
        forall|m: Id| !core2.tally@.contains(m),
    ensures
        stands_for(core2, post, n),
{
    assert(post.votes == c.votes);
    assert forall|m: Id| core2.tally@.contains(m) implies voters_for(
        post,
        n,
        core2.server.current_term as nat,
    ).contains(m) by {}
    assert forall|w: Vote| #[trigger] post.votes.contains(w) && w.voter == n implies w.term
        <= post.servers[n].current_term by {
        assert(c.votes.contains(w));
    }
}

} // verus!
