//! An election that actually happens.
//!
//! `proofs::raft::theorem_election_safety` says at most one server leads a
//! term. A protocol in which nobody can ever be elected satisfies that
//! perfectly, and so does one whose transitions are all unreachable — the
//! theorem would be true, machine-checked, and empty.
//!
//! This module rules that out by construction. It builds a concrete three-server
//! cluster, walks it from initialisation through a real election, and exports
//! the run with every step named, so the timeout at index 0 is the one the vote
//! at index 1 answers and the leadership at index 2 is the one those two votes
//! bought.
//!
//! ```text
//! init                          0,1,2 all followers at term 0
//! Timeout(0)                    0 stands for term 1, voting for itself
//! GrantVote(1 -> 0, term 1)     1 grants; two of three have now voted for 0
//! BecomeLeader(0, term 1)       0 leads term 1
//! ```
//!
//! Three servers rather than two, on purpose: in a cluster of two a single
//! self-vote is already a majority, and the scenario would not exercise the
//! thing it exists to exercise — one server persuading another.
#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::raft::proofs::election::*;
use crate::raft::model::*;

verus! {

/// The three members of the scenario's cluster.
pub open spec fn three() -> Set<ServerId> {
    Set::empty().insert(0).insert(1).insert(2)
}

/// Everybody a follower at term 0.
pub open spec fn all_followers() -> Map<ServerId, Server> {
    Map::empty().insert(0, Server { role: Role::Follower, current_term: 0 }).insert(
        1,
        Server { role: Role::Follower, current_term: 0 },
    ).insert(2, Server { role: Role::Follower, current_term: 0 })
}

/// The initial cluster.
pub open spec fn start() -> Cluster {
    Cluster {
        members: three(),
        servers: all_followers(),
        votes: Set::empty(),
        messages: Set::empty(),
    }
}

/// The cluster has three members, and 0, 1 and 2 are all of them.
pub proof fn lemma_three_members()
    ensures
        three().len() == 3,
        three().contains(0),
        three().contains(1),
        three().contains(2),
{
}

/// The starting cluster is a legal initial state.
pub proof fn lemma_start_is_init()
    ensures
        raft_init(start()),
{
    assert forall|n: ServerId| start().members.contains(n) implies start().servers.contains_key(n)
        by {
        assert(n == 0 || n == 1 || n == 2);
    }
    assert forall|n: ServerId| start().servers.contains_key(n) implies !is_leader(
        start().servers[n],
    ) && start().servers[n].current_term == 0 by {
        assert(n == 0 || n == 1 || n == 2);
    }
}

/// **An election happens.**
///
/// Every successor state below is *defined* as the exact expression its
/// transition demands — `pre.servers.insert(..)`, `pre.votes.insert(..)` — so
/// the state equalities in each guard hold by construction and what is left to
/// prove is the part that is actually interesting: that the guards are
/// satisfied, and that two votes out of three really are a majority.
pub proof fn scenario_a_leader_is_elected()
    ensures
        exists|tr: Seq<Cluster>, labels: Seq<RaftStep>|
            {
                &&& #[trigger] raft_labelled_execution(tr, labels)
                &&& labels.len() == 3
                &&& labels[0] == (RaftStep::Timeout { server: 0 })
                &&& labels[1] == (RaftStep::GrantVote { voter: 1, candidate: 0, term: 1 })
                &&& labels[2] == (RaftStep::BecomeLeader { server: 0, term: 1 })
                // ... and at the end, server 0 leads term 1.
                &&& tr[3].servers.contains_key(0)
                &&& is_leader(tr[3].servers[0])
                &&& tr[3].servers[0].current_term == 1
                // ... having been put there by a majority, not by fiat.
                &&& won_election(tr[3], 0, 1)
            },
{
    lemma_three_members();
    lemma_start_is_init();

    let c0 = start();

    // 0 times out into term 1 and votes for itself.
    let c1 = Cluster {
        members: c0.members,
        servers: c0.servers.insert(0, Server { role: Role::Candidate, current_term: 1 }),
        votes: c0.votes.insert(Vote { voter: 0, term: 1, candidate: 0 }),
        messages: c0.messages.insert(RaftMessage::RequestVote { term: 1, candidate: 0 }),
    };
    assert(c0.servers[0].current_term == 0);
    assert(!is_leader(c0.servers[0]));
    assert(tr_timeout(c0, c1, 0));

    // 1 grants its vote. It has not voted in term 1 — nothing has, except 0 for
    // itself, and 0 is not 1.
    let c2 = Cluster {
        members: c1.members,
        servers: c1.servers.insert(1, Server { role: Role::Follower, current_term: 1 }),
        votes: c1.votes.insert(Vote { voter: 1, term: 1, candidate: 0 }),
        messages: c1.messages.insert(
            RaftMessage::VoteGranted { term: 1, voter: 1, candidate: 0 },
        ),
    };
    assert(c1.messages.contains(RaftMessage::RequestVote { term: 1, candidate: 0 }));
    assert(c1.servers[1].current_term == 0);
    assert forall|cand: ServerId| !c1.votes.contains(
        Vote { voter: 1, term: 1, candidate: cand },
    ) by {
        assert(!c0.votes.contains(Vote { voter: 1, term: 1, candidate: cand }));
    }
    assert(!has_voted(c1, 1, 1));
    assert(tr_grant_vote(c1, c2, 1, 0, 1));

    // Two of the three have now voted for 0 in term 1, which is a majority.
    assert(voters_for(c2, 0, 1) =~= Set::empty().insert(0).insert(1));
    assert(voters_for(c2, 0, 1).len() == 2);
    assert forall|n: ServerId| voters_for(c2, 0, 1).contains(n) implies c2.members.contains(n) by {}
    assert(voters_for(c2, 0, 1).subset_of(c2.members));
    assert(won_election(c2, 0, 1));

    // So 0 takes the term.
    let c3 = Cluster {
        members: c2.members,
        servers: c2.servers.insert(0, Server { role: Role::Leader, current_term: 1 }),
        votes: c2.votes,
        messages: c2.messages.insert(RaftMessage::Heartbeat { term: 1, leader: 0 }),
    };
    assert(is_candidate(c2.servers[0]));
    assert(tr_become_leader(c2, c3, 0, 1));

    let tr = seq![c0, c1, c2, c3];
    let labels = seq![
        RaftStep::Timeout { server: 0 },
        RaftStep::GrantVote { voter: 1, candidate: 0, term: 1 },
        RaftStep::BecomeLeader { server: 0, term: 1 },
    ];

    assert(tr.len() == 4);
    assert(labels.len() == 3);
    assert forall|i: int| 0 <= i < labels.len() implies raft_step(tr[i], tr[i + 1], labels[i]) by {
        if i == 0 {
            assert(tr[0] == c0 && tr[1] == c1);
        } else if i == 1 {
            assert(tr[1] == c1 && tr[2] == c2);
        } else {
            assert(i == 2);
            assert(tr[2] == c2 && tr[3] == c3);
        }
    }
    assert(raft_run(tr, labels));
    assert(tr[0] == c0);
    assert(raft_labelled_execution(tr, labels));

    // The endpoint, stated about the run rather than about `c3` alone.
    assert(tr[3] == c3);
    assert(is_leader(c3.servers[0]));
    lemma_quorum_survives(c2, c3, 0, 1);
    assert(won_election(c3, 0, 1));
}

/// The run reaches a state the safety theorem applies to, and in it the elected
/// leader is the *only* leader of its term.
///
/// This is the pairing that makes the scenario worth having: an election that
/// happens, ending in a state where Election Safety is not vacuous because
/// there is a leader for it to be about.
pub proof fn scenario_the_elected_leader_is_the_only_one(c: Cluster, other: ServerId)
    requires
        raft_inv(c),
        c.servers.contains_key(0),
        is_leader(c.servers[0]),
        c.servers[0].current_term == 1,
        c.servers.contains_key(other),
        is_leader(c.servers[other]),
        c.servers[other].current_term == 1,
    ensures
        other == 0,
{
    theorem_election_safety(c, 0, other);
}

} // verus!
