//! **The guarantees are not vacuous.** One concrete run, written out in full:
//! the actor is taken by host `A`, which accepts a message; it is handed over to
//! `B` through the whole ownership protocol; `B` accepts the next message. Then
//! the refusals the theorems promise are exhibited in the state it ends in.
//!
//! Every theorem in this directory is an implication under hypotheses, and an
//! implication whose hypotheses cannot all hold at once is true and says
//! nothing. This run is the check the theorems cannot perform on themselves: if
//! [`as_accept`]'s guards could not hold together with the ownership protocol's
//! real transitions, it would stop verifying.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::actor::model::*;
use crate::actor::proofs::delivery::*;
use crate::actor::proofs::exclusive::*;
use crate::actor::proofs::invariant::*;
use crate::actor::proofs::journal::*;
use crate::actor::proofs::state::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;

verus! {

// Node 1 is `A`, node 2 is `B`; `B` is also the sender. The actor is 0.

pub open spec fn sc_actor() -> Id {
    Id(0)
}

pub open spec fn sc_a() -> Id {
    Id(1)
}

pub open spec fn sc_b() -> Id {
    Id(2)
}

pub open spec fn sc_env0() -> Envelope {
    Envelope { sender: Id(2), seq: 0, body: 7 }
}

pub open spec fn sc_env1() -> Envelope {
    Envelope { sender: Id(2), seq: 1, body: 9 }
}

/// The ownership layer at each point of the run.
pub open spec fn sc_own(k: int) -> OwnershipSystem {
    let nodes = Set::<Id>::empty().insert(Id(1)).insert(Id(2));
    let grant_a = Message::Grant { actor: Id(0), to: Id(1), epoch: 41 };
    let revoke = Message::Revoke { actor: Id(0), target: Id(1), old_epoch: 41, new_epoch: 42 };
    let released = Message::Released { actor: Id(0), from: Id(1), new_epoch: 42 };
    let grant_b = Message::Grant { actor: Id(0), to: Id(2), epoch: 42 };
    let tok_a = Token { actor: Id(0), epoch: 41, holder: Id(1) };
    let tok_b = Token { actor: Id(0), epoch: 42, holder: Id(2) };
    let unowned_a = Map::<Id, OwnershipState>::empty().insert(
        Id(0),
        OwnershipState::Unowned { epoch: 41, intended_owner: Id(1) },
    );
    let owned_a = Map::<Id, OwnershipState>::empty().insert(
        Id(0),
        OwnershipState::Owned { owner: Id(1), epoch: 41 },
    );
    let moving = Map::<Id, OwnershipState>::empty().insert(
        Id(0),
        OwnershipState::Transferring { from: Id(1), to: Id(2), old_epoch: 41, new_epoch: 42 },
    );
    let unowned_b = Map::<Id, OwnershipState>::empty().insert(
        Id(0),
        OwnershipState::Unowned { epoch: 42, intended_owner: Id(2) },
    );
    let owned_b = Map::<Id, OwnershipState>::empty().insert(
        Id(0),
        OwnershipState::Owned { owner: Id(2), epoch: 42 },
    );
    if k == 0 {
        OwnershipSystem {
            actors: unowned_a,
            nodes: nodes,
            live: nodes,
            issued: Set::empty(),
            network: Set::empty(),
        }
    } else if k == 1 {
        OwnershipSystem {
            actors: unowned_a,
            nodes: nodes,
            live: nodes,
            issued: Set::empty(),
            network: Set::empty().insert(grant_a),
        }
    } else if k == 2 {
        OwnershipSystem {
            actors: owned_a,
            nodes: nodes,
            live: nodes,
            issued: Set::empty().insert(tok_a),
            network: Set::empty().insert(grant_a),
        }
    } else if k == 3 {
        OwnershipSystem {
            actors: moving,
            nodes: nodes,
            live: nodes,
            issued: Set::empty().insert(tok_a),
            network: Set::empty().insert(grant_a).insert(revoke),
        }
    } else if k == 4 {
        OwnershipSystem {
            actors: moving,
            nodes: nodes,
            live: nodes,
            issued: Set::empty().insert(tok_a),
            network: Set::empty().insert(grant_a).insert(revoke).insert(released),
        }
    } else if k == 5 {
        OwnershipSystem {
            actors: unowned_b,
            nodes: nodes,
            live: nodes,
            issued: Set::empty().insert(tok_a),
            network: Set::empty().insert(grant_a).insert(revoke).insert(released).insert(grant_b),
        }
    } else {
        OwnershipSystem {
            actors: owned_b,
            nodes: nodes,
            live: nodes,
            issued: Set::empty().insert(tok_a).insert(tok_b),
            network: Set::empty().insert(grant_a).insert(revoke).insert(released).insert(grant_b),
        }
    }
}

pub open spec fn sc_entry0() -> Entry {
    Entry { env: sc_env0(), host: Id(1), epoch: 41 }
}

pub open spec fn sc_entry1() -> Entry {
    Entry { env: sc_env1(), host: Id(2), epoch: 42 }
}

/// The whole actor system at each of the eleven points of the run.
pub open spec fn sc_state(k: int) -> ActorSystem {
    let sent0 = Set::<Envelope>::empty().insert(sc_env0());
    let sent1 = sent0.insert(sc_env1());
    let seq1 = Map::<Id, nat>::empty().insert(Id(2), 1nat);
    let seq2 = Map::<Id, nat>::empty().insert(Id(2), 2nat);
    let j1 = Seq::<Entry>::empty().push(sc_entry0());
    let j2 = j1.push(sc_entry1());
    if k <= 2 {
        ActorSystem {
            own: sc_own(k),
            actor: Id(0),
            sent: Set::empty(),
            next_seq: Map::empty(),
            journal: Seq::empty(),
        }
    } else if k == 3 {
        ActorSystem {
            own: sc_own(2),
            actor: Id(0),
            sent: sent0,
            next_seq: seq1,
            journal: Seq::empty(),
        }
    } else if k == 4 {
        ActorSystem { own: sc_own(2), actor: Id(0), sent: sent0, next_seq: seq1, journal: j1 }
    } else if k <= 8 {
        ActorSystem { own: sc_own(k - 2), actor: Id(0), sent: sent0, next_seq: seq1, journal: j1 }
    } else if k == 9 {
        ActorSystem { own: sc_own(6), actor: Id(0), sent: sent1, next_seq: seq2, journal: j1 }
    } else {
        ActorSystem { own: sc_own(6), actor: Id(0), sent: sent1, next_seq: seq2, journal: j2 }
    }
}

/// The label of each step of the run.
pub open spec fn sc_label(i: int) -> ActorStep {
    if i == 0 {
        ActorStep::Own { own_step: Step::IssueGrant { actor: Id(0) } }
    } else if i == 1 {
        ActorStep::Own { own_step: Step::Acquire { actor: Id(0), node: Id(1) } }
    } else if i == 2 {
        ActorStep::Send { from: Id(2), body: 7 }
    } else if i == 3 {
        ActorStep::Accept { host: Id(1), epoch: 41, env: sc_env0() }
    } else if i == 4 {
        ActorStep::Own { own_step: Step::BeginTransfer { actor: Id(0), from: Id(1), to: Id(2) } }
    } else if i == 5 {
        ActorStep::Own {
            own_step: Step::HandleRevoke {
                actor: Id(0),
                target: Id(1),
                old_epoch: 41,
                new_epoch: 42,
            },
        }
    } else if i == 6 {
        ActorStep::Own { own_step: Step::CompleteRelease { actor: Id(0) } }
    } else if i == 7 {
        ActorStep::Own { own_step: Step::Acquire { actor: Id(0), node: Id(2) } }
    } else if i == 8 {
        ActorStep::Send { from: Id(2), body: 9 }
    } else {
        ActorStep::Accept { host: Id(2), epoch: 42, env: sc_env1() }
    }
}

/// Each point of the run steps to the next by the step that is labelled.
pub proof fn lemma_sc_step(i: int)
    requires
        0 <= i < 10,
    ensures
        actor_step(sc_state(i), sc_state(i + 1), sc_label(i)),
{
    if i == 0 {
        assert(tr_issue_grant(sc_own(0), sc_own(1), Id(0)));
    } else if i == 1 {
        assert(sc_own(1).network.contains(Message::Grant { actor: Id(0), to: Id(1), epoch: 41 }));
        assert(sc_own(2).actors =~= sc_own(1).actors.insert(
            Id(0),
            OwnershipState::Owned { owner: Id(1), epoch: 41 },
        ));
        assert(tr_acquire(sc_own(1), sc_own(2), Id(0), Id(1)));
    } else if i == 2 {
        assert(as_send(sc_state(2), sc_state(3), Id(2), 7));
    } else if i == 3 {
        assert(can_mutate(sc_own(2), Id(0), Id(1), 41));
        assert(sc_state(3).sent.contains(sc_env0()));
        assert(accepted_from(Seq::<Entry>::empty(), Id(2)) == 0);
        assert(as_accept(sc_state(3), sc_state(4), Id(1), 41, sc_env0()));
    } else if i == 4 {
        assert(sc_own(3).actors =~= sc_own(2).actors.insert(
            Id(0),
            OwnershipState::Transferring { from: Id(1), to: Id(2), old_epoch: 41, new_epoch: 42 },
        ));
        assert(tr_begin_transfer(sc_own(2), sc_own(3), Id(0), Id(1), Id(2)));
    } else if i == 5 {
        assert(tr_handle_revoke(sc_own(3), sc_own(4), Id(0), Id(1), 41, 42));
    } else if i == 6 {
        assert(sc_own(5).actors =~= sc_own(4).actors.insert(
            Id(0),
            OwnershipState::Unowned { epoch: 42, intended_owner: Id(2) },
        ));
        assert(tr_complete_release(sc_own(4), sc_own(5), Id(0)));
    } else if i == 7 {
        assert(sc_own(5).network.contains(Message::Grant { actor: Id(0), to: Id(2), epoch: 42 }));
        assert(sc_own(6).actors =~= sc_own(5).actors.insert(
            Id(0),
            OwnershipState::Owned { owner: Id(2), epoch: 42 },
        ));
        assert(tr_acquire(sc_own(5), sc_own(6), Id(0), Id(2)));
    } else if i == 8 {
        assert(seq_of(sc_state(8), Id(2)) == 1);
        assert(sc_state(9).next_seq =~= sc_state(8).next_seq.insert(Id(2), 2nat));
        assert(as_send(sc_state(8), sc_state(9), Id(2), 9));
    } else {
        assert(can_mutate(sc_own(6), Id(0), Id(2), 42));
        assert(sc_state(9).sent.contains(sc_env1()));
        assert(accepted_from(Seq::<Entry>::empty(), Id(2)) == 0);
        lemma_accepted_from_push(Seq::<Entry>::empty(), sc_entry0(), Id(2));
        assert(accepted_from(sc_state(9).journal, Id(2)) == 1);
        assert(as_accept(sc_state(9), sc_state(10), Id(2), 42, sc_env1()));
    }
}

/// The states of the run, as a sequence.
pub open spec fn sc_tr() -> Seq<ActorSystem> {
    Seq::new(11, |i: int| sc_state(i))
}

/// The labels of the run, as a sequence.
pub open spec fn sc_labels() -> Seq<ActorStep> {
    Seq::new(10, |i: int| sc_label(i))
}

/// **The run is an execution of the actor system** — from `actor_init`, by the
/// labelled steps above, through the ownership protocol's real transitions.
pub proof fn scenario_the_run_is_an_execution()
    ensures
        actor_run(sc_tr(), sc_labels()),
        actor_execution(sc_tr()),
        actor_reachable(sc_state(10)),
{
    let tr = sc_tr();
    let labels = sc_labels();
    assert(tr.len() == 11);
    assert(labels.len() == 10);
    assert forall|i: int| 0 <= i < labels.len() implies actor_step(
        #[trigger] tr[i],
        tr[i + 1],
        labels[i],
    ) by {
        lemma_sc_step(i);
    }
    assert(actor_init(tr[0])) by {
        assert(tr[0] == sc_state(0));
        assert(init(sc_own(0)));
    }
    assert forall|i: int| 0 <= i < tr.len() - 1 implies actor_next(#[trigger] tr[i], tr[i + 1]) by {
        lemma_sc_step(i);
        assert(actor_step(tr[i], tr[i + 1], sc_label(i)));
    }
    assert(actor_execution(tr));
    assert(tr[tr.len() - 1] == sc_state(10));
    assert(actor_execution(tr) && tr[tr.len() - 1] == sc_state(10));
}

/// **The run ends where the guarantees say it should.** Two entries, written by
/// two different hosts under two different epochs, in the order they were sent;
/// and the state is the behaviour applied to them in that order — which is not
/// the order that would give the same answer, since `apply` does not commute.
pub proof fn scenario_the_run_ends_with_both_hosts_in_the_journal()
    ensures
        sc_state(10).journal.len() == 2,
        sc_state(10).journal[0] == sc_entry0(),
        sc_state(10).journal[1] == sc_entry1(),
        sc_entry0().host != sc_entry1().host,
        sc_entry0().epoch < sc_entry1().epoch,
        state_of(sc_state(10).journal) == 226,
{
    let j1 = Seq::<Entry>::empty().push(sc_entry0());
    let j2 = j1.push(sc_entry1());
    assert(sc_state(10).journal == j2);
    assert(state_of(Seq::<Entry>::empty()) == 0);
    lemma_state_of_push(Seq::<Entry>::empty(), sc_entry0());
    lemma_state_of_push(j1, sc_entry1());
    assert(state_of(j1) == 7);
    assert(state_of(j2) == 226);
}

/// **The old host, still believing, is refused.** `A` hosted the actor at epoch
/// 41 and does not know it has been handed over; whatever it presents, nothing
/// is appended.
pub proof fn scenario_the_old_host_is_refused(post: ActorSystem, env: Envelope)
    ensures
        !as_accept(sc_state(10), post, Id(1), 41, env),
{
    assert(sc_own(6).actors.contains_key(Id(0)));
    assert(sc_state(10).own == sc_own(6));
    theorem_a_superseded_host_cannot_accept(sc_state(10), post, Id(1), 41, env);
}

/// **A redelivered message is refused**, by the current host at the current
/// epoch — the one pair that is otherwise allowed to append.
pub proof fn scenario_a_redelivery_is_refused(post: ActorSystem)
    ensures
        !as_accept(sc_state(10), post, Id(2), 42, sc_env0()),
        !as_accept(sc_state(10), post, Id(2), 42, sc_env1()),
{
    scenario_the_run_is_an_execution();
    theorem_reachable_inv(sc_state(10));
    theorem_a_redelivered_message_is_refused(sc_state(10), post, Id(2), 42, sc_env0(), 0);
    theorem_a_redelivered_message_is_refused(sc_state(10), post, Id(2), 42, sc_env1(), 1);
}

} // verus!
