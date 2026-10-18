//! The executable steps agree with the model.
//!
//! The obligations [`crate::raft::proofs::refinement`] discharges for the Raft
//! steps: when a step fires, the model's transition fires, to exactly the state
//! computed; and when it refuses, the model's transition is not enabled in *any*
//! post-state. The second half carries the weight, because a step that refused
//! everything would satisfy the first perfectly.
//!
//! # The couplings
//!
//! A step sees answers; the model's state is a whole [`ActorSystem`]. The
//! correspondence is named as hypotheses rather than assumed:
//!
//! | Hypothesis | What supplies it |
//! | --- | --- |
//! | `may_write == can_mutate(c.own, c.actor, host, epoch)` | the ownership layer's own verified `may_write_step`, asked about the registry's current record — `ownership::proofs::refinement::theorem_may_write_step_is_the_system_fence` |
//! | `was_sent == c.sent.contains(env)` | the host's record of what has been sent |
//! | `accepted == accepted_from(c.journal, env.sender)` | the count the host keeps beside the journal |
//! | `c.own.live.contains(host)` | **the host is live**: the service has no `Crash` step, so it refines the crash-free executions, as `composed::service` does |
//!
//! The count is the one a host can get wrong, and getting it wrong is exactly
//! getting the guarantees wrong: an under-count accepts a duplicate, an
//! over-count refuses a message that is owed. [`lemma_accepted_from_push`] is
//! what keeps it right across an append.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::model::*;
use crate::actor::proofs::journal::*;
use crate::actor::steps::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;

verus! {

/// Where `Send` sends the system.
pub open spec fn send_post(c: ActorSystem, from: NodeId, body: nat) -> ActorSystem {
    ActorSystem {
        own: c.own,
        actor: c.actor,
        sent: c.sent.insert(Envelope { sender: from, seq: seq_of(c, from), body: body }),
        next_seq: c.next_seq.insert(from, seq_of(c, from) + 1),
        journal: c.journal,
    }
}

/// Where `Accept` sends it.
pub open spec fn accept_post(c: ActorSystem, host: NodeId, epoch: Epoch, env: Envelope) -> ActorSystem {
    ActorSystem {
        own: c.own,
        actor: c.actor,
        sent: c.sent,
        next_seq: c.next_seq,
        journal: c.journal.push(Entry { env: env, host: host, epoch: epoch }),
    }
}

/// When the sender's step fires, the model's `Send` fires, to exactly the state
/// computed.
pub proof fn theorem_send_step_refines(c: ActorSystem, from: NodeId, body: nat)
    requires
        c.own.live.contains(from),
    ensures
        as_send(c, send_post(c, from, body), from, body),
{
}

/// When the host's step fires, the model's `Accept` fires, to exactly the state
/// computed.
pub proof fn theorem_accept_step_refines(
    c: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
)
    requires
        c.own.live.contains(host),
        accept_fires(
            can_mutate(c.own, c.actor, host, epoch),
            c.sent.contains(env),
            env.seq,
            accepted_from(c.journal, env.sender),
        ),
    ensures
        as_accept(c, accept_post(c, host, epoch, env), host, epoch, env),
{
}

/// A refused append is a transition the model could not have taken either,
/// whatever state it was sent to.
pub proof fn theorem_accept_step_refuses_exactly_when_disabled(
    c: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
)
    requires
        !accept_fires(
            can_mutate(c.own, c.actor, host, epoch),
            c.sent.contains(env),
            env.seq,
            accepted_from(c.journal, env.sender),
        ),
    ensures
        !as_accept(c, post, host, epoch, env),
{
}

/// **The count stays right across an append.** After the model's `Accept`, the
/// count of messages from `env`'s sender is one more, and from anyone else's is
/// what it was. This is the fact a host leans on to keep its count beside the
/// journal without recounting.
pub proof fn theorem_accepting_advances_the_count_by_one(
    pre: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
    s: NodeId,
)
    requires
        as_accept(pre, post, host, epoch, env),
    ensures
        accepted_from(post.journal, s) == accepted_from(pre.journal, s) + if env.sender == s {
            1nat
        } else {
            0nat
        },
{
    lemma_accepted_from_push(pre.journal, Entry { env: env, host: host, epoch: epoch }, s);
}

/// **The fence answer is `can_mutate`.** The step is handed `may_write_step`'s
/// answer about the registry's own record; that is the model's authority guard.
pub proof fn theorem_the_fence_answer_is_the_models_authority(
    c: ActorSystem,
    st: crate::ownership::steps::ExecState,
    host: u64,
    epoch: u64,
)
    requires
        c.own.actors.contains_key(c.actor),
        c.own.actors[c.actor] == st.view(),
    ensures
        may_mutate(st.view(), host as nat, epoch as nat) == can_mutate(
            c.own,
            c.actor,
            host as nat,
            epoch as nat,
        ),
{
}

} // verus!
