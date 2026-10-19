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
//! | `next == seq_of(c, from)` | the sender's counter, kept by the host beside `sent` |
//! | `accepted == accepted_from(c.journal, env.sender)` | the count the host keeps beside the journal |
//! | `c.own.live.contains(host)` | **the host is live**: the service has no `Crash` step, so it refines the crash-free executions, as `composed::service` does |
//!
//! The count is the one a host can get wrong, and getting it wrong is exactly
//! getting the guarantees wrong: an under-count accepts a duplicate, an
//! over-count refuses a message that is owed. [`lemma_accepted_from_push`] is
//! what keeps it right across an append.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;

use crate::actor::model::*;
use crate::actor::proofs::journal::*;
use crate::actor::steps::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;

verus! {

/// Where `Send` sends the system.
pub open spec fn send_post(c: ActorSystem, from: HostId, body: nat) -> ActorSystem {
    ActorSystem {
        own: c.own,
        actor: c.actor,
        sent: c.sent.insert(Envelope { sender: from, seq: seq_of(c, from), body: body }),
        next_seq: c.next_seq.insert(from, seq_of(c, from) + 1),
        journal: c.journal,
    }
}

/// Where `Accept` sends it.
pub open spec fn accept_post(c: ActorSystem, host: HostId, epoch: Epoch, env: Envelope) -> ActorSystem {
    ActorSystem {
        own: c.own,
        actor: c.actor,
        sent: c.sent,
        next_seq: c.next_seq,
        journal: c.journal.push(Entry { env: env, host: host, epoch: epoch }),
    }
}

/// When the sender's step fires, the model's `Send` fires, to exactly the state
/// computed — and the number the step hands out, and the counter it leaves, are
/// the model's.
///
/// `send_step(next)` returns `Ok(next)` exactly when [`send_fires`] holds. Given
/// the coupling `next == seq_of(c, from)`, the envelope it numbers is the one
/// [`send_post`] adds to `sent`, the counter it stores is `next + 1`, and that
/// still fits the `u64` it is kept in because `send_fires` says `next < u64::MAX`.
pub proof fn theorem_send_step_refines(c: ActorSystem, from: HostId, body: nat, next: u64)
    requires
        c.own.live.contains(from),
        next as nat == seq_of(c, from),
        send_fires(next as nat),
    ensures
        as_send(c, send_post(c, from, body), from, body),
        send_post(c, from, body).sent.contains(
            Envelope { sender: from, seq: next as nat, body: body },
        ),
        send_post(c, from, body).next_seq[from] == next as nat + 1,
        next as nat + 1 <= u64::MAX as nat,
{
}

/// **Where the executable sender is narrower than the model, and only there.**
/// `send_step` refuses only with the counter at `u64::MAX`, and at that point the
/// model's `Send` is still enabled: the model's counter is a `nat`. The service
/// refuses rather than wrapping, because a wrapped counter would repeat a number
/// and the accept guard would take the repeat for a duplicate. So the refinement
/// holds below the bound and at the bound the executable does less than the model
/// allows, which is safe — the model's guarantees are about what *is* accepted.
pub proof fn theorem_send_step_refuses_only_at_exhaustion(
    c: ActorSystem,
    from: HostId,
    body: nat,
    next: u64,
)
    requires
        c.own.live.contains(from),
        next as nat == seq_of(c, from),
        !send_fires(next as nat),
    ensures
        next == u64::MAX,
        as_send(c, send_post(c, from, body), from, body),
{
}

/// When the host's step fires, the model's `Accept` fires, to exactly the state
/// computed.
pub proof fn theorem_accept_step_refines(
    c: ActorSystem,
    host: HostId,
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

/// **Where the executable host is narrower than the model, and only there.**
/// `accept_step` refuses an append the model enables only with `Exhausted`, and
/// only with the count at `u64::MAX`: its contract says a refusal is either a
/// disabled `Accept` (the theorem below) or [`accept_has_room`] failing. The
/// model's count is a `nat`, so there `Accept` is still enabled. The host
/// refuses rather than wrapping, because a wrapped count would take a repeat
/// for a message it had not seen. Like the sender's, this is the safe direction:
/// the model's guarantees are about what *is* accepted.
pub proof fn theorem_accept_step_refuses_an_enabled_append_only_at_exhaustion(
    c: ActorSystem,
    host: HostId,
    epoch: Epoch,
    env: Envelope,
    accepted: u64,
)
    requires
        c.own.live.contains(host),
        accepted as nat == accepted_from(c.journal, env.sender),
        accept_fires(
            can_mutate(c.own, c.actor, host, epoch),
            c.sent.contains(env),
            env.seq,
            accepted as nat,
        ),
        !accept_has_room(accepted as nat),
    ensures
        accepted == u64::MAX,
        as_accept(c, accept_post(c, host, epoch, env), host, epoch, env),
{
}

/// A refused append is a transition the model could not have taken either,
/// whatever state it was sent to — except at exhaustion, which the theorem above
/// states.
pub proof fn theorem_accept_step_refuses_exactly_when_disabled(
    c: ActorSystem,
    post: ActorSystem,
    host: HostId,
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
    host: HostId,
    epoch: Epoch,
    env: Envelope,
    s: HostId,
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
    host: HostId,
    epoch: u64,
)
    requires
        c.own.actors.contains_key(c.actor),
        c.own.actors[c.actor] == st.view(),
    ensures
        may_mutate(st.view(), host, epoch as nat) == can_mutate(
            c.own,
            c.actor,
            host,
            epoch as nat,
        ),
{
}

} // verus!
