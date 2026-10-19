//! The state space of a distributed actor, and the transitions between states.
//!
//! This defines only the machine. It makes no claims about it; those are in
//! [`crate::actor::proofs`].
//!
//! # The journal is the state
//!
//! A host does not *have* the actor's state. The actor's state is
//! [`state_of`] its [`ActorSystem::journal`], the ordered sequence of messages
//! it has accepted, and any host that can read the journal can recompute it.
//! That one decision is what makes migration trivial and the guarantees
//! provable: there is no state to ship, only a log to keep linear.
//!
//! Keeping it linear is the ownership protocol's job. [`as_accept`] — the only
//! transition that writes the journal — requires
//! [`crate::ownership::spec::can_mutate`] at the epoch the host presents, which
//! is `Owned { host, epoch }` and nothing else. A host that is not the owner, or
//! is the owner of a generation that has been superseded, is refused. Nothing
//! about the actor needs a second fence: the journal write *is* the mutation the
//! ownership protocol fences.
//!
//! # The network
//!
//! [`ActorSystem::sent`] is every message ever sent and is never consumed, so a
//! message can be offered to the host any number of times, in any order, at any
//! later point — the same convention as `OwnershipSystem::network` and
//! `Raymond::requests`. Duplication, reordering and delay are therefore not
//! failure modes added to the model; they are what an `Accept` step is *already*
//! quantified over.
//!
//! # Ordering
//!
//! A sender numbers its messages from zero ([`as_send`]). The host accepts a
//! message only if its number is exactly the count of messages already accepted
//! from that sender. That single guard is both the duplicate filter (a message
//! already accepted has a number below the count) and the order filter (a message
//! ahead of the count is refused until the ones before it arrive).
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;

verus! {

/// One message. `sender` and `seq` identify it; `body` is what the actor's
/// behaviour reads.
pub struct Envelope {
    pub sender: HostId,
    pub seq: nat,
    pub body: nat,
}

/// One accepted message, with who accepted it and under which fencing epoch.
///
/// The host and epoch are not needed to *compute* the actor's state. They are
/// the evidence of who wrote each entry, which is what lets the proofs say that
/// no two hosts ever wrote under the same epoch.
pub struct Entry {
    pub env: Envelope,
    pub host: HostId,
    pub epoch: Epoch,
}

/// The size of the machine word the actor's state lives in.
pub open spec fn word() -> nat {
    18446744073709551616
}

/// The actor's behaviour: what a message does to its state.
///
/// Deterministic, and that is the only thing that matters about it — every
/// theorem here holds for any function. It is not commutative, so a journal
/// processed in the wrong order would visibly give a different state.
///
/// Taken modulo [`word`] so that the state fits the `u64` a host keeps it in:
/// the model's state is a `nat`, and a behaviour that grew without bound would
/// make the executable one narrower than the model for a reason unrelated to
/// anything the actor guarantees.
pub open spec fn apply(state: nat, body: nat) -> nat {
    (state * 31 + body) % word()
}

/// The messages accepted from `sender` in `journal`.
pub open spec fn accepted_from(journal: Seq<Entry>, sender: HostId) -> nat
    decreases journal.len(),
{
    if journal.len() == 0 {
        0
    } else {
        accepted_from(journal.drop_last(), sender) + if journal.last().env.sender == sender {
            1nat
        } else {
            0nat
        }
    }
}

/// The actor's state: the fold of its behaviour over its journal.
pub open spec fn state_of(journal: Seq<Entry>) -> nat
    decreases journal.len(),
{
    if journal.len() == 0 {
        0
    } else {
        apply(state_of(journal.drop_last()), journal.last().env.body)
    }
}

/// One actor, the ownership protocol that fences it, and the messages in flight.
pub struct ActorSystem {
    /// The ownership layer: who owns the actor, at which epoch.
    pub own: OwnershipSystem,
    /// The actor this system is about.
    pub actor: ActorId,
    /// Every message ever sent. Never shrinks; see the module docs.
    pub sent: Set<Envelope>,
    /// Each sender's next sequence number. A sender with no entry is at zero.
    pub next_seq: Map<HostId, nat>,
    /// The messages the actor has accepted, in order. The actor's state.
    pub journal: Seq<Entry>,
}

/// `n`'s next sequence number.
pub open spec fn seq_of(c: ActorSystem, n: HostId) -> nat {
    if c.next_seq.contains_key(n) {
        c.next_seq[n]
    } else {
        0
    }
}

/// `from` sends a message, numbered after the last one it sent.
///
/// No host is named. A sender addresses the actor, not the machine it happens to
/// be on; which host may process the message is decided by the ownership layer
/// when it is accepted, not when it is sent.
pub open spec fn as_send(pre: ActorSystem, post: ActorSystem, from: HostId, body: nat) -> bool {
    &&& pre.own.live.contains(from)
    &&& post.sent == pre.sent.insert(Envelope { sender: from, seq: seq_of(pre, from), body })
    &&& post.next_seq == pre.next_seq.insert(from, seq_of(pre, from) + 1)
    &&& post.own == pre.own
    &&& post.actor == pre.actor
    &&& post.journal == pre.journal
}

/// `host` accepts `env`, presenting `epoch`: the message is appended to the
/// journal.
///
/// Four guards, and each is a different guarantee:
///
/// * `can_mutate` — **only the owner, at the current epoch.** The ownership
///   protocol's single definition of mutable authority; this is where fencing
///   and exclusivity enter.
/// * `sent.contains(env)` — **nothing is invented.**
/// * `env.seq == accepted_from(..)` — **once, and in order.**
/// * `live` — a crashed node executes nothing.
pub open spec fn as_accept(
    pre: ActorSystem,
    post: ActorSystem,
    host: HostId,
    epoch: Epoch,
    env: Envelope,
) -> bool {
    &&& pre.own.live.contains(host)
    &&& can_mutate(pre.own, pre.actor, host, epoch)
    &&& pre.sent.contains(env)
    &&& env.seq == accepted_from(pre.journal, env.sender)
    &&& post.journal == pre.journal.push(Entry { env: env, host: host, epoch: epoch })
    &&& post.own == pre.own
    &&& post.actor == pre.actor
    &&& post.sent == pre.sent
    &&& post.next_seq == pre.next_seq
}

/// Any ownership transition, carried unchanged. It touches nothing of the
/// actor's: the journal, and with it the state, stays exactly where it was.
pub open spec fn as_own(pre: ActorSystem, post: ActorSystem, s: Step) -> bool {
    &&& step(pre.own, post.own, s)
    &&& post.actor == pre.actor
    &&& post.sent == pre.sent
    &&& post.next_seq == pre.next_seq
    &&& post.journal == pre.journal
}

/// The labelled transitions of the actor system.
pub enum ActorStep {
    Send { from: HostId, body: nat },
    Accept { host: HostId, epoch: Epoch, env: Envelope },
    Own { own_step: Step },
}

pub open spec fn actor_step(pre: ActorSystem, post: ActorSystem, s: ActorStep) -> bool {
    match s {
        ActorStep::Send { from, body } => as_send(pre, post, from, body),
        ActorStep::Accept { host, epoch, env } => as_accept(pre, post, host, epoch, env),
        ActorStep::Own { own_step } => as_own(pre, post, own_step),
    }
}

pub open spec fn actor_next(pre: ActorSystem, post: ActorSystem) -> bool {
    exists|s: ActorStep| actor_step(pre, post, s)
}

/// Initial states: the ownership layer is initial, the actor exists, nothing has
/// been sent, and the journal is empty.
pub open spec fn actor_init(c: ActorSystem) -> bool {
    &&& init(c.own)
    &&& c.own.actors.contains_key(c.actor)
    &&& c.sent == Set::<Envelope>::empty()
    &&& c.next_seq == Map::<HostId, nat>::empty()
    &&& c.journal == Seq::<Entry>::empty()
}

/// `tr` is a finite execution of the actor system.
///
/// The multi-trigger on both adjacent states is the one every execution
/// predicate here uses, for the reason documented on
/// [`crate::ownership::model::valid_execution`].
pub open spec fn actor_execution(tr: Seq<ActorSystem>) -> bool {
    &&& tr.len() > 0
    &&& actor_init(tr[0])
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> actor_next(tr[i], tr[i + 1]))
}

/// A **labelled** finite run: `labels[i]` is the step from `tr[i]` to
/// `tr[i + 1]`.
pub open spec fn actor_run(tr: Seq<ActorSystem>, labels: Seq<ActorStep>) -> bool {
    &&& tr.len() > 0
    &&& labels.len() == tr.len() - 1
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() ==> actor_step(tr[i], tr[i + 1], labels[i]))
}

/// `c` is reachable.
pub open spec fn actor_reachable(c: ActorSystem) -> bool {
    exists|tr: Seq<ActorSystem>| actor_execution(tr) && tr[tr.len() - 1] == c
}

} // verus!
