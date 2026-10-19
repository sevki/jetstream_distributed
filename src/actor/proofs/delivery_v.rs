//! **Each message once, in the order sent.** What the network can do to a
//! message, and what the actor does about it.
//!
//! The network may deliver a message any number of times, in any order, at any
//! later point (`ActorSystem::sent` never shrinks). None of that is a separate
//! failure mode to be handled: it is what [`as_accept`] is already quantified
//! over, and these theorems say that whatever it is offered, the journal comes
//! out the same shape.
//!
//! All of it is one guard — `env.seq == accepted_from(journal, env.sender)` — and
//! one invariant, [`inv_fifo`]. Each theorem here is a different reading of it.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::model::*;
use crate::actor::proofs::invariant::*;
use crate::actor::proofs::journal::*;
use crate::ownership::model::*;

verus! {

/// **Nothing is invented.** Every message in the journal was sent.
pub proof fn theorem_only_sent_messages_are_accepted(c: ActorSystem, i: int)
    requires
        actor_reachable(c),
        0 <= i < c.journal.len(),
    ensures
        c.sent.contains(c.journal[i].env),
{
    theorem_reachable_inv(c);
}

/// **The `n`th message accepted from a sender carries sequence number `n`.** The
/// journal holds each sender's messages numbered 0, 1, 2, ... in that order:
/// none out of place, none repeated, none skipped.
pub proof fn theorem_the_nth_message_from_a_sender_is_numbered_n(c: ActorSystem, i: int)
    requires
        actor_reachable(c),
        0 <= i < c.journal.len(),
    ensures
        c.journal[i].env.seq == accepted_from(c.journal.take(i), c.journal[i].env.sender),
{
    theorem_reachable_inv(c);
}

/// **A later message from the same sender has a larger sequence number.**
/// Messages from one sender are accepted in the order they were sent.
pub proof fn theorem_one_senders_messages_are_accepted_in_order(c: ActorSystem, i: int, k: int)
    requires
        actor_reachable(c),
        0 <= i < k < c.journal.len(),
        c.journal[i].env.sender == c.journal[k].env.sender,
    ensures
        c.journal[i].env.seq < c.journal[k].env.seq,
{
    theorem_reachable_inv(c);
    let s = c.journal[i].env.sender;
    // Entry `i` is `s`'s, so the prefix through `i` counts one more than the
    // prefix before it, and the prefix before `k` is at least the prefix
    // through `i`.
    lemma_accepted_from_next(c.journal, i, s);
    lemma_accepted_from_monotone(c.journal, i + 1, k, s);
}

/// **A message is accepted at most once.** However many times the network
/// delivers it, it appears in the journal once.
pub proof fn theorem_a_message_is_accepted_at_most_once(c: ActorSystem, i: int, k: int)
    requires
        actor_reachable(c),
        0 <= i < k < c.journal.len(),
    ensures
        c.journal[i].env != c.journal[k].env,
{
    if c.journal[i].env == c.journal[k].env {
        theorem_one_senders_messages_are_accepted_in_order(c, i, k);
    }
}

/// **A message already accepted is refused if it arrives again.** The
/// redelivery case directly: given a state in which `env` is in the journal, no
/// host, at any epoch, can accept it again.
///
/// This does not need reachability, only the invariant — which is what makes it
/// usable from a service that holds a journal and wants to know whether an
/// arrival is a duplicate.
pub proof fn theorem_a_redelivered_message_is_refused(
    pre: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
    i: int,
)
    requires
        actor_inv(pre),
        0 <= i < pre.journal.len(),
        pre.journal[i].env == env,
    ensures
        !as_accept(pre, post, host, epoch, env),
{
    let s = env.sender;
    lemma_accepted_from_next(pre.journal, i, s);
    lemma_accepted_from_monotone(pre.journal, i + 1, pre.journal.len() as int, s);
    lemma_take_all(pre.journal);
}

/// **A message ahead of its turn is refused.** If `env` carries a sequence number
/// beyond the count already accepted from its sender, no host can accept it yet:
/// the ones before it have to arrive first.
pub proof fn theorem_a_message_ahead_of_its_turn_is_refused(
    pre: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
)
    requires
        env.seq > accepted_from(pre.journal, env.sender),
    ensures
        !as_accept(pre, post, host, epoch, env),
{
}

} // verus!
