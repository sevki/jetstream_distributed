//! **One host at a time.** Who may append to the journal, and who may not.
//!
//! The ownership layer already proves that at most one node may mutate an actor
//! (`ownership::proofs::exclusivity`) and that a stale epoch cannot
//! (`ownership::proofs::fencing`). The actor's journal write is *defined* as that
//! mutation, so these are the same facts about a different verb — the first two
//! theorems here are the ownership layer's, read at [`as_accept`]. The last two
//! are not: they are about the journal, over a whole run, and say that the
//! fence kept every entry in it ordered and single-authored.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::model::*;
use crate::actor::proofs::invariant::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::proofs::fencing::*;
use crate::ownership::spec::*;

verus! {

/// **At most one host can accept at any instant** — and at only one epoch.
///
/// No reachability needed: in *no* state at all do two different hosts both
/// satisfy [`as_accept`]'s authority guard. `may_mutate` is a match on a single
/// ownership record, and only `Owned` grants anything.
pub proof fn theorem_at_most_one_host_can_accept(
    c: ActorSystem,
    h1: NodeId,
    e1: Epoch,
    h2: NodeId,
    e2: Epoch,
)
    requires
        can_mutate(c.own, c.actor, h1, e1),
        can_mutate(c.own, c.actor, h2, e2),
    ensures
        h1 == h2,
        e1 == e2,
{
}

/// **A host that has been superseded cannot accept.** Present any epoch behind
/// the actor's current one and no post-state, whatever the message, satisfies
/// [`as_accept`].
///
/// This is what makes a returning stale owner harmless: it is partitioned away,
/// the actor moves on, it comes back still believing it hosts the actor, and its
/// first append is refused.
pub proof fn theorem_a_superseded_host_cannot_accept(
    pre: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
)
    requires
        pre.own.actors.contains_key(pre.actor),
        epoch < current_epoch(pre.own.actors[pre.actor]),
    ensures
        !as_accept(pre, post, host, epoch, env),
{
}

/// **Nobody accepts while the actor is between owners.** During `Transferring`
/// and `Unowned` there is no host, so there is no one to append — in particular
/// not the outgoing owner, whose epoch was burned the moment the transfer began.
pub proof fn theorem_nobody_accepts_between_owners(
    pre: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
)
    requires
        pre.own.actors.contains_key(pre.actor),
        !is_owned(pre.own.actors[pre.actor]),
    ensures
        !as_accept(pre, post, host, epoch, env),
{
}

/// **Only the owner accepts, and only at the current epoch.**
pub proof fn theorem_only_the_owner_accepts(
    pre: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
)
    requires
        as_accept(pre, post, host, epoch, env),
    ensures
        pre.own.actors.contains_key(pre.actor),
        is_owned_by(pre.own.actors[pre.actor], host),
        epoch == current_epoch(pre.own.actors[pre.actor]),
{
}

/// **One host per epoch.** Across the whole life of the actor, two entries
/// written at the same epoch were written by the same host.
///
/// This is the history-level form of exclusivity, and it is not a restatement of
/// [`theorem_at_most_one_host_can_accept`]: that says two hosts cannot append *at
/// once*; this says two hosts cannot append *under one generation*, however far
/// apart in time.
pub proof fn theorem_one_host_per_epoch(c: ActorSystem, i: int, k: int)
    requires
        actor_reachable(c),
        0 <= i < c.journal.len(),
        0 <= k < c.journal.len(),
        c.journal[i].epoch == c.journal[k].epoch,
    ensures
        c.journal[i].host == c.journal[k].host,
{
    theorem_reachable_inv(c);
}

/// **Epochs never fall along the journal.** An entry is never written under an
/// older generation than the entry before it: nobody writes behind a newer host.
pub proof fn theorem_epochs_never_fall_along_the_journal(c: ActorSystem, i: int, k: int)
    requires
        actor_reachable(c),
        0 <= i < k < c.journal.len(),
    ensures
        c.journal[i].epoch <= c.journal[k].epoch,
{
    theorem_reachable_inv(c);
}

/// One step never lowers the actor's epoch, and never changes which actor this is.
proof fn lemma_step_epoch(pre: ActorSystem, post: ActorSystem, s: ActorStep)
    requires
        pre.own.actors.contains_key(pre.actor),
        actor_step(pre, post, s),
    ensures
        post.actor == pre.actor,
        post.own.actors.contains_key(pre.actor),
        current_epoch(post.own.actors[pre.actor]) >= current_epoch(pre.own.actors[pre.actor]),
{
    match s {
        ActorStep::Own { own_step } => {
            theorem_epoch_monotone_step(pre.own, post.own, own_step, pre.actor);
        },
        _ => {},
    }
}

/// The actor's epoch never falls along an execution.
pub proof fn lemma_run_epoch(tr: Seq<ActorSystem>, i: int, j: int)
    requires
        actor_execution(tr),
        0 <= i <= j < tr.len(),
    ensures
        tr[j].actor == tr[i].actor,
        tr[j].own.actors.contains_key(tr[i].actor),
        current_epoch(tr[j].own.actors[tr[i].actor]) >= current_epoch(
            tr[i].own.actors[tr[i].actor],
        ),
    decreases j - i,
{
    lemma_execution_inv(tr, i);
    if i < j {
        lemma_run_epoch(tr, i, j - 1);
        assert(actor_next(tr[j - 1], tr[j - 1 + 1]));
        let pre = tr[j - 1];
        let post = tr[j];
        let s = choose|s: ActorStep| actor_step(pre, post, s);
        lemma_step_epoch(pre, post, s);
    }
}

/// **Nothing is written under an epoch the actor has already left.** From any
/// point of an execution on, every entry appended afterwards carries an epoch at
/// least the actor's epoch at that point.
///
/// This is fencing as a fact about the journal rather than about a single
/// request. [`theorem_a_superseded_host_cannot_accept`] says a superseded host's
/// *attempt* is refused; this says none of its writes can be found in the log
/// afterwards, however the network reordered what it sent.
pub proof fn theorem_nothing_is_written_under_a_superseded_epoch(
    tr: Seq<ActorSystem>,
    i: int,
    j: int,
    k: int,
)
    requires
        actor_execution(tr),
        0 <= i <= j < tr.len(),
        tr[i].journal.len() <= k < tr[j].journal.len(),
    ensures
        tr[j].journal[k].epoch >= current_epoch(tr[i].own.actors[tr[i].actor]),
    decreases j - i,
{
    if i < j {
        assert(actor_next(tr[j - 1], tr[j - 1 + 1]));
        let pre = tr[j - 1];
        let post = tr[j];
        let s = choose|s: ActorStep| actor_step(pre, post, s);
        lemma_run_epoch(tr, i, j - 1);
        match s {
            ActorStep::Accept { host, epoch, env } => {
                if k < pre.journal.len() {
                    theorem_nothing_is_written_under_a_superseded_epoch(tr, i, j - 1, k);
                }
            },
            _ => {
                theorem_nothing_is_written_under_a_superseded_epoch(tr, i, j - 1, k);
            },
        }
    }
}

} // verus!
