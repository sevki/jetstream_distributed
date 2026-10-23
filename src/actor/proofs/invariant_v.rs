//! The invariant every reachable state satisfies, and the proof that every step
//! preserves it.
//!
//! Five facts about the journal, each of which is the inductive form of one of
//! the actor's guarantees:
//!
//! | invariant | guarantee it carries |
//! | --- | --- |
//! | [`inv_sent`] | nothing is invented: every accepted message was sent |
//! | [`inv_fifo`] | each message once, in order, none skipped |
//! | [`inv_epochs_bounded`] | no entry was written under an epoch from the future |
//! | [`inv_epochs_ordered`] | epochs never fall along the journal: nobody writes behind a newer host |
//! | [`inv_single_writer`] | one host per epoch |
//!
//! plus [`inv_current_epoch_host`], which is not a guarantee in itself but the
//! fact that makes the last one provable by induction: entries written at the
//! actor's *current* epoch were written by its *current* owner.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::id::Id;

use crate::actor::model::*;
use crate::actor::proofs::journal::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::proofs::fencing::*;
use crate::ownership::proofs::properties::*;
use crate::ownership::spec::*;

verus! {

/// Every accepted message was sent.
pub open spec fn inv_sent(c: ActorSystem) -> bool {
    forall|i: int|
        0 <= i < c.journal.len() ==> #[trigger] c.sent.contains(c.journal[i].env)
}

/// Each entry's sequence number is the number of earlier entries from its
/// sender: from any one sender, the journal holds messages numbered 0, 1, 2, ...
/// in that order.
pub open spec fn inv_fifo(c: ActorSystem) -> bool {
    forall|i: int|
        0 <= i < c.journal.len() ==> #[trigger] c.journal[i].env.seq == accepted_from(
            c.journal.take(i),
            c.journal[i].env.sender,
        )
}

/// The actor exists, and no entry was written at an epoch ahead of the actor's
/// current one.
pub open spec fn inv_epochs_bounded(c: ActorSystem) -> bool {
    &&& c.own.actors.contains_key(c.actor)
    &&& forall|i: int|
        0 <= i < c.journal.len() ==> #[trigger] c.journal[i].epoch <= current_epoch(
            c.own.actors[c.actor],
        )
}

/// Epochs never fall along the journal.
pub open spec fn inv_epochs_ordered(c: ActorSystem) -> bool {
    forall|i: int, k: int|
        #![trigger c.journal[i], c.journal[k]]
        0 <= i < k < c.journal.len() ==> c.journal[i].epoch <= c.journal[k].epoch
}

/// An entry written at the actor's current epoch was written by its current
/// owner, who still owns it.
pub open spec fn inv_current_epoch_host(c: ActorSystem) -> bool {
    forall|i: int|
        0 <= i < c.journal.len() && c.own.actors.contains_key(c.actor) && #[trigger] c.journal[i].epoch
            == current_epoch(c.own.actors[c.actor]) ==> c.own.actors[c.actor]
            == (OwnershipState::Owned { owner: c.journal[i].host, epoch: c.journal[i].epoch })
}

/// Two entries written at the same epoch were written by the same host.
pub open spec fn inv_single_writer(c: ActorSystem) -> bool {
    forall|i: int, k: int|
        #![trigger c.journal[i], c.journal[k]]
        0 <= i < c.journal.len() && 0 <= k < c.journal.len() && c.journal[i].epoch
            == c.journal[k].epoch ==> c.journal[i].host == c.journal[k].host
}

/// The actor system's invariant.
pub open spec fn actor_inv(c: ActorSystem) -> bool {
    &&& inv_sent(c)
    &&& inv_fifo(c)
    &&& inv_epochs_bounded(c)
    &&& inv_epochs_ordered(c)
    &&& inv_current_epoch_host(c)
    &&& inv_single_writer(c)
}

/// An initial state satisfies it: the journal is empty, so every clause is
/// vacuous.
pub proof fn lemma_init_inv(c: ActorSystem)
    requires
        actor_init(c),
    ensures
        actor_inv(c),
{
}

/// **Sending preserves it.** A send touches only `sent` and `next_seq`, and `sent`
/// only grows.
pub proof fn lemma_send_preserves_inv(pre: ActorSystem, post: ActorSystem, from: Id, body: Vec<u8>)
    requires
        actor_inv(pre),
        as_send(pre, post, from, body),
    ensures
        actor_inv(post),
{
    assert forall|i: int| 0 <= i < post.journal.len() implies #[trigger] post.sent.contains(
        post.journal[i].env,
    ) by {
        assert(pre.sent.contains(pre.journal[i].env));
    }
}

/// **An ownership step preserves it.** The journal is untouched, so the only
/// clauses that can change are the ones that read the actor's current epoch.
pub proof fn lemma_own_preserves_inv(pre: ActorSystem, post: ActorSystem, s: Step)
    requires
        actor_inv(pre),
        as_own(pre, post, s),
    ensures
        actor_inv(post),
{
    let a = pre.actor;
    theorem_epoch_monotone_step(pre.own, post.own, s, a);

    assert forall|i: int| 0 <= i < post.journal.len() implies #[trigger] post.journal[i].epoch
        <= current_epoch(post.own.actors[post.actor]) by {
        assert(post.journal[i].epoch <= current_epoch(pre.own.actors[a]));
    }

    assert forall|i: int|
        0 <= i < post.journal.len() && post.own.actors.contains_key(post.actor)
            && #[trigger] post.journal[i].epoch == current_epoch(post.own.actors[post.actor])
            implies post.own.actors[post.actor] == (OwnershipState::Owned {
        owner: post.journal[i].host,
        epoch: post.journal[i].epoch,
    }) by {
        let e = post.journal[i].epoch;
        // Written at `e`, so `e` was never ahead of the epoch then; the epoch
        // has not fallen since; and it is `e` now. So it was `e` before too,
        // and the owner at `e` has not changed.
        assert(e <= current_epoch(pre.own.actors[a]));
        assert(current_epoch(pre.own.actors[a]) <= current_epoch(post.own.actors[a]));
        assert(current_epoch(pre.own.actors[a]) == e);
        assert(pre.own.actors[a] == (OwnershipState::Owned {
            owner: pre.journal[i].host,
            epoch: e,
        }));
        lemma_owned_epoch_frozen(pre.own, post.own, s, a, pre.journal[i].host, e);
    }
}

/// **An accepted append preserves it.** The only step that writes the journal,
/// and so the only one with real work to do.
///
/// `can_mutate` is what carries it: it says the actor is `Owned { host, epoch }`
/// *right now*, so the new entry is written at exactly the current epoch, by
/// exactly the current owner. Every other clause follows from that and from the
/// invariant on the entries already there.
pub proof fn lemma_accept_preserves_inv(
    pre: ActorSystem,
    post: ActorSystem,
    host: Id,
    epoch: Epoch,
    env: Envelope,
)
    requires
        actor_inv(pre),
        as_accept(pre, post, host, epoch, env),
    ensures
        actor_inv(post),
{
    let a = pre.actor;
    let n = pre.journal.len() as int;
    let e = Entry { env: env, host: host, epoch: epoch };
    assert(post.journal.len() == n + 1);
    assert(post.journal[n] == e);
    assert forall|i: int| 0 <= i < n implies post.journal[i] == pre.journal[i] by {}

    // The fence: the actor is owned by `host`, at `epoch`, now.
    assert(pre.own.actors[a] == (OwnershipState::Owned { owner: host, epoch: epoch }));
    assert(current_epoch(pre.own.actors[a]) == epoch);

    assert forall|i: int| 0 <= i < post.journal.len() implies #[trigger] post.sent.contains(
        post.journal[i].env,
    ) by {
        if i < n {
            assert(pre.sent.contains(pre.journal[i].env));
        }
    }

    assert forall|i: int| 0 <= i < post.journal.len() implies #[trigger] post.journal[i].env.seq
        == accepted_from(post.journal.take(i), post.journal[i].env.sender) by {
        if i < n {
            assert(post.journal.take(i) =~= pre.journal.take(i));
        } else {
            assert(post.journal.take(n) =~= pre.journal);
        }
    }

    assert forall|i: int| 0 <= i < post.journal.len() implies #[trigger] post.journal[i].epoch
        <= current_epoch(post.own.actors[post.actor]) by {
        if i < n {
            assert(pre.journal[i].epoch <= current_epoch(pre.own.actors[a]));
        }
    }

    assert forall|i: int, k: int| 0 <= i < k < post.journal.len() implies #[trigger]
        post.journal[i].epoch <= #[trigger] post.journal[k].epoch by {
        if k < n {
            assert(pre.journal[i].epoch <= pre.journal[k].epoch);
        } else {
            assert(pre.journal[i].epoch <= current_epoch(pre.own.actors[a]));
        }
    }

    assert forall|i: int|
        0 <= i < post.journal.len() && post.own.actors.contains_key(post.actor)
            && #[trigger] post.journal[i].epoch == current_epoch(post.own.actors[post.actor])
            implies post.own.actors[post.actor] == (OwnershipState::Owned {
        owner: post.journal[i].host,
        epoch: post.journal[i].epoch,
    }) by {
        if i < n {
            assert(pre.journal[i].epoch == current_epoch(pre.own.actors[a]));
        }
    }

    assert forall|i: int, k: int|
        0 <= i < post.journal.len() && 0 <= k < post.journal.len() && post.journal[i].epoch
            == post.journal[k].epoch implies #[trigger] post.journal[i].host
            == #[trigger] post.journal[k].host by {
        if i < n && k < n {
            assert(pre.journal[i].host == pre.journal[k].host);
        } else if i < n {
            // `i` was written at the epoch the actor is at now, so by its owner
            // — who is `host`.
            assert(pre.journal[i].epoch == current_epoch(pre.own.actors[a]));
        } else if k < n {
            assert(pre.journal[k].epoch == current_epoch(pre.own.actors[a]));
        }
    }
}

/// **Every step preserves it.**
pub proof fn lemma_step_preserves_inv(pre: ActorSystem, post: ActorSystem, s: ActorStep)
    requires
        actor_inv(pre),
        actor_step(pre, post, s),
    ensures
        actor_inv(post),
{
    match s {
        ActorStep::Send { from, body } => lemma_send_preserves_inv(pre, post, from, body),
        ActorStep::Accept { host, epoch, env } => lemma_accept_preserves_inv(
            pre,
            post,
            host,
            epoch,
            env,
        ),
        ActorStep::Own { own_step } => lemma_own_preserves_inv(pre, post, own_step),
    }
}

/// The unlabelled transition relation preserves it.
pub proof fn lemma_next_preserves_inv(pre: ActorSystem, post: ActorSystem)
    requires
        actor_inv(pre),
        actor_next(pre, post),
    ensures
        actor_inv(post),
{
    let s = choose|s: ActorStep| actor_step(pre, post, s);
    lemma_step_preserves_inv(pre, post, s);
}

/// The invariant holds at every point of an execution.
pub proof fn lemma_execution_inv(tr: Seq<ActorSystem>, i: int)
    requires
        actor_execution(tr),
        0 <= i < tr.len(),
    ensures
        actor_inv(tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_init_inv(tr[0]);
    } else {
        lemma_execution_inv(tr, i - 1);
        assert(actor_next(tr[i - 1], tr[i - 1 + 1]));
        lemma_next_preserves_inv(tr[i - 1], tr[i]);
    }
}

/// **The invariant holds in every reachable state.**
pub proof fn theorem_reachable_inv(c: ActorSystem)
    requires
        actor_reachable(c),
    ensures
        actor_inv(c),
{
    let tr = choose|tr: Seq<ActorSystem>| actor_execution(tr) && tr[tr.len() - 1] == c;
    lemma_execution_inv(tr, tr.len() - 1);
}

} // verus!
