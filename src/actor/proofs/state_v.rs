//! **State that survives.** The journal only grows, the state is a fold over it,
//! and moving the actor to another host changes neither.
//!
//! The actor's state is not held by a host — it is [`state_of`] the journal, and
//! any host that can read the journal can recompute it. So "a handover preserves
//! state" is not a property of some state-transfer mechanism; it is the fact that
//! the only things that can happen to the journal are an append by the owner at
//! the current epoch, and nothing. These theorems say that, and say what an
//! append does to the state: exactly one application of the actor's behaviour.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::model::*;
use crate::actor::proofs::invariant::*;
use crate::actor::proofs::journal::*;
use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::proofs::fencing::*;
use crate::ownership::spec::*;

verus! {

/// `b` is `a` with more entries after it.
pub open spec fn extends(a: Seq<Entry>, b: Seq<Entry>) -> bool {
    &&& a.len() <= b.len()
    &&& b.take(a.len() as int) =~= a
}

/// The state reached by applying the behaviour to each entry of `entries`, in
/// order, starting from `state`.
pub open spec fn replay_from(state: nat, entries: Seq<Entry>) -> nat
    decreases entries.len(),
{
    if entries.len() == 0 {
        state
    } else {
        apply(replay_from(state, entries.drop_last()), entries.last().env.body)
    }
}

pub proof fn lemma_extends_refl(a: Seq<Entry>)
    ensures
        extends(a, a),
{
}

pub proof fn lemma_extends_trans(a: Seq<Entry>, b: Seq<Entry>, c: Seq<Entry>)
    requires
        extends(a, b),
        extends(b, c),
    ensures
        extends(a, c),
{
    assert(c.take(b.len() as int).take(a.len() as int) =~= c.take(a.len() as int));
}

pub proof fn lemma_extends_push(a: Seq<Entry>, e: Entry)
    ensures
        extends(a, a.push(e)),
{
    assert(a.push(e).take(a.len() as int) =~= a);
}

/// **Every step leaves the journal as it was or extends it.**
pub proof fn lemma_step_extends(pre: ActorSystem, post: ActorSystem, s: ActorStep)
    requires
        actor_step(pre, post, s),
    ensures
        extends(pre.journal, post.journal),
{
    match s {
        ActorStep::Accept { host, epoch, env } => {
            lemma_extends_push(pre.journal, Entry { env: env, host: host, epoch: epoch });
        },
        _ => {
            lemma_extends_refl(pre.journal);
        },
    }
}

/// **The journal is append-only.** Along any execution, an earlier journal is a
/// prefix of every later one: what the actor accepted, it keeps, in the order it
/// accepted it. No message acknowledged is ever lost, reordered or rewritten —
/// including by a handover.
pub proof fn theorem_the_journal_is_append_only(tr: Seq<ActorSystem>, i: int, j: int)
    requires
        actor_execution(tr),
        0 <= i <= j < tr.len(),
    ensures
        extends(tr[i].journal, tr[j].journal),
    decreases j - i,
{
    if i == j {
        lemma_extends_refl(tr[i].journal);
    } else {
        theorem_the_journal_is_append_only(tr, i, j - 1);
        assert(actor_next(tr[j - 1], tr[j - 1 + 1]));
        let pre = tr[j - 1];
        let post = tr[j];
        let s = choose|s: ActorStep| actor_step(pre, post, s);
        lemma_step_extends(pre, post, s);
        lemma_extends_trans(tr[i].journal, tr[j - 1].journal, tr[j].journal);
    }
}

/// **An append is one application of the behaviour.** The state after
/// accepting a message is the behaviour applied to the state before.
pub proof fn theorem_accepting_applies_the_behaviour(
    pre: ActorSystem,
    post: ActorSystem,
    host: NodeId,
    epoch: Epoch,
    env: Envelope,
)
    requires
        as_accept(pre, post, host, epoch, env),
    ensures
        state_of(post.journal) == apply(state_of(pre.journal), env.body),
{
    lemma_state_of_push(pre.journal, Entry { env: env, host: host, epoch: epoch });
}

/// **A handover changes neither the journal nor the state.** Whatever the
/// ownership layer does — a transfer, a revocation, a crash, a recovery — the
/// actor's accepted messages, and therefore its state, are exactly what they were.
///
/// The new owner does not receive the state from the old one; it reads the same
/// journal and recomputes the same state.
pub proof fn theorem_a_handover_preserves_the_state(pre: ActorSystem, post: ActorSystem, s: Step)
    requires
        as_own(pre, post, s),
    ensures
        post.journal == pre.journal,
        state_of(post.journal) == state_of(pre.journal),
{
}

/// A longer journal's state is the shorter one's, with the extra entries replayed
/// on top.
pub proof fn lemma_state_of_extends(a: Seq<Entry>, b: Seq<Entry>)
    requires
        extends(a, b),
    ensures
        state_of(b) == replay_from(state_of(a), b.skip(a.len() as int)),
    decreases b.len(),
{
    if a.len() == b.len() {
        assert(b =~= a);
        assert(b.skip(a.len() as int) =~= Seq::<Entry>::empty());
    } else {
        let m = a.len() as int;
        let b2 = b.drop_last();
        assert(extends(a, b2)) by {
            assert(b2.take(m) =~= b.take(m));
        }
        lemma_state_of_extends(a, b2);
        let tail = b.skip(m);
        assert(tail.drop_last() =~= b2.skip(m));
        assert(tail.last() == b.last());
    }
}

/// **A run continues the state; it does not restart it.** Between any two points
/// of an execution, the state at the later point is the state at the earlier one
/// with the entries accepted in between replayed on top.
///
/// Across a handover this is the new owner picking up exactly where the old one
/// left off.
pub proof fn theorem_the_state_continues_across_a_run(tr: Seq<ActorSystem>, i: int, j: int)
    requires
        actor_execution(tr),
        0 <= i <= j < tr.len(),
    ensures
        state_of(tr[j].journal) == replay_from(
            state_of(tr[i].journal),
            tr[j].journal.skip(tr[i].journal.len() as int),
        ),
{
    theorem_the_journal_is_append_only(tr, i, j);
    lemma_state_of_extends(tr[i].journal, tr[j].journal);
}

} // verus!
