//! The OwnershipSystem model: state, transitions, executions.
//!
//! This module defines *only* the state space and the transition relation.
//! It deliberately has no dependency on the specification functions in
//! [`crate::ownership::spec`] / [`crate::ownership::fencing`], so that the model cannot be
//! "tuned" to make a specification come out true.
//!
//! ## What is modelled
//!
//! * A fixed set of actors, each with an [`OwnershipState`].
//! * A fixed set of nodes, of which a subset is `live` - participating in the
//!   protocol rather than merely powered on; see `OwnershipSystem::live`.
//! * `issued`: every ownership [`Token`] that was ever physically handed out.
//!   This set never shrinks: a crash does not erase the tokens a node was
//!   holding, so stale physical tokens survive crashes and partitions.
//! * `network`: every [`Message`] that was ever sent. This set never shrinks
//!   either, and delivery does not consume a message. That single modelling
//!   choice gives us, for free and by construction:
//!   - **duplication** - a message can be delivered any number of times;
//!   - **reordering**  - deliveries may happen in any order;
//!   - **delay**       - an arbitrary number of steps may pass before delivery;
//!   - **staleness**   - a message from epoch `n` is still deliverable long
//!     after the protocol has advanced to epoch `n + k`;
//!   - **loss**        - a message may simply never be delivered.
//!
//! See `README.md` ("Failure model") for the assumptions this encodes.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;

verus! {

/// Identity of an actor. Ownership is tracked per actor.
pub type ActorId = nat;

/// A fencing epoch. Monotonically increasing per actor.
pub type Epoch = nat;

/// The ownership state of a single actor.
///
/// The protocol never assigns ownership atomically: moving an actor from one
/// node to another always passes through `Transferring` and `Unowned`.
pub enum OwnershipState {
    /// `owner` holds exclusive mutable authority at `epoch`.
    Owned { owner: HostId, epoch: Epoch },
    /// Authority has been withdrawn from `from` and a new epoch has been
    /// allocated for `to`, but nobody holds authority right now.
    Transferring { from: HostId, to: HostId, old_epoch: Epoch, new_epoch: Epoch },
    /// Nobody holds authority. `intended_owner` is the node that a grant for
    /// `epoch` has been (or will be) addressed to.
    Unowned { epoch: Epoch, intended_owner: HostId },
}

/// A physical ownership capability.
///
/// A token is a *physical* artifact: it can be copied, it survives crashes and
/// it can be presented by a node that has been partitioned away for a long
/// time. Whether a token confers *authority* is a question about the current
/// OwnershipSystem state, see `crate::ownership::token_authorized`.
pub struct Token {
    pub actor: ActorId,
    pub epoch: Epoch,
    pub holder: HostId,
}

/// Protocol messages. Messages are hints: every state change is additionally
/// guarded by the actor's own ownership state, so a replayed or reordered
/// message can never by itself move the protocol forward.
pub enum Message {
    /// Coordinator -> current owner: stop mutating, `new_epoch` was allocated.
    Revoke { actor: ActorId, target: HostId, old_epoch: Epoch, new_epoch: Epoch },
    /// Owner -> coordinator: acknowledgement of a `Revoke`.
    Released { actor: ActorId, from: HostId, new_epoch: Epoch },
    /// Coordinator -> new owner: you may take ownership at `epoch`.
    Grant { actor: ActorId, to: HostId, epoch: Epoch },
}

/// The whole OwnershipSystem.
pub struct OwnershipSystem {
    /// Ownership state of every actor. The domain never changes.
    ///
    /// **This is the ownership registry, not per-node state.** Every
    /// epoch-advancing transition reads `pre.actors[a]` and writes
    /// `post.actors.insert(a, ..)` in one step, so each actor's record is a
    /// single value updated atomically. That is an assumption about the
    /// deployment, and it is the strongest one this model makes: it rules out,
    /// *by construction*, two coordinators deciding concurrently — both reading
    /// `Owned { owner, epoch }` and both allocating `epoch + 1` for different
    /// successors. The model cannot express that, because the second read
    /// necessarily sees the first write.
    ///
    /// A real deployment has to buy that atomicity somewhere: consensus, or an
    /// object store with compare-and-swap, which is what makes "read
    /// `Owned { A, 41 }`, write `Unowned { 42, B }`" a single step. See the
    /// failure-model table in `README.md`.
    pub actors: Map<ActorId, OwnershipState>,
    /// All nodes that exist.
    pub nodes: Set<HostId>,
    /// The nodes **participating in the protocol**.
    ///
    /// Not quite the same as "powered on", and the difference matters in one
    /// place. A node leaves this set when it crashes and rejoins it at
    /// `Recover`, and every transition that makes a node *act* requires it to be
    /// in here - `tr_handle_revoke`, `crate::composed::model::cs_ray`,
    /// `crate::composed::model::cs_pass_token` and the rest.
    ///
    /// The exception is [`crate::composed::model::cs_reconcile`], which fires while the
    /// node is outside this set, and it is not a hole in that discipline: it
    /// models a step of the node's **recovery routine**, re-reading
    /// authoritative routing state before rejoining. A node running its recovery
    /// routine is executing but not yet participating, which is exactly the gap
    /// between the two readings. The ordering `Reconcile` then `Recover` is what
    /// encodes it, and `crate::composed::recovers_a_seized_node` is what enforces
    /// it - so a node cannot come back and start taking protocol steps on a
    /// belief it never corrected.
    ///
    /// Nothing else is permitted outside this set, so "not participating" never
    /// licenses a crashed node to act.
    pub live: Set<HostId>,
    /// Every token ever issued. Monotonically grows (see module docs).
    pub issued: Set<Token>,
    /// Every message ever sent. Monotonically grows (see module docs).
    pub network: Set<Message>,
}

// ---------------------------------------------------------------------------
// Transitions
// ---------------------------------------------------------------------------

/// `node` takes ownership of `actor` after receiving a matching grant.
///
/// The guard is the *state*, not the message: the actor must currently be
/// `Unowned` at exactly the epoch named by the grant, and `node` must be the
/// intended owner. A duplicated or stale `Grant` therefore cannot fire this
/// transition a second time, because the state is no longer `Unowned`.
pub open spec fn tr_acquire(pre: OwnershipSystem, post: OwnershipSystem, a: ActorId, n: HostId) -> bool {
    &&& pre.actors.contains_key(a)
    &&& pre.live.contains(n)
    &&& match pre.actors[a] {
        OwnershipState::Unowned { epoch, intended_owner } =>
            intended_owner == n
            && pre.network.contains(Message::Grant { actor: a, to: n, epoch: epoch })
            && post.actors == pre.actors.insert(a, OwnershipState::Owned { owner: n, epoch: epoch })
            && post.issued == pre.issued.insert(Token { actor: a, epoch: epoch, holder: n })
            && post.nodes == pre.nodes
            && post.live == pre.live
            && post.network == pre.network,
        _ => false,
    }
}

/// The current owner agrees to hand `actor` over to `to`.
///
/// This allocates the next epoch immediately, which fences the outgoing owner
/// straight away: from this moment on nobody has mutable authority.
///
/// **The owner must be participating.** "Agrees to hand over" is an action by
/// `from`, so this is guarded like every other transition a node takes: see
/// `OwnershipSystem::live`. Without it, `Acquire(A) -> Crash(A) -> BeginTransfer(A, B)`
/// was accepted, and a crashed node could volunteer - which would make the
/// forcible path redundant in the model, since `RevokeOwner` and
/// `crate::composed::model::cs_seize_token` exist precisely for the case where the
/// owner *cannot* cooperate. A model in which the dead cooperate does not need
/// them.
pub open spec fn tr_begin_transfer(
    pre: OwnershipSystem,
    post: OwnershipSystem,
    a: ActorId,
    from: HostId,
    to: HostId,
) -> bool {
    &&& pre.actors.contains_key(a)
    &&& pre.nodes.contains(to)
    &&& pre.live.contains(from)
    &&& from != to
    &&& match pre.actors[a] {
        OwnershipState::Owned { owner, epoch } =>
            owner == from
            && post.actors == pre.actors.insert(
                a,
                OwnershipState::Transferring {
                    from: from,
                    to: to,
                    old_epoch: epoch,
                    new_epoch: epoch + 1,
                },
            )
            && post.network == pre.network.insert(
                Message::Revoke { actor: a, target: from, old_epoch: epoch, new_epoch: epoch + 1 },
            )
            && post.issued == pre.issued
            && post.nodes == pre.nodes
            && post.live == pre.live,
        _ => false,
    }
}

/// A live node acknowledges a revocation it received.
///
/// The guard is deliberately weak: it requires only that *some* `Revoke` for
/// this actor is on the never-shrinking network and that `target` is live. It
/// does **not** require the actor to be `Transferring`, nor `target` to be its
/// owner, so any live node can manufacture a `Released` from any `Revoke` ever
/// sent, however ancient.
///
/// That is safe, but the reason is not "no ownership state changes" — it spans
/// three transitions, and is machine-checked rather than asserted here:
///
/// * `proofs::adversarial::theorem_complete_release_needs_the_matching_released`
///   — the only step that consumes a `Released` is `CompleteRelease`, which
///   re-reads the actor's *current* state, so a `Released` is inert unless the
///   actor is `Transferring` right now, away from exactly that node, at exactly
///   that `new_epoch`;
/// * `proofs::adversarial::theorem_complete_release_outcome_is_fixed_by_state`
///   — the resulting epoch is read from the live `Transferring` record, not
///   from the message, so a fabricated `Released` cannot steer the handover;
/// * `proofs::properties::theorem_stale_stays_stale` — no epoch is ever
///   revisited, so a `new_epoch` cannot come back around and make an old
///   `Released` relevant again.
pub open spec fn tr_handle_revoke(
    pre: OwnershipSystem,
    post: OwnershipSystem,
    a: ActorId,
    target: HostId,
    old_epoch: Epoch,
    new_epoch: Epoch,
) -> bool {
    &&& pre.live.contains(target)
    &&& pre.network.contains(
        Message::Revoke { actor: a, target: target, old_epoch: old_epoch, new_epoch: new_epoch },
    )
    &&& post.network == pre.network.insert(
        Message::Released { actor: a, from: target, new_epoch: new_epoch },
    )
    &&& post.actors == pre.actors
    &&& post.issued == pre.issued
    &&& post.nodes == pre.nodes
    &&& post.live == pre.live
}

/// The coordinator observed the release acknowledgement and publishes a grant
/// for the new epoch.
pub open spec fn tr_complete_release(pre: OwnershipSystem, post: OwnershipSystem, a: ActorId) -> bool {
    &&& pre.actors.contains_key(a)
    &&& match pre.actors[a] {
        OwnershipState::Transferring { from, to, old_epoch, new_epoch } =>
            pre.network.contains(Message::Released { actor: a, from: from, new_epoch: new_epoch })
            && post.actors == pre.actors.insert(
                a,
                OwnershipState::Unowned { epoch: new_epoch, intended_owner: to },
            )
            && post.network == pre.network.insert(
                Message::Grant { actor: a, to: to, epoch: new_epoch },
            )
            && post.issued == pre.issued
            && post.nodes == pre.nodes
            && post.live == pre.live,
        _ => false,
    }
}

/// An ownership transfer was interrupted midway (for example the coordinator
/// or `to` crashed while the actor was `Transferring`).
///
/// Recovery burns *another* epoch, so that any `Grant` for `new_epoch` that is
/// still in flight is already stale when it is delivered, and offers the actor
/// back to the original owner.
pub open spec fn tr_abort_transfer(pre: OwnershipSystem, post: OwnershipSystem, a: ActorId) -> bool {
    &&& pre.actors.contains_key(a)
    &&& match pre.actors[a] {
        OwnershipState::Transferring { from, to, old_epoch, new_epoch } =>
            post.actors == pre.actors.insert(
                a,
                OwnershipState::Unowned { epoch: new_epoch + 1, intended_owner: from },
            )
            && post.network == pre.network.insert(
                Message::Grant { actor: a, to: from, epoch: new_epoch + 1 },
            )
            && post.issued == pre.issued
            && post.nodes == pre.nodes
            && post.live == pre.live,
        _ => false,
    }
}

/// Forcible revocation: a failure detector decides the current owner is gone
/// and hands the actor to `next`.
///
/// Note that this transition does **not** require the owner to actually be
/// crashed. Failure detectors are unreliable, and modelling the wrong-suspicion
/// case is the whole point: safety must come from the epoch bump, not from the
/// detector being right.
pub open spec fn tr_revoke_owner(pre: OwnershipSystem, post: OwnershipSystem, a: ActorId, next: HostId) -> bool {
    &&& pre.actors.contains_key(a)
    &&& pre.nodes.contains(next)
    &&& match pre.actors[a] {
        OwnershipState::Owned { owner, epoch } =>
            post.actors == pre.actors.insert(
                a,
                OwnershipState::Unowned { epoch: epoch + 1, intended_owner: next },
            )
            && post.network == pre.network.insert(
                Message::Grant { actor: a, to: next, epoch: epoch + 1 },
            )
            && post.issued == pre.issued
            && post.nodes == pre.nodes
            && post.live == pre.live,
        _ => false,
    }
}

/// The intended owner never picked the actor up (it crashed, or the grant was
/// lost). Burn the epoch and offer the actor to somebody else.
pub open spec fn tr_reassign_unowned(pre: OwnershipSystem, post: OwnershipSystem, a: ActorId, next: HostId) -> bool {
    &&& pre.actors.contains_key(a)
    &&& pre.nodes.contains(next)
    &&& match pre.actors[a] {
        OwnershipState::Unowned { epoch, intended_owner } =>
            post.actors == pre.actors.insert(
                a,
                OwnershipState::Unowned { epoch: epoch + 1, intended_owner: next },
            )
            && post.network == pre.network.insert(
                Message::Grant { actor: a, to: next, epoch: epoch + 1 },
            )
            && post.issued == pre.issued
            && post.nodes == pre.nodes
            && post.live == pre.live,
        _ => false,
    }
}

/// The coordinator (re)publishes the grant for an actor's current epoch to its
/// intended owner. Retransmission is always safe: the grant only names state
/// that is already public.
pub open spec fn tr_issue_grant(pre: OwnershipSystem, post: OwnershipSystem, a: ActorId) -> bool {
    &&& pre.actors.contains_key(a)
    &&& match pre.actors[a] {
        OwnershipState::Unowned { epoch, intended_owner } =>
            post.network == pre.network.insert(
                Message::Grant { actor: a, to: intended_owner, epoch: epoch },
            )
            && post.actors == pre.actors
            && post.issued == pre.issued
            && post.nodes == pre.nodes
            && post.live == pre.live,
        _ => false,
    }
}

/// A node crashes. Its tokens stay in `issued`: crashing does not destroy the
/// physical capability the node was holding.
pub open spec fn tr_crash(pre: OwnershipSystem, post: OwnershipSystem, n: HostId) -> bool {
    &&& pre.live.contains(n)
    &&& post.live == pre.live.remove(n)
    &&& post.actors == pre.actors
    &&& post.issued == pre.issued
    &&& post.nodes == pre.nodes
    &&& post.network == pre.network
}

/// A crashed node comes back. It comes back still holding whatever tokens it
/// had before the crash, and with no knowledge of what happened meanwhile.
pub open spec fn tr_recover(pre: OwnershipSystem, post: OwnershipSystem, n: HostId) -> bool {
    &&& pre.nodes.contains(n)
    &&& !pre.live.contains(n)
    &&& post.live == pre.live.insert(n)
    &&& post.actors == pre.actors
    &&& post.issued == pre.issued
    &&& post.nodes == pre.nodes
    &&& post.network == pre.network
}

/// The network redelivers a message that was sent at some earlier point.
/// Explicit duplication/replay step.
pub open spec fn tr_replay(pre: OwnershipSystem, post: OwnershipSystem, m: Message) -> bool {
    &&& pre.network.contains(m)
    &&& post.network == pre.network.insert(m)
    &&& post.actors == pre.actors
    &&& post.issued == pre.issued
    &&& post.nodes == pre.nodes
    &&& post.live == pre.live
}

/// Nothing happens (models an arbitrary delay).
pub open spec fn tr_stutter(pre: OwnershipSystem, post: OwnershipSystem) -> bool {
    &&& post.actors == pre.actors
    &&& post.nodes == pre.nodes
    &&& post.live == pre.live
    &&& post.issued == pre.issued
    &&& post.network == pre.network
}

/// The labelled transitions of the OwnershipSystem.
pub enum Step {
    Acquire { actor: ActorId, node: HostId },
    BeginTransfer { actor: ActorId, from: HostId, to: HostId },
    HandleRevoke { actor: ActorId, target: HostId, old_epoch: Epoch, new_epoch: Epoch },
    CompleteRelease { actor: ActorId },
    AbortTransfer { actor: ActorId },
    RevokeOwner { actor: ActorId, next: HostId },
    ReassignUnowned { actor: ActorId, next: HostId },
    IssueGrant { actor: ActorId },
    Crash { node: HostId },
    Recover { node: HostId },
    Replay { msg: Message },
    Stutter,
}

/// The transition relation, indexed by the step that was taken.
pub open spec fn step(pre: OwnershipSystem, post: OwnershipSystem, s: Step) -> bool {
    match s {
        Step::Acquire { actor, node } => tr_acquire(pre, post, actor, node),
        Step::BeginTransfer { actor, from, to } => tr_begin_transfer(pre, post, actor, from, to),
        Step::HandleRevoke { actor, target, old_epoch, new_epoch } =>
            tr_handle_revoke(pre, post, actor, target, old_epoch, new_epoch),
        Step::CompleteRelease { actor } => tr_complete_release(pre, post, actor),
        Step::AbortTransfer { actor } => tr_abort_transfer(pre, post, actor),
        Step::RevokeOwner { actor, next } => tr_revoke_owner(pre, post, actor, next),
        Step::ReassignUnowned { actor, next } => tr_reassign_unowned(pre, post, actor, next),
        Step::IssueGrant { actor } => tr_issue_grant(pre, post, actor),
        Step::Crash { node } => tr_crash(pre, post, node),
        Step::Recover { node } => tr_recover(pre, post, node),
        Step::Replay { msg } => tr_replay(pre, post, msg),
        Step::Stutter => tr_stutter(pre, post),
    }
}

/// The unlabelled transition relation.
pub open spec fn next(pre: OwnershipSystem, post: OwnershipSystem) -> bool {
    exists|s: Step| step(pre, post, s)
}

/// Structural test used by [`init`]. Kept local to this module so that the
/// model does not depend on the specification layer.
pub open spec fn starts_unowned(s: OwnershipState) -> bool {
    match s {
        OwnershipState::Unowned { .. } => true,
        _ => false,
    }
}

/// Initial states: no actor is owned, nothing has been issued, nothing has
/// been sent, and every live node is a real node.
pub open spec fn init(sys: OwnershipSystem) -> bool {
    &&& (forall|a: ActorId| #[trigger] sys.actors.contains_key(a) ==> starts_unowned(sys.actors[a]))
    &&& (forall|t: Token| !(#[trigger] sys.issued.contains(t)))
    &&& (forall|m: Message| !(#[trigger] sys.network.contains(m)))
    &&& sys.live.subset_of(sys.nodes)
}

/// `tr` is a finite execution of the OwnershipSystem.
pub open spec fn valid_execution(tr: Seq<OwnershipSystem>) -> bool {
    &&& tr.len() > 0
    &&& init(tr[0])
    // A multi-trigger on *both* adjacent states. With `tr[i]` alone, the
    // conclusion introduces `tr[i + 1]`, which matches the trigger again at
    // `i + 1` and walks off the end of the sequence: the `0 <= i < tr.len() - 1`
    // antecedent is checked after instantiation, so it does not stop e-matching.
    // Requiring both terms means producing `tr[i + 1]` cannot fire the
    // quantifier unless `tr[i + 2]` is already in play.
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1]]
        0 <= i < tr.len() - 1 ==> next(tr[i], tr[i + 1]))
}

/// A **labelled** finite run: `tr` holds the states and `labels[i]` is the step
/// that takes `tr[i]` to `tr[i + 1]`.
///
/// `valid_execution` quantifies over `next`, which hides which step was taken
/// at each index. That is the right notion for a safety theorem - "whatever the
/// OwnershipSystem did, this holds" - and the wrong one for a scenario, whose entire
/// content is *which* steps were taken. A scenario assembled from reachable
/// endpoints and a step or two claims much less than it appears to: the
/// existentials can be satisfied from different executions, so the conjunction
/// need not describe any single run.
pub open spec fn run(tr: Seq<OwnershipSystem>, labels: Seq<Step>) -> bool {
    &&& tr.len() > 0
    &&& labels.len() == tr.len() - 1
    // Multi-trigger on both adjacent states and the label between them, for the
    // reason documented on `valid_execution`.
    &&& (forall|i: int|
        #![trigger tr[i], tr[i + 1], labels[i]]
        0 <= i < labels.len() ==> step(tr[i], tr[i + 1], labels[i]))
}

/// A labelled run that starts at initialisation.
pub open spec fn labelled_execution(tr: Seq<OwnershipSystem>, labels: Seq<Step>) -> bool {
    &&& run(tr, labels)
    &&& init(tr[0])
}

/// `sys` is reachable if some finite execution ends in it.
pub open spec fn reachable(sys: OwnershipSystem) -> bool {
    exists|tr: Seq<OwnershipSystem>| valid_execution(tr) && tr[tr.len() - 1] == sys
}

} // verus!
