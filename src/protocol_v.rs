//! **Each model's [`Protocol`] instance says what the model already said.**
//!
//! A model instantiates [`Protocol`] by naming its own `init` and `step`; the trait
//! supplies `next` as "some step". Every model already defined its `next` the same
//! way, but a separate definition that happens to agree is exactly the kind of
//! agreement that drifts. These lemmas pin it: the trait's `next` *is* the model's
//! `next`, and `init` is the model's `init`, so a theorem stated against a model
//! and one stated against its [`Protocol`] are the same theorem.
//!
//! There is one lemma per model rather than a generic one, because the model's own
//! `next` is a different function in each module, and the only way to say "the
//! model's `next`" is to name it.
//!
//! The last lemma ties [`runs_of`] to the one liveness statement the crate already
//! makes (the mailbox's), so the generic way of saying "a run" and the existing one
//! are shown to be the same.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::actor::mailbox::model::*;
use crate::actor::model::*;
use crate::composed::model::*;
use crate::id::Id;
use crate::ownership::model as ownership_model;
use crate::protocol::*;
use crate::raft::model::*;
use crate::raymond::model::*;
use crate::swim::model as swim_model;
use crate::temporal::*;

verus! {

pub proof fn lemma_ownership_next_agrees(pre: ownership_model::OwnershipSystem, post: ownership_model::OwnershipSystem)
    ensures
        ownership_model::OwnershipProtocol::next(pre, post) <==> ownership_model::next(pre, post),
{
    if ownership_model::OwnershipProtocol::next(pre, post) {
        let l = choose|l: ownership_model::Step| #[trigger] ownership_model::OwnershipProtocol::step(pre, post, l);
        assert(ownership_model::step(pre, post, l));
    }
    if ownership_model::next(pre, post) {
        let l = choose|l: ownership_model::Step| #[trigger] ownership_model::step(pre, post, l);
        assert(ownership_model::OwnershipProtocol::step(pre, post, l));
    }
}

pub proof fn lemma_raft_next_agrees(pre: Cluster, post: Cluster)
    ensures
        RaftProtocol::next(pre, post) <==> raft_next(pre, post),
{
    if RaftProtocol::next(pre, post) {
        let l = choose|l: RaftStep| #[trigger] RaftProtocol::step(pre, post, l);
        assert(raft_step(pre, post, l));
    }
    if raft_next(pre, post) {
        let l = choose|l: RaftStep| #[trigger] raft_step(pre, post, l);
        assert(RaftProtocol::step(pre, post, l));
    }
}

pub proof fn lemma_raymond_next_agrees(pre: Raymond, post: Raymond)
    ensures
        RaymondProtocol::next(pre, post) <==> ray_next(pre, post),
{
    if RaymondProtocol::next(pre, post) {
        let l = choose|l: RayStep| #[trigger] RaymondProtocol::step(pre, post, l);
        assert(ray_step(pre, post, l));
    }
    if ray_next(pre, post) {
        let l = choose|l: RayStep| #[trigger] ray_step(pre, post, l);
        assert(RaymondProtocol::step(pre, post, l));
    }
}

pub proof fn lemma_swim_next_agrees(pre: swim_model::Cluster, post: swim_model::Cluster)
    ensures
        swim_model::SwimProtocol::next(pre, post) <==> swim_model::swim_next(pre, post),
{
    if swim_model::SwimProtocol::next(pre, post) {
        let l = choose|l: swim_model::SwimStep| #[trigger] swim_model::SwimProtocol::step(pre, post, l);
        assert(swim_model::swim_step(pre, post, l));
    }
    if swim_model::swim_next(pre, post) {
        let l = choose|l: swim_model::SwimStep| #[trigger] swim_model::swim_step(pre, post, l);
        assert(swim_model::SwimProtocol::step(pre, post, l));
    }
}

pub proof fn lemma_actor_next_agrees(pre: ActorSystem, post: ActorSystem)
    ensures
        ActorProtocol::next(pre, post) <==> actor_next(pre, post),
{
    if ActorProtocol::next(pre, post) {
        let l = choose|l: ActorStep| #[trigger] ActorProtocol::step(pre, post, l);
        assert(actor_step(pre, post, l));
    }
    if actor_next(pre, post) {
        let l = choose|l: ActorStep| #[trigger] actor_step(pre, post, l);
        assert(ActorProtocol::step(pre, post, l));
    }
}

pub proof fn lemma_mailbox_next_agrees(pre: Mailbox, post: Mailbox)
    ensures
        MailboxProtocol::next(pre, post) <==> mb_next(pre, post),
{
    if MailboxProtocol::next(pre, post) {
        let l = choose|l: MbStep| #[trigger] MailboxProtocol::step(pre, post, l);
        assert(mb_step(l, pre, post));
    }
    if mb_next(pre, post) {
        let l = choose|l: MbStep| #[trigger] mb_step(l, pre, post);
        assert(MailboxProtocol::step(pre, post, l));
    }
}

pub proof fn lemma_composed_next_agrees(pre: Composed, post: Composed)
    ensures
        ComposedProtocol::next(pre, post) <==> composed_next(pre, post),
{
    if ComposedProtocol::next(pre, post) {
        let l = choose|l: ComposedStep| #[trigger] ComposedProtocol::step(pre, post, l);
        assert(composed_step(pre, post, l));
    }
    if composed_next(pre, post) {
        let l = choose|l: ComposedStep| #[trigger] composed_step(pre, post, l);
        assert(ComposedProtocol::step(pre, post, l));
    }
}

/// `init` is the model's `init`, at the configuration the model has. These three
/// are by definition, and are stated so that a change to an instance's `init` that
/// stops being the model's `init` fails here.
pub proof fn lemma_init_agrees(
    c: swim_model::Cluster,
    m: Mailbox,
    r: Raymond,
    root: Id,
)
    ensures
        swim_model::SwimProtocol::init((), c) == swim_model::swim_init(c),
        MailboxProtocol::init((), m) == mb_init(m),
        RaymondProtocol::init(root, r) == ray_init(r, root),
{
}

/// A mailbox run in the crate's existing sense is a run of the mailbox *protocol*.
///
/// The existing statement is [`crate::actor::mailbox::proofs::invariant::lemma_mb_run_runs`].
pub proof fn lemma_mailbox_run_is_a_run_of_the_protocol(ex: spec_fn(nat) -> Mailbox)
    requires
        crate::actor::mailbox::proofs::invariant::mb_run(ex),
    ensures
        runs_of::<MailboxProtocol>((), ex),
{
    crate::actor::mailbox::proofs::invariant::lemma_mb_run_runs(ex);
    let next = |a: Mailbox, b: Mailbox| MailboxProtocol::next(a, b);
    assert forall|i: nat| #[trigger] next(ex(i), ex(i + 1)) by {
        lemma_mailbox_next_agrees(ex(i), ex(i + 1));
    }
}

} // verus!
