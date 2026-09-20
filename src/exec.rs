//! The only *executable* code in this crate.
//!
//! Everything else here is specification and proof. This module is the thin
//! runtime counterpart: the `u64`-valued fence check a node actually performs
//! before touching an actor, together with a proof that it agrees with the
//! model's [`may_mutate`].
//!
//! It is deliberately tiny. There is no networking, no persistence and no actor
//! runtime; proving the protocol says nothing about whether an implementation
//! follows it, and this module exists only to pin down the one place where the
//! two meet.
//!
//! **What this check is, and what it is not.** `accepts` consults the node's
//! *own* belief about the actor, which is whatever generation it last observed.
//! A partitioned `A` still holding `FenceGuard::new(A, 41)` gets
//! `accepts(A, 41) == true` while the system has already moved to
//! `Owned { B, 42 }`. That is not a contradiction — the postcondition promises
//! `may_mutate(self.view(), ..)`, and `view()` is exactly that stale belief —
//! but it means **a node cannot fence itself**. The safety property proved in
//! `crate::proofs` is about the *system's* state (`can_mutate(sys, ..)`), and
//! nothing in this module connects a guard to it.
//!
//! So what a guard buys is node-local staleness rejection, not fencing. Real
//! fencing has to happen where the effect lands, against authoritative state:
//! the storage layer rejecting a write whose epoch is superseded, or a reply
//! gate that re-reads the ownership record after a write is durable and before
//! acknowledging it, refusing the acknowledgement if the record no longer names
//! this node at this epoch. That check is what turns exclusivity into something
//! an outsider can rely on, and it is not in this crate.
//!
//! Note what is *not* here: there is no operation that mutates a [`FenceGuard`],
//! and its fields are private so callers cannot assign to them either. A guard
//! is an immutable record that only ever answers questions. Any mutator would,
//! at the level of
//! [`FenceGuard::view`], move an actor straight from `Owned(A, e)` to
//! `Owned(B, e + 1)` - precisely the atomic ownership assignment the model
//! refuses to admit, and which `proofs::transfer::theorem_ownership_only_via_acquire`
//! rules out for the model's own transitions. Making a guard follow the protocol
//! needs the refinement relation listed as future work in `README.md`, so until
//! that exists this module offers queries only.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::fencing::*;
use crate::model::*;
use crate::ownership::*;

verus! {

/// A node's local, executable record of "actor X is owned by `owner` at
/// `epoch`". This is the `Owned` case of [`OwnershipState`] narrowed to `u64`,
/// which is the only case in which anybody may mutate anything.
pub struct FenceGuard {
    owner: u64,
    epoch: u64,
}

impl FenceGuard {
    /// The ghost `OwnershipState` this guard stands for.
    ///
    /// `closed` because the fields are private: outside this module a guard is
    /// an opaque, immutable record, and the only way to learn what it stands
    /// for is the postcondition of [`FenceGuard::new`].
    pub closed spec fn view(self) -> OwnershipState {
        OwnershipState::Owned { owner: self.owner as nat, epoch: self.epoch as nat }
    }

    /// The only constructor.
    ///
    /// A guard is an **immutable** record of one ownership generation that this
    /// node has observed. The fields are private and there is no setter, so a
    /// guard's `view()` is fixed at construction: it cannot drift from
    /// `Owned(A, e)` to `Owned(B, e + 1)` the way a mutable guard could, which
    /// would be the atomic ownership assignment the model exists to forbid.
    /// Observing a *new* generation means constructing a *new* guard.
    pub fn new(owner: u64, epoch: u64) -> (r: FenceGuard)
        ensures
            r.view() == (OwnershipState::Owned { owner: owner as nat, epoch: epoch as nat }),
    {
        FenceGuard { owner: owner, epoch: epoch }
    }

    /// **The node-local staleness check.** Returns exactly the model's verdict
    /// *for the generation this guard records* — see the module docs on why
    /// that is not the same as fencing. A stale guard accepts stale requests.
    pub fn accepts(&self, node: u64, epoch: u64) -> (r: bool)
        ensures
            r == may_mutate(self.view(), node as nat, epoch as nat),
    {
        node == self.owner && epoch == self.epoch
    }

    /// A request carrying a superseded epoch is rejected. This is
    /// `theorem_stale_epoch_cannot_mutate` made executable.
    pub fn rejects_stale(&self, node: u64, epoch: u64) -> (r: bool)
        requires
            (epoch as nat) < current_epoch(self.view()),
        ensures
            r,
            !may_mutate(self.view(), node as nat, epoch as nat),
    {
        proof {
            lemma_stale_epoch_cannot_mutate(self.view(), node as nat, epoch as nat);
        }
        !self.accepts(node, epoch)
    }
}

} // verus!
