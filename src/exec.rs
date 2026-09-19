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
    pub owner: u64,
    pub epoch: u64,
}

impl FenceGuard {
    /// The ghost `OwnershipState` this guard stands for.
    pub open spec fn view(self) -> OwnershipState {
        OwnershipState::Owned { owner: self.owner as nat, epoch: self.epoch as nat }
    }

    /// **The runtime fence check.** Returns exactly the model's verdict.
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
            epoch < self.epoch,
        ensures
            r,
            !may_mutate(self.view(), node as nat, epoch as nat),
    {
        proof {
            lemma_stale_epoch_cannot_mutate(self.view(), node as nat, epoch as nat);
        }
        !self.accepts(node, epoch)
    }

    /// Start the next ownership generation.
    ///
    /// Epoch exhaustion is a hard failure rather than a wraparound: the model
    /// uses `nat`, so an implementation must guarantee there is room. The
    /// precondition is that guarantee, made explicit.
    pub fn bump(&mut self, next_owner: u64)
        requires
            old(self).epoch < u64::MAX,
        ensures
            final(self).epoch == old(self).epoch + 1,
            final(self).owner == next_owner,
            current_epoch(final(self).view()) > current_epoch(old(self).view()),
    {
        self.epoch = self.epoch + 1;
        self.owner = next_owner;
    }
}

} // verus!
