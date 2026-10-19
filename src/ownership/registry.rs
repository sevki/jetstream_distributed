//! The registry's record, executable and verified.
//!
//! [`crate::ownership::steps`] decides what a request does to the actor's record.
//! The registry also keeps two things the record is not: the **grants it has
//! published**, which stand for the model's `Grant` messages on the network, and
//! a **count of writes**. A [`RegistryCore`] is the three together, with one
//! method per thing a registry does, and each method's contract says what it
//! does to all three.
//!
//! # Why the grants are here
//!
//! `acquire_step` takes `granted` as an input standing for
//! `sys.network.contains(Grant { .. })`, and [`crate::ownership::proofs::refinement`]
//! applies its refusal theorem under the hypothesis that the registry's set *is*
//! the network's `Grant`s. That equality is not a fact about a function; it is a
//! fact the registry has to keep true by publishing a grant at every transition
//! that publishes one — a poll, a release, and each of the three forced moves —
//! and one registry did not, for a long time. The set and the state now change
//! in one method, under one contract, and
//! [`crate::ownership::proofs::registry`] shows the contract is the model's.
//!
//! # What is verified
//!
//! * `poll`, `acquire`, `begin_transfer`, `release`, `force` and `write` are the
//!   model's steps on the record, and each says exactly which grants it
//!   publishes: `poll` the one it answers with, `release` and `force` the one
//!   they move the actor on to, the others none.
//! * A refusal changes nothing.
//!
//! # What is not
//!
//! The lock, the identity lookup, the audit log, and the **durable epoch floor**.
//! `begin_transfer` and `force` take a `persist` closure, call it with the epoch
//! they are about to burn, and move only if it says the epoch is written down.
//! That the closure is called *before* the state moves is the code above; what
//! it makes durable is the caller's.
#![allow(unused_imports)]
#![allow(clippy::new_without_default)]

use vstd::prelude::*;

use crate::ownership::fencing::*;
use crate::ownership::model::*;
use crate::ownership::spec::*;
use crate::ownership::steps::*;

verus! {

/// The actor's record, the grants published, and the writes landed.
pub struct RegistryCore {
    /// The actor's ownership record.
    pub state: ExecState,
    /// Grants published, as `(node, epoch)`: the model's `Grant` messages.
    pub grants: Vec<(u64, u64)>,
    /// Writes landed so far.
    pub writes: u64,
}

/// Why a transition that burns an epoch did not happen.
#[derive(Clone, Copy)]
pub enum BurnRefusal {
    /// The protocol declined it.
    Refused(Refusal),
    /// The epoch could not be made durable, so it was not used.
    Down,
}

/// What a write did.
#[derive(Clone, Copy)]
pub enum WriteOutcome {
    /// It landed, at this sequence number.
    Wrote(u64),
    /// The fence stopped it.
    Fenced,
    /// The count of writes would wrap.
    Exhausted,
}

impl RegistryCore {
    /// `(n, e)` has been published.
    pub open spec fn has_grant(&self, n: nat, e: nat) -> bool {
        exists|k: int|
            0 <= k < self.grants@.len() && self.grants@[k].0 as nat == n && self.grants@[k].1 as nat
                == e
    }
}

/// The grants are as they were.
pub open spec fn grants_same(pre: RegistryCore, post: RegistryCore) -> bool {
    forall|n: nat, e: nat| #[trigger] post.has_grant(n, e) == pre.has_grant(n, e)
}

/// The grants are as they were, and `(node, epoch)` is now among them.
pub open spec fn grants_plus(pre: RegistryCore, post: RegistryCore, node: nat, epoch: nat) -> bool {
    forall|n: nat, e: nat|
        #[trigger] post.has_grant(n, e) == (pre.has_grant(n, e) || (n == node && e == epoch))
}

/// Nothing about the registry changed.
pub open spec fn unchanged(pre: RegistryCore, post: RegistryCore) -> bool {
    &&& post.state.view() == pre.state.view()
    &&& post.writes == pre.writes
    &&& grants_same(pre, post)
}

impl RegistryCore {
    /// An actor offered to `intended` at `epoch`, nothing published, nothing
    /// written. The model's initial record: `Unowned` and an empty network.
    pub fn new(epoch: u64, intended: u64) -> (c: RegistryCore)
        ensures
            c.state.view() == (OwnershipState::Unowned {
                epoch: epoch as nat,
                intended_owner: intended as nat,
            }),
            c.writes == 0,
            forall|n: nat, e: nat| !c.has_grant(n, e),
    {
        RegistryCore {
            state: ExecState::Unowned { epoch, intended },
            grants: Vec::new(),
            writes: 0,
        }
    }

    /// Whether `(node, epoch)` has been published.
    pub fn granted(&self, node: u64, epoch: u64) -> (r: bool)
        ensures
            r == self.has_grant(node as nat, epoch as nat),
    {
        let mut k: usize = 0;
        while k < self.grants.len()
            invariant
                k <= self.grants@.len(),
                forall|m: int| 0 <= m < k ==> self.grants@[m] != (node, epoch),
            decreases self.grants@.len() - k,
        {
            if self.grants[k].0 == node && self.grants[k].1 == epoch {
                return true;
            }
            k += 1;
        }
        false
    }

    /// Publish a grant.
    fn publish(&mut self, node: u64, epoch: u64)
        ensures
            final(self).state.view() == old(self).state.view(),
            final(self).writes == old(self).writes,
            grants_plus(*old(self), *final(self), node as nat, epoch as nat),
    {
        let ghost before = *self;
        self.grants.push((node, epoch));
        proof {
            assert forall|n: nat, e: nat|
                #[trigger] self.has_grant(n, e) == (before.has_grant(n, e) || (n == node as nat
                    && e == epoch as nat)) by {
                if self.has_grant(n, e) && !(n == node as nat && e == epoch as nat) {
                    let k = choose|k: int|
                        0 <= k < self.grants@.len() && self.grants@[k].0 as nat == n
                            && self.grants@[k].1 as nat == e;
                    assert(k < before.grants@.len());
                }
                if before.has_grant(n, e) {
                    let k = choose|k: int|
                        0 <= k < before.grants@.len() && before.grants@[k].0 as nat == n
                            && before.grants@[k].1 as nat == e;
                    assert(self.grants@[k] == before.grants@[k]);
                }
                if n == node as nat && e == epoch as nat {
                    let last = (self.grants@.len() - 1) as int;
                    assert(self.grants@[last] == (node, epoch));
                }
            }
        }
    }

    /// `poll`: what is on offer for `node`. A grant it answers with is published
    /// — `tr_issue_grant`, which is retransmission and always safe, the grant
    /// naming only state that is already public.
    pub fn poll(&mut self, node: u64) -> (r: ExecOffer)
        ensures
            r == poll_answer(old(self).state, node),
            final(self).state.view() == old(self).state.view(),
            final(self).writes == old(self).writes,
            match r {
                ExecOffer::Grant(e) => grants_plus(*old(self), *final(self), node as nat, e as nat),
                _ => grants_same(*old(self), *final(self)),
            },
    {
        let offer = poll_step(self.state, node);
        if let ExecOffer::Grant(epoch) = offer {
            self.publish(node, epoch);
        }
        offer
    }

    /// `tr_acquire`: take an offered grant — which has to have been published.
    pub fn acquire(&mut self, node: u64, epoch: u64) -> (r: Result<(), Refusal>)
        ensures
            final(self).writes == old(self).writes,
            grants_same(*old(self), *final(self)),
            match r {
                Ok(_) => {
                    &&& acquire_fires(
                        old(self).state.view(),
                        node as nat,
                        epoch as nat,
                        old(self).has_grant(node as nat, epoch as nat),
                    )
                    &&& final(self).state.view() == acquire_next(old(self).state.view(), node as nat)
                },
                Err(_) => {
                    &&& !acquire_fires(
                        old(self).state.view(),
                        node as nat,
                        epoch as nat,
                        old(self).has_grant(node as nat, epoch as nat),
                    )
                    &&& final(self).state.view() == old(self).state.view()
                },
            },
    {
        let granted = self.granted(node, epoch);
        let ghost before = *self;
        match acquire_step(self.state, node, epoch, granted) {
            Outcome::Moved(next) => {
                self.state = next;
                proof {
                    assert(self.grants@ == before.grants@);
                    assert forall|n: nat, e: nat| #[trigger] self.has_grant(n, e) == before.has_grant(n, e) by {}
                }
                Ok(())
            },
            Outcome::Refused(why) => Err(why),
        }
    }

    /// The fence, at the point where the effect lands. A write that passes it is
    /// counted.
    pub fn write(&mut self, node: u64, epoch: u64) -> (r: WriteOutcome)
        ensures
            final(self).state.view() == old(self).state.view(),
            grants_same(*old(self), *final(self)),
            match r {
                WriteOutcome::Wrote(seq) => {
                    &&& may_mutate(old(self).state.view(), node as nat, epoch as nat)
                    &&& old(self).writes < u64::MAX
                    &&& seq == old(self).writes + 1
                    &&& final(self).writes == seq
                },
                WriteOutcome::Fenced => {
                    &&& !may_mutate(old(self).state.view(), node as nat, epoch as nat)
                    &&& final(self).writes == old(self).writes
                },
                WriteOutcome::Exhausted => {
                    &&& may_mutate(old(self).state.view(), node as nat, epoch as nat)
                    &&& old(self).writes == u64::MAX
                    &&& final(self).writes == old(self).writes
                },
            },
    {
        if !may_write_step(self.state, node, epoch) {
            return WriteOutcome::Fenced;
        }
        if self.writes == u64::MAX {
            return WriteOutcome::Exhausted;
        }
        self.writes += 1;
        WriteOutcome::Wrote(self.writes)
    }

    /// `tr_begin_transfer`: the owner agrees to hand the actor to `to`. The next
    /// epoch is passed to `persist` and the actor moves only if it says the epoch
    /// is written down: durable before visible.
    pub fn begin_transfer<F: FnOnce(u64) -> bool>(
        &mut self,
        from: u64,
        to: u64,
        to_is_node: bool,
        persist: F,
    ) -> (r: Result<(), BurnRefusal>)
        requires
            forall|e: u64| call_requires(persist, (e,)),
        ensures
            final(self).writes == old(self).writes,
            grants_same(*old(self), *final(self)),
            match r {
                Ok(_) => {
                    &&& begin_transfer_fires(
                        old(self).state.view(),
                        from as nat,
                        to as nat,
                        to_is_node,
                    )
                    &&& final(self).state.view() == begin_transfer_next(
                        old(self).state.view(),
                        to as nat,
                    )
                },
                Err(BurnRefusal::Refused(why)) => {
                    &&& (!begin_transfer_fires(old(self).state.view(), from as nat, to as nat, to_is_node)
                        || (why is Exhausted))
                    &&& final(self).state.view() == old(self).state.view()
                },
                Err(BurnRefusal::Down) => {
                    &&& begin_transfer_fires(old(self).state.view(), from as nat, to as nat, to_is_node)
                    &&& final(self).state.view() == old(self).state.view()
                },
            },
    {
        match begin_transfer_step(self.state, from, to, to_is_node) {
            Outcome::Moved(moved) => {
                if persist(moved.current()) {
                    self.state = moved;
                    Ok(())
                } else {
                    Err(BurnRefusal::Down)
                }
            },
            Outcome::Refused(why) => Err(BurnRefusal::Refused(why)),
        }
    }

    /// `tr_handle_revoke` then `tr_complete_release`: the outgoing owner
    /// acknowledges, and the actor is offered on — and that offer is published.
    /// Returns the node it is offered to.
    pub fn release(&mut self, node: u64, epoch: u64) -> (r: Result<u64, Refusal>)
        ensures
            final(self).writes == old(self).writes,
            match r {
                Ok(to) => {
                    &&& release_fires(old(self).state.view(), node as nat, epoch as nat)
                    &&& final(self).state.view() == release_next(old(self).state.view())
                    &&& to as nat == intended_owner(final(self).state.view())
                    &&& grants_plus(*old(self), *final(self), to as nat, epoch as nat)
                },
                Err(_) => {
                    &&& !release_fires(old(self).state.view(), node as nat, epoch as nat)
                    &&& final(self).state.view() == old(self).state.view()
                    &&& grants_same(*old(self), *final(self))
                },
            },
    {
        match release_step(self.state, node, epoch) {
            Outcome::Moved(next) => {
                self.state = next;
                let to = next.intended();
                self.publish(to, epoch);
                Ok(to)
            },
            Outcome::Refused(why) => Err(why),
        }
    }

    /// `tr_revoke_owner`, `tr_reassign_unowned` or `tr_abort_transfer`: the
    /// coordinator forcing progress. The new epoch is passed to `persist` first.
    /// Returns the node the actor is now offered to, which is not always `next`,
    /// and publishes that offer.
    pub fn force<F: FnOnce(u64) -> bool>(
        &mut self,
        next: u64,
        next_is_node: bool,
        persist: F,
    ) -> (r: Result<u64, BurnRefusal>)
        requires
            forall|e: u64| call_requires(persist, (e,)),
        ensures
            final(self).writes == old(self).writes,
            match r {
                Ok(offered) => {
                    &&& force_fires(old(self).state.view(), next_is_node)
                    &&& final(self).state.view() == force_next(old(self).state.view(), next as nat)
                    &&& offered as nat == force_offers_to(old(self).state.view(), next as nat)
                    &&& grants_plus(
                        *old(self),
                        *final(self),
                        offered as nat,
                        current_epoch(final(self).state.view()),
                    )
                },
                Err(BurnRefusal::Refused(why)) => {
                    &&& (!force_fires(old(self).state.view(), next_is_node) || (why is Exhausted))
                    &&& final(self).state.view() == old(self).state.view()
                    &&& grants_same(*old(self), *final(self))
                },
                Err(BurnRefusal::Down) => {
                    &&& force_fires(old(self).state.view(), next_is_node)
                    &&& final(self).state.view() == old(self).state.view()
                    &&& grants_same(*old(self), *final(self))
                },
            },
    {
        match force_step(self.state, next, next_is_node) {
            ForceOutcome::Moved(moved, offered) => {
                let epoch = moved.current();
                if persist(epoch) {
                    self.state = moved;
                    self.publish(offered, epoch);
                    Ok(offered)
                } else {
                    Err(BurnRefusal::Down)
                }
            },
            ForceOutcome::Refused(why) => Err(BurnRefusal::Refused(why)),
        }
    }
}

} // verus!
