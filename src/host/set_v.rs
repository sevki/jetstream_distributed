//! A set of hosts, executable and verified.
//!
//! Three places kept "a set of hosts" in a `Vec<HostId>` and proved, each time,
//! that a linear scan stands for a [`Set`]: the Raft tally of votes, the composed
//! machine's debts, and the lemma between them. A [`HostSet`] is the one
//! implementation, over [`std::collections::HashSet`], whose specification type
//! is `Set<HostId>` — so the abstraction is vstd's rather than ours, and what
//! each method promises is stated in terms of that set.
//!
//! # What is trusted
//!
//! vstd's specifications of `HashSet`, and in particular
//! `obeys_key_model::<u128>()`: that the standard library's default hasher
//! behaves as a function on keys. That assumption is stated in vstd, not in this
//! repository, and `README.md` names it. The `Vec` this
//! replaces rested on nothing beyond `Vec`'s own specification.
//!
//! Iteration order is not specified. Anything that serialises a set sorts first.
#![allow(unused_imports)]
#![allow(clippy::new_without_default)]

use std::collections::HashSet;

use vstd::prelude::*;

use crate::host::HostId;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// A set of hosts.
pub struct HostSet {
    hosts: HashSet<HostId>,
}

impl View for HostSet {
    type V = Set<HostId>;

    closed spec fn view(&self) -> Set<HostId> {
        self.hosts@
    }
}

impl HostSet {
    /// The empty set.
    pub fn new() -> (s: HostSet)
        ensures
            s@ == Set::<HostId>::empty(),
    {
        HostSet { hosts: HashSet::new() }
    }

    /// Whether `x` is in the set.
    pub fn contains(&self, x: HostId) -> (r: bool)
        ensures
            r == self@.contains(x),
    {
        self.hosts.contains(&x)
    }

    /// Add `x`. Adding a member again changes nothing.
    pub fn insert(&mut self, x: HostId)
        ensures
            final(self)@ == old(self)@.insert(x),
    {
        self.hosts.insert(x);
    }

    /// Remove `x`. Removing a stranger changes nothing.
    pub fn remove(&mut self, x: HostId)
        ensures
            final(self)@ == old(self)@.remove(x),
    {
        self.hosts.remove(&x);
    }

    /// How many hosts are in the set.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self@.len(),
    {
        self.hosts.len()
    }

    /// Whether the set has no hosts.
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == self@.is_empty(),
    {
        self.hosts.is_empty()
    }

    /// The members, for a caller that wants to look at them. Their order is not
    /// specified, and nothing is promised about them beyond what `HashSet` does.
    pub fn as_std(&self) -> (r: &HashSet<HostId>)
        ensures
            r@ == self@,
    {
        &self.hosts
    }
}

} // verus!
