//! A set of ids, executable and verified.
//!
//! Three places kept "a set of hosts" in a `Vec<Id>` and proved, each time, that a
//! linear scan stands for a [`Set`]: the Raft tally of votes, the composed
//! machine's debts, and the lemma between them. An [`IdSet`] is the one
//! implementation, over [`std::collections::HashSet`], whose specification type is
//! `Set<Id>` — so the abstraction is vstd's rather than ours, and what each method
//! promises is stated in terms of that set.
//!
//! # What is trusted
//!
//! vstd's specifications of `HashSet`, and in particular
//! `obeys_key_model::<u128>()`: that the standard library's default hasher
//! behaves as a function on keys. That assumption is stated in vstd, not in this
//! repository, and `README.md` names it. The `Vec` this
//! replaces rested on nothing beyond `Vec`'s own specification.
//!
//! The set holds the `u128` inside each [`Id`], not the `Id`: vstd states that
//! assumption for the built-in key types and it cannot be proved for a type of
//! ours. [`lift`] is the spec function that turns the stored numbers back into ids.
//!
//! Iteration order is not specified. Anything that serialises a set sorts first.
#![allow(unused_imports)]
#![allow(clippy::new_without_default)]

use std::collections::HashSet;

use vstd::prelude::*;

use crate::id::Id;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// The ids whose numbers are `s`.
pub open spec fn lift(s: Set<u128>) -> Set<Id> {
    s.map(|y: u128| Id(y))
}

/// An id is in `lift(s)` exactly when its number is in `s`.
pub proof fn lemma_lift_contains(s: Set<u128>, z: Id)
    ensures
        lift(s).contains(z) <==> s.contains(z.0),
{
    if s.contains(z.0) {
        assert(s.map(|y: u128| Id(y)).contains(Id(z.0)));
        assert(lift(s).contains(z));
    }
    if lift(s).contains(z) {
        let y = choose|y: u128| s.contains(y) && Id(y) == z;
        assert(y == z.0);
    }
}

/// Lifting does not change how many there are: `Id` is injective.
pub proof fn lemma_lift_len(s: Set<u128>)
    ensures
        lift(s).len() == s.len(),
{
    let f = |y: u128| Id(y);
    assert(s.injective_on(f));
    vstd::set_lib::lemma_map_size(s, lift(s), f);
}

/// A set of ids.
pub struct IdSet {
    ids: HashSet<u128>,
}

impl View for IdSet {
    type V = Set<Id>;

    closed spec fn view(&self) -> Set<Id> {
        lift(self.ids@)
    }
}

impl IdSet {
    /// The empty set.
    pub fn new() -> (s: IdSet)
        ensures
            s@ == Set::<Id>::empty(),
    {
        let s = IdSet { ids: HashSet::new() };
        proof {
            assert(s.ids@ == Set::<u128>::empty());
            assert(lift(s.ids@) == Set::<Id>::empty());
        }
        s
    }

    /// Whether `x` is in the set.
    pub fn contains(&self, x: Id) -> (r: bool)
        ensures
            r == self@.contains(x),
    {
        let r = self.ids.contains(&x.0);
        proof {
            lemma_lift_contains(self.ids@, x);
        }
        r
    }

    /// Add `x`. Adding a member again changes nothing.
    pub fn insert(&mut self, x: Id)
        ensures
            final(self)@ == old(self)@.insert(x),
    {
        self.ids.insert(x.0);
        proof {
            assert forall|z: Id| #[trigger] lift(final(self).ids@).contains(z) == lift(
                old(self).ids@,
            ).insert(x).contains(z) by {
                lemma_lift_contains(final(self).ids@, z);
                lemma_lift_contains(old(self).ids@, z);
            }
            assert(lift(final(self).ids@) == lift(old(self).ids@).insert(x));
        }
    }

    /// Remove `x`. Removing a stranger changes nothing.
    pub fn remove(&mut self, x: Id)
        ensures
            final(self)@ == old(self)@.remove(x),
    {
        self.ids.remove(&x.0);
        proof {
            assert forall|z: Id| #[trigger] lift(final(self).ids@).contains(z) == lift(
                old(self).ids@,
            ).remove(x).contains(z) by {
                lemma_lift_contains(final(self).ids@, z);
                lemma_lift_contains(old(self).ids@, z);
            }
            assert(lift(final(self).ids@) == lift(old(self).ids@).remove(x));
        }
    }

    /// How many ids are in the set.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self@.len(),
    {
        proof {
            lemma_lift_len(self.ids@);
        }
        self.ids.len()
    }

    /// Whether the set has no ids.
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == self@.is_empty(),
    {
        proof {
            lemma_lift_len(self.ids@);
        }
        self.ids.is_empty()
    }
}

} // verus!

impl IdSet {
    /// The members, for a caller that wants to look at them. Their order is not
    /// specified, and nothing is promised about them beyond what `HashSet` does.
    pub fn iter(&self) -> impl Iterator<Item = Id> + '_ {
        self.ids.iter().map(|&n| Id(n))
    }
}
