//! A node's table, executable and verified.
//!
//! [`crate::swim::steps`] decides what a node believes about one peer after
//! hearing one record. This is the part that *holds* those beliefs: a
//! [`SwimTable`], one record per member that has ever been heard about, with the
//! two operations a node performs on it — read what it believes, and learn a
//! record. [`crate::swim::proofs::table`] proves that learning is the model's
//! `tr_gossip`, and that a self-refutation is a second gossip step.
//!
//! The table is a pair of vectors searched linearly. That is a choice for the
//! proof, not for the cluster: a node's table is bounded by its roster, which
//! the service caps at `MAX_UPDATES`.
//!
//! # What is verified
//!
//! * [`SwimTable::get`] is the model's `record_of`, with no entry meaning the
//!   fresh record.
//! * [`SwimTable::learn`] writes the merge of what is held and what arrived —
//!   and, if the record that changed is the node's own, the refutation merged on
//!   top of it — and nothing else changes.
//!
//! # What is not
//!
//! The roster (who may speak, which numbers are members), the lock, the audit
//! log, and the batch limit are the service's. So is the order in which a batch
//! is applied: each record is one step, and the theorems are about one.
#![allow(unused_imports)]
#![allow(clippy::new_without_default, clippy::len_without_is_empty)]

use vstd::prelude::*;

use crate::id::Id;
use crate::swim::model::*;
use crate::swim::proofs::refinement::*;
use crate::swim::steps::*;

verus! {

/// Every member that has ever been heard about, and what is believed of it.
///
/// A member with no entry is exactly a member at its fresh record.
pub struct SwimTable {
    /// The members, each once. Private: a table built or edited from outside
    /// could have an id with no record, and every method here assumes it does not.
    ids: Vec<Id>,
    /// `records[i]` is what is believed about `ids[i]`.
    records: Vec<ExecRecord>,
}

impl SwimTable {
    /// The table holds one record per member, each member once.
    pub closed spec fn well_formed(&self) -> bool {
        &&& self.ids@.len() == self.records@.len()
        &&& forall|i: int, j: int|
            0 <= i < self.ids@.len() && 0 <= j < self.ids@.len() && self.ids@[i] == self.ids@[j]
                ==> i == j
    }

    /// Whether `n` has an entry.
    pub closed spec fn has_entry(&self, n: Id) -> bool {
        exists|i: int| 0 <= i < self.ids@.len() && self.ids@[i] == n
    }

    /// What the table believes about `n`: its entry, or the fresh record.
    pub closed spec fn record(&self, n: Id) -> MemberRecord {
        if self.has_entry(n) {
            self.records@[choose|i: int| 0 <= i < self.ids@.len() && self.ids@[i] == n].view()
        } else {
            fresh_record()
        }
    }

    /// Where `id` is, if it is.
    fn find(&self, id: Id) -> (found: Option<usize>)
        requires
            self.well_formed(),
        ensures
            match found {
                Some(i) => i < self.ids@.len() && self.ids@[i as int] == id,
                None => forall|k: int| 0 <= k < self.ids@.len() ==> self.ids@[k] != id,
            },
    {
        let mut i: usize = 0;
        while i < self.ids.len()
            invariant
                i <= self.ids@.len(),
                forall|k: int| 0 <= k < i ==> self.ids@[k] != id,
            decreases self.ids@.len() - i,
        {
            if self.ids[i] == id {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// No entries: every member at its fresh record.
    pub fn new() -> (t: SwimTable)
        ensures
            t.well_formed(),
            forall|n: Id| t.record(n) == fresh_record(),
    {
        SwimTable { ids: Vec::new(), records: Vec::new() }
    }

    /// `record_of`: what the table believes about `id`.
    pub fn get(&self, id: Id) -> (r: ExecRecord)
        requires
            self.well_formed(),
        ensures
            r.view() == self.record(id),
    {
        match self.find(id) {
            Some(i) => {
                assert(self.has_entry(id));
                assert(self.ids@[i as int] == id);
                assert(self.record(id) == self.records@[i as int].view());
                self.records[i]
            },
            None => {
                assert(!self.has_entry(id));
                fresh_exec_record()
            },
        }
    }

    /// Write `rec` as the belief about `id`. Nothing else changes.
    fn put(&mut self, id: Id, rec: ExecRecord)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).record(id) == rec.view(),
            forall|n: Id| n != id ==> final(self).record(n) == old(self).record(n),
    {
        match self.find(id) {
            Some(i) => {
                self.records.set(i, rec);
                proof {
                    assert forall|n: Id| n != id implies self.record(n) == old(self).record(n) by {
                        if old(self).has_entry(n) {
                            let j = choose|j: int| 0 <= j < old(self).ids@.len() && old(self).ids@[j] == n;
                            assert(self.ids@[j] == n);
                            assert(j != i as int);
                            assert(self.has_entry(n));
                            let k = choose|k: int| 0 <= k < self.ids@.len() && self.ids@[k] == n;
                            assert(self.ids@[k] == self.ids@[j]);
                            assert(k == j);
                            assert(self.records@[k] == old(self).records@[j]);
                        } else {
                            assert(!self.has_entry(n));
                        }
                    }
                    assert(self.has_entry(id));
                    let k = choose|k: int| 0 <= k < self.ids@.len() && self.ids@[k] == id;
                    assert(self.ids@[k] == self.ids@[i as int]);
                    assert(k == i as int);
                }
            },
            None => {
                self.ids.push(id);
                self.records.push(rec);
                proof {
                    let last = (self.ids@.len() - 1) as int;
                    assert(self.ids@[last] == id);
                    assert(self.has_entry(id));
                    let k = choose|k: int| 0 <= k < self.ids@.len() && self.ids@[k] == id;
                    assert(self.ids@[k] == self.ids@[last]);
                    assert(k == last) by {
                        if k != last {
                            assert(self.ids@[k] == old(self).ids@[k]);
                            assert(old(self).ids@[k] != id);
                        }
                    }
                    assert forall|n: Id| n != id implies self.record(n) == old(self).record(n) by {
                        if old(self).has_entry(n) {
                            let j = choose|j: int| 0 <= j < old(self).ids@.len() && old(self).ids@[j] == n;
                            assert(self.ids@[j] == n);
                            assert(self.has_entry(n));
                            let k2 = choose|k2: int| 0 <= k2 < self.ids@.len() && self.ids@[k2] == n;
                            if k2 == last {
                                assert(self.ids@[k2] == id);
                                assert(false);
                            }
                            assert(self.ids@[k2] == old(self).ids@[k2]);
                            assert(self.ids@[k2] == self.ids@[j]);
                            assert(k2 == j) by {
                                assert(old(self).ids@[k2] == old(self).ids@[j]);
                            }
                        } else {
                            assert(!self.has_entry(n)) by {
                                if self.has_entry(n) {
                                    let k3 = choose|k3: int| 0 <= k3 < self.ids@.len() && self.ids@[k3] == n;
                                    if k3 == last {
                                        assert(self.ids@[k3] == id);
                                    } else {
                                        assert(old(self).ids@[k3] == n);
                                    }
                                }
                            }
                        }
                    }
                    assert forall|i: int, j: int|
                        0 <= i < self.ids@.len() && 0 <= j < self.ids@.len() && self.ids@[i] == self.ids@[j]
                            implies i == j by {
                        if i == last && j != last {
                            assert(old(self).ids@[j] != id);
                        } else if j == last && i != last {
                            assert(old(self).ids@[i] != id);
                        }
                    }
                }
            },
        }
    }

    /// `tr_gossip`: adopt `incoming` about `id` if it is at least as
    /// authoritative as what is held. Returns whether the belief changed.
    pub fn learn(&mut self, id: Id, incoming: ExecRecord) -> (changed: bool)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).record(id) == merge(old(self).record(id), incoming.view()),
            forall|n: Id| n != id ==> final(self).record(n) == old(self).record(n),
            changed == (final(self).record(id) != old(self).record(id)),
    {
        /* The table is a pair of vectors rather than a `HashMap` (vstd's hash-map
         * specs need `obeys_key_model`), so the read goes through `get`, the write
         * through `put`, and "the same record" is the verified comparison both ways.
         * Origin Rust: let held = g.table.get(&u.node).copied().unwrap_or_else(fresh);
         *              let merged = merge_step(held, u.record());
         *              if same(merged, held) {
         *                  return Ok(());
         *              }
         *              g.table.insert(u.node, merged);
         */
        let held = self.get(id);
        let merged = merge_step(held, incoming);
        let moved = !(key_geq_exec(held, merged) && key_geq_exec(merged, held));
        if moved {
            self.put(id, merged);
        } else {
            proof {
                assert(merged.view() == held.view()) by {
                    assert(key_geq(held.view(), merged.view()));
                    assert(key_geq(merged.view(), held.view()));
                    if held.view().incarnation == merged.view().incarnation {
                        lemma_rank_is_injective(held.view().status, merged.view().status);
                    }
                }
            }
        }
        proof {
            if !moved {
                assert(self.record(id) == held.view());
            }
        }
        moved
    }

    /// **A node hears a record about `id`**, and `me` is this node's own number.
    ///
    /// The record is merged in ([`SwimTable::learn`]); and if what changed is the
    /// node's *own* record, somebody has said something about it that out-ranks
    /// what it believes, so it answers with [`refute_step`] — `Alive`, one
    /// incarnation above the accusation — merged in through the same door. Two
    /// gossip steps, the second only when the first changed the node's own record.
    ///
    /// At the top of the incarnation space there is nothing to refute with: the
    /// first step has happened, the second has not, and it says so.
    pub fn hear(&mut self, id: Id, incoming: ExecRecord, me: Id) -> (r: Result<
        Heard,
        SwimRefusal,
    >)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            forall|n: Id| n != id ==> final(self).record(n) == old(self).record(n),
            ({
                let merged = merge(old(self).record(id), incoming.view());
                let changed = merged != old(self).record(id);
                match r {
                    Ok(h) => {
                        // At the top of the incarnation space there is nothing to
                        // refute with, and that is an `Err`, not an `Ok`.
                        &&& !(id == me && changed && merged.incarnation >= u64::MAX as nat)
                        &&& (h.learned is Some) == changed
                        &&& (h.learned matches Some(m) ==> m.view() == merged)
                        &&& (h.refuted is Some) == (id == me && changed
                            && merged.incarnation < u64::MAX as nat)
                        &&& (h.refuted matches Some(a) ==> a.view() == refutation(merged.incarnation)
                            && final(self).record(id) == a.view())
                        &&& (h.refuted is None ==> final(self).record(id) == merged)
                    },
                    Err(_) => {
                        &&& id == me
                        &&& changed
                        &&& merged.incarnation >= u64::MAX as nat
                        &&& final(self).record(id) == merged
                    },
                }
            }),
    {
        /* The audit log stays in the service, so the table reports what it learned
         * and what it answered with instead of pushing `Event`s; the refusal at the
         * top of the incarnation space is returned after the first merge, as before.
         * Origin Rust: if u.node == self.me {
         *                  let refutation = refute_step(merged.incarnation).map_err(refuse)?;
         *                  let after = merge_step(merged, refutation);
         *                  g.table.insert(self.me, after);
         *                  g.log.push(Event::Refuted { incarnation: after.incarnation });
         *              }
         */
        let changed = self.learn(id, incoming);
        if !changed {
            return Ok(Heard { learned: None, refuted: None });
        }
        let merged = self.get(id);
        if id != me {
            return Ok(Heard { learned: Some(merged), refuted: None });
        }
        match refute_step(merged.incarnation) {
            Ok(refutation_record) => {
                self.learn(me, refutation_record);
                let after = self.get(me);
                proof {
                    // The refutation out-ranks the accusation it answers.
                    theorem_a_refutation_outranks_what_it_answers(
                        merged.incarnation as nat,
                        merged.view(),
                    );
                }
                Ok(Heard { learned: Some(merged), refuted: Some(after) })
            },
            Err(why) => Err(why),
        }
    }
}

/// What a node's table did on hearing one record.
pub struct Heard {
    /// The belief that replaced the one held, if the record changed it.
    pub learned: Option<ExecRecord>,
    /// The node's own record after it refuted, if it did.
    pub refuted: Option<ExecRecord>,
}

} // verus!
