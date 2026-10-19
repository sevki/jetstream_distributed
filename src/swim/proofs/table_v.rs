//! The executable table is the model.
//!
//! [`crate::swim::exec::SwimTable`] is what a node keeps, and each of its
//! operations has a contract about [`SwimTable::record`]. These theorems show the
//! contract is the model's step: given a model cluster the table stands for, a
//! table that learns a record stands for the cluster the model's `tr_gossip`
//! produces, and a table that hears a record about itself stands for the cluster
//! after two of them.
//!
//! # The relation
//!
//! [`stands_for`] says the table and the cluster agree about every member:
//! `record_of(c, n)` is `t.record(n)`. A member with no entry and a member at its
//! fresh record are the same thing on both sides, which is why the model's
//! `record_of` is the thing to compare — a table that skips a write because
//! nothing changed and a cluster that inserts the record it already had stand for
//! each other.
//!
//! # What is not here
//!
//! Which numbers are members and which callers may speak are the service's; the
//! lock and the audit log are too. The theorems are about one record at a time.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::host::HostId;
use crate::swim::exec::*;
use crate::swim::model::*;
use crate::swim::proofs::merge::*;
use crate::swim::proofs::monotone::*;
use crate::swim::proofs::refinement::*;
use crate::swim::steps::*;

verus! {

/// The table stands for the cluster: they agree about every member.
pub open spec fn stands_for(t: SwimTable, c: Cluster) -> bool {
    forall|n: HostId| #[trigger] t.record(n) == record_of(c, n)
}

/// The cluster in which `n` has been heard about with `incoming` and nothing else
/// has changed.
pub open spec fn after_gossip(c: Cluster, n: HostId, incoming: MemberRecord) -> Cluster {
    Cluster { members: c.members.insert(n, merge(record_of(c, n), incoming)) }
}

/// **A new table is the model's initial state.**
pub proof fn theorem_new_table_is_the_initial_cluster(t: SwimTable)
    requires
        forall|n: HostId| t.record(n) == fresh_record(),
    ensures
        exists|c: Cluster| swim_init(c) && stands_for(t, c),
{
    let c = Cluster { members: Map::empty() };
    assert(swim_init(c));
    assert forall|n: HostId| #[trigger] t.record(n) == record_of(c, n) by {
        assert(!c.members.contains_key(n));
    }
}

/// **`learn` is the model's `tr_gossip`.**
///
/// A table standing for `c` that learns `incoming` about `id` stands for the
/// cluster `tr_gossip` leads to — and that step is a step of the model.
pub proof fn theorem_learn_is_a_gossip_step(
    pre: SwimTable,
    post: SwimTable,
    c: Cluster,
    id: HostId,
    incoming: MemberRecord,
)
    requires
        stands_for(pre, c),
        post.record(id) == merge(pre.record(id), incoming),
        forall|n: HostId| n != id ==> #[trigger] post.record(n) == pre.record(n),
    ensures
        tr_gossip(c, after_gossip(c, id, incoming), id, incoming),
        swim_next(c, after_gossip(c, id, incoming)),
        stands_for(post, after_gossip(c, id, incoming)),
{
    let c2 = after_gossip(c, id, incoming);
    assert(tr_gossip(c, c2, id, incoming));
    let s = SwimStep::Gossip { node: id, incoming };
    assert(swim_step(c, c2, s));
    assert forall|n: HostId| #[trigger] post.record(n) == record_of(c2, n) by {
        if n == id {
            assert(c2.members.contains_key(id));
        } else {
            assert(c2.members.contains_key(n) == c.members.contains_key(n));
        }
    }
}

/// **A table never forgets how far a member has got.** Whatever it learns, what
/// it then believes about any member out-ranks, or equals, what it believed.
pub proof fn theorem_learning_never_lowers_a_belief(
    pre: SwimTable,
    post: SwimTable,
    id: HostId,
    incoming: MemberRecord,
    n: HostId,
)
    requires
        post.record(id) == merge(pre.record(id), incoming),
        forall|m: HostId| m != id ==> #[trigger] post.record(m) == pre.record(m),
    ensures
        key_geq(post.record(n), pre.record(n)),
{
    if n == id {
        lemma_merge_key_dominates_local(pre.record(id), incoming);
    } else {
        assert(post.record(n) == pre.record(n));
        assert(key_geq(pre.record(n), pre.record(n)));
    }
}

/// **Hearing an accusation about oneself is two gossip steps.**
///
/// The first merges the accusation; the second merges the refutation, an `Alive`
/// record one incarnation above it. Both are `tr_gossip`, so the model needs no
/// step of its own for a refutation — and the table ends up believing the
/// refutation, which out-ranks the accusation.
pub proof fn theorem_hearing_oneself_accused_is_two_gossip_steps(
    pre: SwimTable,
    post: SwimTable,
    c: Cluster,
    me: HostId,
    incoming: MemberRecord,
)
    requires
        stands_for(pre, c),
        ({
            let merged = merge(pre.record(me), incoming);
            &&& merged != pre.record(me)
            &&& post.record(me) == refutation(merged.incarnation)
            &&& forall|n: HostId| n != me ==> #[trigger] post.record(n) == pre.record(n)
        }),
    ensures
        exists|c1: Cluster, c2: Cluster|
            tr_gossip(c, c1, me, incoming) && tr_gossip(c1, c2, me, refutation(
                merge(record_of(c, me), incoming).incarnation,
            )) && stands_for(post, c2),
{
    let merged = merge(pre.record(me), incoming);
    let c1 = after_gossip(c, me, incoming);
    assert(record_of(c, me) == pre.record(me));
    assert(record_of(c1, me) == merged) by {
        assert(c1.members.contains_key(me));
    }
    let r = refutation(merged.incarnation);
    theorem_a_refutation_outranks_what_it_answers(merged.incarnation, merged);
    let c2 = after_gossip(c1, me, r);
    assert(tr_gossip(c1, c2, me, r));
    assert(merge(record_of(c1, me), r) == r);
    assert forall|n: HostId| #[trigger] post.record(n) == record_of(c2, n) by {
        if n == me {
            assert(c2.members.contains_key(me));
        } else {
            assert(c2.members.contains_key(n) == c1.members.contains_key(n));
            assert(c1.members.contains_key(n) == c.members.contains_key(n));
        }
    }
}

/// **A table is always the view of a reachable cluster.**
///
/// A table built by `new` and changed only by `learn` stands for some state the
/// model can reach. So every theorem about reachable clusters —
/// [`theorem_a_record_key_never_falls_across_a_run`] among them — is a theorem
/// about what the table holds.
pub proof fn theorem_a_table_stands_for_a_reachable_cluster_after_learning(
    pre: SwimTable,
    post: SwimTable,
    c: Cluster,
    id: HostId,
    incoming: MemberRecord,
)
    requires
        swim_reachable(c),
        stands_for(pre, c),
        post.record(id) == merge(pre.record(id), incoming),
        forall|n: HostId| n != id ==> #[trigger] post.record(n) == pre.record(n),
    ensures
        exists|c2: Cluster| swim_reachable(c2) && stands_for(post, c2),
{
    theorem_learn_is_a_gossip_step(pre, post, c, id, incoming);
    let c2 = after_gossip(c, id, incoming);
    let tr = choose|tr: Seq<Cluster>| swim_execution(tr) && tr[tr.len() - 1] == c;
    let tr2 = tr.push(c2);
    assert(swim_execution(tr2)) by {
        assert(tr2.len() > 0);
        assert(swim_init(tr2[0]));
        assert forall|i: int|
            #![trigger tr2[i], tr2[i + 1]]
            0 <= i < tr2.len() - 1 implies swim_next(tr2[i], tr2[i + 1]) by {
            if i < tr.len() - 1 {
                assert(tr2[i] == tr[i]);
                assert(tr2[i + 1] == tr[i + 1]);
            } else {
                assert(tr2[i] == c);
                assert(tr2[i + 1] == c2);
            }
        }
    }
    assert(tr2[tr2.len() - 1] == c2);
    assert(swim_reachable(c2));
}

} // verus!
