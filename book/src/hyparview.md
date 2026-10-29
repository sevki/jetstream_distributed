# HyParView: who to talk to

[SWIM](swim.md) answers *is each member up?* by keeping a record and a verdict on every
member. HyParView answers a different question, *who should I talk to?*, and keeps no
table of the cluster to do it. A node holds two small sets:

- an **active view**, a handful of peers it gossips with. Links in it are meant to be
  two-sided: if `a` is in `b`'s active view, `b` is in `a`'s;
- a **passive view**, a larger reserve of nodes it has heard of and could promote when an
  active peer is lost.

Nothing here judges anyone alive or dead. A peer leaves the active view because a link
closed or a slot was needed, not because it was suspected.

```text
 Join(new) ──► contact adds `new` to its active view
              (demoting one peer to passive if full),
              and walks ForwardJoin(new, ttl) to its other active peers
 ForwardJoin ► at the end of the walk, adds `new` to active and asks it to reciprocate;
              before the end, passes the walk on, noting `new` in passive at ttl = prwl
 Disconnect ──► the peer leaves active and goes to passive
 Neighbor ────► the peer joins active (always granted, here)
```

## What is built

This is the first piece, built the way SWIM was: **one node's views and the four handlers
that maintain them**, with the model, an executable table, and the proof that the table
is the model. What the proofs say is a node's views stay trustworthy under any message,
in any order, any number of times: it is never its own peer, a peer is in one view and
not both, and both views stay within their capacities. The paper leaves "drop a random
peer" to the node; the model leaves it as a choice, so any way of choosing is correct,
and the random choice is the caller's.

## What is not

No shuffle (which refreshes the passive view), no promotion on failure (which refills a
vacated active slot), and nothing about several nodes together: **symmetry of active
views is the paper's central property and is not claimed here**, because the model is one
node. The [Reference](reference/hyparview.md) has the rows and the full list.

## The service half

`hyparview::service::Node` is the table behind a lock, with the random choices drawn
from a seeded generator, and it implements `membership::PeerSampling` (`peers()` is the
active view). It is **transport-free**: `handle(from, message)` returns the messages to
send, so a test or a real transport can sit in front of it. It is the second
implementation of the contract, held to the same checks as SWIM in
`tests/membership_contract.rs`. HyParView passes a verdict on nobody, so it is held to
`PeerSampling` alone and is not a `FailureDetector`; that is what the split is for.

Whether a cluster of these nodes is an overlay is **tested, not proved**:
`tests/hyparview_cluster.rs` runs nodes against a queue and checks that active views end
up symmetric, bounded, and connected on those runs. The model is one node and says
nothing about that, and **symmetry does not hold in general**: a `Neighbor` that overlaps
a `Disconnect` can leave a link one-sided, and a test pins one such interleaving.
Nothing in the crate consumes HyParView yet.

Next: [the mailbox](mailbox.md).
