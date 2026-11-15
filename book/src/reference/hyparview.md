# HyParView: two small views

[HyParView](../hyparview.md) keeps no table of the cluster. A node holds an **active
view** (the peers it gossips with, at most `active_cap`) and a **passive view** (a
reserve of nodes it has heard of, at most `passive_cap`), and nothing else. This page
is what is claimed about the node that holds them, and what is not.

It is **one node**, and it is the first piece, built the way [SWIM](swim.md) was: the
four handlers that build and prune the active view, with the model, the executable
table and the refinement between them. `src/hyparview/model_t.rs` is the model,
`src/hyparview/exec_v.rs` the table, and `src/hyparview/proofs/invariant_v.rs` the
theorems.

## What is proved

| ID | Claim | Theorem | Assumes |
| --- | --- | --- | --- |
| H1 | **Adding to the passive view keeps the views well-formed** and leaves the active view alone. A node never holds itself; a peer already active, already passive or equal to the node is not added; a full view evicts one entry to make room | `hyparview::proofs::invariant::lemma_passive_added_keeps_views_ok` | well-formed views |
| H2 | **Adding to the active view keeps the views well-formed**, makes the peer active (unless it is the node itself or the view has no room at all), takes it out of the passive view (a promotion, not a copy), and when the view is full demotes exactly one active peer, which is no longer active | `hyparview::proofs::invariant::lemma_active_added_keeps_views_ok` | well-formed views |
| H3 | **Every handler keeps the views well-formed**: no node is its own peer in either view, no peer is in both views, and both are within their capacities. For `Join`, `ForwardJoin`, `Disconnect` and `Neighbor`, from any well-formed state, with any choice of the peer to demote, the entry to evict and the next hop, and so on any replay of any message in any order, including a `ForwardJoin` that arrives from a node that is no longer an active peer (the model ignores it: no change, nothing sent) | `hyparview::proofs::invariant::theorem_every_step_keeps_the_views_well_formed`, `lemma_init_is_well_formed` | none beyond a well-formed start |
| H4 | **The executable table is the model.** `HvTable::add_passive` and `add_active` are the model's `passive_added` and `active_added`. Each handler (`join`, `forward_join`, `disconnect`, `neighbor`) returns the messages to send such that, **for any history of earlier messages**, the table's change together with those messages is a step of the model. The choices are arguments, and any value is a correct choice | `hyparview::exec::HvTable::{add_passive, add_active, join, forward_join, disconnect, neighbor}` (their contracts) | the table is well-formed, which every method preserves |
| H5 | **The table keeps its views well-formed**: if the views were well-formed before a handler, they are after, and so by H3 and H4 from an empty table onward | the same handlers' contracts, with H3 | none |
| H6 | **The model is a `Protocol`** whose `next` is the model's `hv_next` | `protocol_agreement::lemma_hyparview_next_agrees` | none |

## What is not claimed

* **Symmetry of active views.** The paper's central property is that if `a` is in
  `b`'s active view then `b` is in `a`'s. That is a property of how *several* nodes are
  connected, and this model is one node. It is not stated here and is not proved.
  The `Neighbor` request that a terminal `ForwardJoin` sends is the mechanism that
  makes links two-sided, and what it sends is proved (H4); that the other end acts on it
  is the network's.
* **Connectivity, or a random sample.** Nothing here says the overlay stays connected,
  or that a node's peers are uniformly random. The picks are arguments, so how random
  they are is the caller's.
* **Shuffle, and promotion on failure.** Not built. Without them a passive view only
  ever receives what forwarded joins and demotions give it, and a vacated active slot is
  not refilled. Promotion is what would use a failure detector's verdict, and nothing
  here has one.
* **`Neighbor` is always granted.** The paper's low-priority request, which an
  active-full node refuses and answers, is part of promotion and so not here.
* **A `ForwardJoin` that ends a walk sends `Neighbor` to the newcomer.** The paper
  leaves the two-sidedness of the link to the connection that carries the walk; the
  model says it as a message so that it has a name and is replay-safe.
* **The network.** `sent` only grows and a message may be delivered any number of
  times, so the handlers are proved safe on replays. Delivery itself, authentication of
  who is speaking, and the lock around a table are the service's, which is plain Rust.
