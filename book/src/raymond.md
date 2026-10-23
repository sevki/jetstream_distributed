# Raymond: routing the privilege

Raymond's algorithm is a distributed mutual-exclusion scheme. Here it is modelled as
a **routing** layer, kept strictly separate from ownership semantics: it answers
"which way is the privilege?", never "who may mutate?".

## What each node keeps

Per node: a `holder` pointer, a request `queue`, an `asked` flag and a `using` flag.
Alongside them, deliberately *not* derived from them, is `privilege`: the node that
**actually** holds it.

```text
request:  D -> B -> A -> C[token]
token:    C -> A -> B -> D
```

Requests travel hop by hop towards the token, and the token travels back along the
reverse path.

## Belief versus authority

The split between `holder` and `privilege` is the routing counterpart of the issued
tokens versus the current state in [ownership](ownership.md):

| | meaning |
| --- | --- |
| `believes_holds(r, n)` | node `n` thinks it holds the privilege (belief) |
| `has_token(r, n)` | node `n` actually holds it (authority) |
| `is_stale_holder(r, n)` | the gap between the two |

The split exists so that a seizure can take the privilege from a node **without
reaching into it**. No implementation can edit the state of a node that is down, and
an earlier version of the model assumed exactly that. After a seizure both
`holder[A] == A` and `holder[B] == B`, and that is deliberate: `A` is a stale holder
whose belief nobody could correct. Uniqueness belongs to `privilege`, not to the
belief graph.

So the unconditional guarantee is an **acyclic forest of beliefs plus one
authoritative holder**. Following the pointers to that holder needs one more
condition, `ray_no_stale_holders`, which is what reconciliation restores.

## Requests are state

Requests in flight are explicit state: every request ever sent, as an
`(originator, destination)` pair. The set only grows and delivery does not consume it,
the same choice the ownership layer makes for its network. The destination is resolved
at *send* time, so a request can be delivered after the token has moved. A guard
phrased against the live pointer would drop it silently, and "arbitrary delay" would
have been claimed but not modelled.

## How it is tied to ownership

One predicate:

```text
couples(r, s) = every node that may mutate in s holds the privilege in r
```

Routing never grants authority; it only constrains who could have it. That is why a
routing step, including a duplicated or reordered request, cannot manufacture an
owner: it does not change who could be the owner.

On its own `couples` is only a predicate. Nothing in the routing layer sees the
ownership state, so nothing stops the token moving out from under a node that still
has authority. [Composed](composed.md) closes that gap.

## What is and is not claimed

- Claimed: at most one privilege holder, routing cannot manufacture ownership,
  duplicated, reordered and arbitrarily delayed requests are safe, and the executable
  routing steps agree with the model in both directions.
- **Not claimed: liveness.** "Every request is eventually served" needs FIFO, reliable
  links and no crashes, and none of those are assumed.
- **No crash model of its own.** The ownership layer models crash, recovery and unreliable
  detection; Raymond's steps do not. What is modelled is the case that matters for the
  composed claim, a seizure that re-establishes the token without the holder acting.
- **The service hosts the whole record in one process.** The router holds every node's
  entries under one lock because the model's `Raymond` is one struct. It checks the
  rules; it does not distribute them. A deployment where each node keeps only its own
  entries is a different system, and nothing here says this one refines it.

The routing claims are the R-rows in the README's
[Raymond section](https://github.com/sevki/jetstream_distributed/blob/main/README.md#the-raymond-layer),
including [seizure without an oracle](https://github.com/sevki/jetstream_distributed/blob/main/README.md#seizure-needs-no-oracle-belief-versus-authority).

Next: [Composed](composed.md).
