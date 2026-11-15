# The Raymond layer

`src/raymond/model_t.rs` models Raymond's distributed mutual-exclusion algorithm as a
**routing** layer, kept strictly separate from ownership semantics. Per node it
tracks a `holder` pointer (that node's **belief** about the next hop towards the
privilege), a request `queue`, an `asked` flag (outstanding request) and `using`
(inside the critical section). Alongside them, and deliberately *not* derived
from them, is `Raymond::privilege`: the node that **actually** holds it.

That split is the routing counterpart of `issued` versus `token_authorized` in
the ownership layer, and it is what lets a seizure take the privilege from a
node without reaching into it. `believes_holds(r, n)` is belief, `has_token(r, n)`
is authority, and `is_stale_holder(r, n)` is the gap — see
[Seizure needs no oracle](ownership.md#seizure-needs-no-oracle-belief-versus-authority).

Requests in flight are explicit state: `Raymond::requests` records every request
ever sent as `(originator, destination)`, never shrinks, and is not consumed by
delivery — the same modelling choice the ownership layer makes for `network`. The
destination is resolved at *send* time, which is what lets a request be delivered
after the token has moved and the holder pointers it was routed against are gone.
A guard phrased against the live `holder[from]` would instead drop such a request
silently, so "arbitrary delay" would have been claimed but not modelled.

Requests travel hop-by-hop towards the token and the token travels back along
the reverse of the request path:

```text
request:  D -> B -> A -> C[token]
token:    C -> A -> B -> D
```

Routing and ownership are glued by one predicate. It is about both layers, so it is
defined with the composed machine (`composed::model::couples`), and the Raymond
layer imports nothing of ownership; the theorems that use it on its own are in
`composed::proofs::couples`:

```rust
spec fn couples(r: Raymond, s: OwnershipState) -> bool {
    forall|n: Id, e: Epoch| may_mutate(s, n, e) ==> has_token(r, n)
}
```

Note the direction: routing never *grants* authority, it only constrains who
could possibly have it. Authority still comes exclusively from the ownership
state and its epoch. That is why a routing step - including a duplicated or
reordered request - cannot manufacture an owner: it does not touch `holder` at
all, so it cannot even change *who could* be the owner.

On its own, though, `couples` is only a predicate: `ray_assign_privilege` never
sees the ownership state, so nothing in the routing layer stops a token from
moving out from under a node that still has authority. `src/composed/model_t.rs` closes
that gap by defining a single state machine over both layers in which the
synchronisation is a **guard**:

* `PassToken` may only fire while the actor is `Unowned` — ownership must be
  genuinely released before the token is allowed to move. (`Transferring` also
  satisfies `!is_owned`, so guarding on that weaker condition would let the token
  move while a handover was still in flight and the outgoing owner had not yet
  acknowledged the revoke.);
* `AcquireUnderToken` may only fire for a node that *holds* the token — authority
  cannot be taken by a node routing has not elected;
* `Ray` carries every Raymond step that does *not* move the token — request
  routing and critical-section entry/exit alike — and `Own` carries every
  ownership transition that does not create authority over the actor.

The `Ray` carrier is guarded on `preserves_token`, deliberately wider than
`is_routing_step`: if it admitted only routing, no composed execution could ever
enter a critical section, every composed-reachable state would keep `using`
uniformly false, and the theorems below would cover only a degenerate fragment
of the real behaviour. `scenario_composed_critical_section` rules that out the
only way that really counts — by building an execution from `composed_init` that
*reaches* a state with `using` set, rather than assuming the entry transition and
checking it type-checks as a composed step.

`couples` is then an invariant of that machine rather than a side condition,
which is what makes "token transfer preserves ownership safety" a claim about
the system instead of a hypothetical.

Every composed theorem is of the form "every *reachable* composed state
satisfies ...", and such statements are worthless if nothing interesting is
reachable. Two executions close that off, both built from `composed_init` via
`lemma_composed_reachable_step`:

* `scenario_composed_handover` — a complete handover driven through both layers
  at once, ending in a reachable state where `B` genuinely owns the actor at
  epoch 42 *and* holds the token, while `A`'s epoch-41 token is still issued and
  powerless;
* `scenario_composed_critical_section` — a reachable state in which a node is
  actually inside the critical section.

Raymond's **liveness** (every request is eventually served) needs FIFO,
reliable links and no crashes. None of those are assumed here and none of it is
claimed.
