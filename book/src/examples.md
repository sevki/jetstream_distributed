# Usage examples

Four small programs, each runnable, each asserting what it shows. The code on this page
is **included from the files themselves** when the book is built, so it cannot drift from
what compiles: `cargo test` builds every example, and CI runs them.

```text
cargo run --example ownership_handover
cargo run --example swim_membership
cargo run --example actor_hosting
cargo run --example actor_basic
```

They are ordered the way the book is: the base first, then what sits on it. Each
example is about *using* a piece, so for why it is shaped that way read the chapter
named above it.

## Handing an actor from one node to another

Chapter: [Ownership](ownership.md).

`A` owns an actor at epoch 41 and writes. `A` agrees to hand it to `B`, which burns the
epoch at once, so `A`'s next write at 41 is refused `FENCED`. `B` takes the actor at 42.

Things to notice:

- **No call names the acting node.** Who is calling is the `Context`, which a transport
  fills in. Here it is built by hand (`from`) because there is no network; over a real
  connection nothing else changes.
- **The refusal comes from the registry, not from `A`.** `A` still believes it holds 41.
- **The floor.** `MemoryFloor::at(40)` seeds the durable record of the highest epoch used,
  which is what keeps a restart from rewinding the actor.

```rust,ignore
{{#include ../../src/ownership/examples/handover.rs}}
```

## A node's view of a failure

Chapter: [SWIM](swim.md).

A node suspects a peer because its own probe failed, then declares it dead when the
suspicion times out. A weaker report cannot undo that; a higher incarnation can, which is
how a peer refutes an accusation.

Things to notice:

- **`suspect` and `declare_dead` are methods on the node and not on the wire.** What
  arrives from outside is a batch of `Update`s, merged by `apply`.
- **The incarnation is an argument.** It is the one the node had when the probe began, so a
  refutation that lands mid-probe cannot be accused after the fact.
- **Applying a message twice changes nothing**, which is the property that lets gossip be
  delivered at least once and in any order.

```rust,ignore
{{#include ../../src/swim/examples/membership.rs}}
```

## Hosting an actor under a fence

Chapters: [Services over Jetstream](services.md) and [the actor](actor.md).

A supervisor hosts an ordinary service behind a mailbox. The fence is the question "may
this host still act for its actor?". When it closes, the next request is answered `FENCED`
without reaching the actor. Draining then drops the service and leaves the mailbox
answering.

Things to notice:

- **The actor is a plain trait implementation.** It has no idea it has a mailbox, a fence
  or a supervisor.
- **`spawn` requires a fence.** There is no way to host an actor that cannot be told it
  lost.
- **The caller gets an ordinary generated channel.** It cannot tell a local actor from a
  remote one.
- **In a deployment the fence is the ownership registry's `may_write(host, epoch)`.** That
  wiring is not built; the example uses a flag in its place.

```rust,ignore
{{#include ../../src/actor/examples/hosting.rs}}
```

## Two actors, one calling the other

Chapter: [The mailbox](mailbox.md).

`A` holds a channel to `B` and calls it. `A` is generic over what `B` is, so it cannot
tell a mailbox from anything else that speaks the protocol.

```rust,ignore
{{#include ../../src/actor/examples/basic.rs}}
```

## Longer examples are the tests

The tests are real programs too, and a good deal longer. They are the better reading
once the examples above make sense, because each one is a story with an expected ending:

| To see | Read |
| --- | --- |
| A handover across simulated hosts, with the audit log | `tests/ownership_handover.rs` |
| A restart that must not rewind the actor | `tests/ownership_durability.rs` |
| A split vote that still elects one leader | `tests/raft_election.rs` |
| A suspicion crossing a healed partition and being refuted | `tests/swim_turmoil.rs` |
| An actor changing hosts with nothing lost or repeated | `tests/actor_turmoil.rs` |
| A cooperative drain, including a handler that panics | `tests/actor_drain.rs` |
| The privilege that will not move while the actor is held | `tests/composed_handover.rs` |

They are plain Rust that Verus never sees. What they check is tested, not proved; see
[Evidence](evidence.md).
