# jetstream_distributed

Machine-checked distributed protocols, written in
[Verus](https://github.com/verus-lang/verus), and the
[Jetstream](https://github.com/sevki/jetstream) services that speak them: **exclusive
mutable ownership across machines**, Raymond's routing layer, Raft, SWIM gossip, and a
distributed actor with a mailbox in front of it.

```text
Rust:
    at most one mutable reference

Distributed ownership:
    at most one authoritative mutable owner
```

This is not Rust's borrow checker extended across a network. It is a **runtime
protocol**, with machine-checked proofs about a *model* of it: exclusivity and fencing
hold in every reachable state, including under crashes, partitions, duplicated messages
and interrupted handovers. What the proofs cover, and what is only tested or assumed,
is stated in the book.

## Read the book

**[sevki.github.io/jetstream_distributed](https://sevki.github.io/jetstream_distributed/)**
is the documentation. The same pages are in this repository under
[`book/src/`](book/src/introduction.md), starting at the
[introduction](book/src/introduction.md), and render on GitHub.

| If you want | Read |
| --- | --- |
| How the algorithms relate, and which relationships are built | [How the algorithms relate](book/src/how-they-relate.md) |
| What "proved", "tested" and "assumed" mean here | [Evidence](book/src/evidence.md) |
| One protocol in depth | [Ownership](book/src/ownership.md), [Raymond](book/src/raymond.md), [Composed](book/src/composed.md), [Raft](book/src/raft.md), [SWIM](book/src/swim.md), [the actor](book/src/actor.md), [the mailbox](book/src/mailbox.md) |
| To run something | [Usage examples](book/src/examples.md) |
| Every theorem, and what it assumes | [Reference](book/src/reference/ownership.md), with the [status](book/src/reference/status.md) of what is proven, modelled and not modelled |
| How the code is laid out | [Repository layout](book/src/reference/layout.md) |

## Build, test, verify

```bash
cargo build --tests --examples          # the services are on by default
cargo test                              # services, simulated-network tests, unit tests
cargo run --example ownership_handover  # the shortest account of the protocol
verus --crate-type=lib src/lib.rs       # the proofs (needs the pinned Verus)
mdbook build book                       # the book
```

[Verifying locally](book/src/reference/verifying.md) has the full commands, including the
pinned Verus release and the toolchain it needs. If Verus is not installed, CI is the
check. [`AGENTS.md`](AGENTS.md) has the rules the repository holds itself to and how to
review a change.
