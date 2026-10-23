# Introduction

`jetstream_distributed` is a set of distributed protocols written in
[Verus](https://github.com/verus-lang/verus), plus the
[Jetstream](https://github.com/sevki/jetstream) services that speak them. The
protocols are **exclusive mutable ownership** of an actor across machines,
Raymond's routing layer, Raft, SWIM gossip membership, and a distributed actor with
a mailbox in front of it.

```text
Rust:
    at most one mutable reference

Distributed ownership:
    at most one authoritative mutable owner
```

This is not Rust's borrow checker extended across a network. It is a runtime
protocol, and the proofs are about a *model* of it. The
[README](https://github.com/sevki/jetstream_distributed/blob/main/README.md) says
exactly what is claimed and what is not.

## What this book is for

The README is the map of claims: every theorem, with the name of the proof and what
it assumes. It is long, because each algorithm is described in detail. This book
answers a different question: **how do the algorithms relate to each other?**
Which one assumes what the others provide, which two are glued together and how,
which are independent, and where a relationship is intended but not built yet.

It does not repeat the claims tables. Where a chapter makes a claim it gives the
README's row number (`A14`, `MB10`, `C54`) and links to the table, so the
statement of what is proved lives in one place.

## How to read it

Start with [How the algorithms relate](how-they-relate.md). It is one page, and
every later chapter is a closer look at one box in its picture. Then read
[Evidence](evidence.md) before trusting any sentence in this book that contains
the word "guarantee": it explains the three tiers (proved, tested, assumed) and
the file naming that tells them apart.

The protocol chapters are in the order the dependencies run, so each one can lean
on the ones before it:

1. [Ownership](ownership.md), the base everything else uses or assumes.
2. [Raymond](raymond.md) and [Composed](composed.md), which route the privilege
   and tie the routing to ownership.
3. [Raft](raft.md), which is how the base's strongest assumption could be bought.
4. [SWIM](swim.md), which agrees on nothing and promises only that views converge.
5. [The actor](actor.md) and [the mailbox](mailbox.md), which sit on ownership.

The last three chapters are about running these: the services, placement and
discovery, and the actor system over QUIC.

## What this book will not do

It will not say a thing is proved when it is only tested. Where the code and the
README disagree, the code wins and the README is the thing to fix. Where a chapter
describes a design that is not built, it says "not built" in the same sentence.
