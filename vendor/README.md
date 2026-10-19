# `vendor/verified-storage`, vendored

(The KVerus agent skills, also vendored, are described in
[`kverus/README.md`](kverus/README.md).)

Microsoft's [verified-storage](https://github.com/microsoft/verified-storage)
repository, whole and verbatim, at commit
`41cab95051229ebd457b4eed7fc111e3e7c9099c` (*"Fix nightly-verita, update to
version 2026-09-20"*). MIT licensed; `verified-storage/LICENSE.txt` is upstream's,
unaltered.

| | |
|---|---|
| `pmemlog` | A verified append-only log on persistent memory. Crash consistent, and it detects bit corruption in its metadata. **The one crate CI verifies.** |
| `multilog` (`multilog`, `pmsafe`) | A collection of logs, each in its own region, with **atomic appends across the logs** |
| `capybaraKV` (`capybarakv`, `pmcopy`) | A persistent-memory key-value store |
| `capybaraNS` | A notary service, written in Dafny |
| `soundness_proofs` | Formalised soundness arguments for the PoWER approach to crash consistency |
| `unverified` | Mocks and tests |

## Why this is here and not a `git` dependency

Because it has to be *verified*, not merely compiled. `cargo verus verify` only
checks crates that opt in with `[package.metadata.verus] verify = true`, and a
dependency fetched from a git URL is checked against whatever that URL says
today. Vendoring puts the source in the diff, so a change to the storage layer's
proofs is a change to this repository that CI checks — which is the same reason
`Cargo.lock` is committed and `turmoil` is pinned exactly.

It is vendored **whole** rather than module by module because a partial copy is
a fork: it has to be argued about, and every later addition widens the argument.
A verbatim tree has one claim — *it is upstream at that commit* — and CI checks
exactly that, with `diff -r` against a fresh checkout (the job "The vendored
source is unmodified").

It is kept out of `src/` because it is somebody else's code under somebody
else's licence. The one-crate rule is about *this* repository's protocols;
keeping a vendored dependency textually separate is what makes the boundary
between what we prove and what we inherit legible.

## What is built and verified

Only `pmemlog` is a workspace member, and only `pmemlog` has a CI job
(`pmemlog proof check`). The rest of the tree is present and unmodified but its
crates are listed under `exclude` in the root `Cargo.toml`:

* `multilog` and `capybarakv` each have a `build.rs` that runs `bindgen`, which
  needs libclang and PMDK headers, and a `pmem` feature that is on by default.
  They have no CI job yet.
* `pmsafe` and `pmcopy` are proc-macro crates only those two use.
* `unverified/*` are mocks and tests, not proofs.

Bringing one in is a change to the root `Cargo.toml`, a CI job like
`pmemlog proof check`, and a line here. Nothing in `src/` depends on any of it
yet.

## Toolchains

Upstream pins a toolchain in each crate directory (`pmemlog/rust-toolchain.toml`
says `1.97.1`; `multilog` and `capybaraKV` say a nightly). **They are stale or
inapplicable here and are not what runs.** `rustup` reads the nearest
`rust-toolchain.toml` to the *current directory*, so from the repository root
the root's pin applies — the release the pinned Verus (`0.2026.09.20.aef82ed`,
via `vstd = "=0.0.0-2026-09-20-0158"`) was built against, `1.98.1`. Running
`cargo` from inside `vendor/verified-storage/pmemlog` would pick upstream's pin
instead; do not.

`pmemlog/src/main.rs` is upstream's demo binary. It re-declares every module and
imports them again through the crate name, so it is a second compile of the
same code rather than evidence about anything. It is part of the vendored tree
because the tree is verbatim, and it is a target of the `pmemlog` package.

## The escape hatches, and why CI allows them here

The root `verify` workflow rejects `assume`, `admit`, `axiom`, `external_body`
and friends anywhere under `src/`. That check deliberately does **not** cover
`vendor/`, and this is the documented exception it was written to leave room
for.

`pmemlog` has six, and every one of them is a boundary of the system model
rather than a proof obligation discharged by fiat:

1. `pmemspec_t::bytes_crc` — computing a CRC by calling `crc64fast`. The spec
   function `spec_crc_bytes` is uninterpreted; the exec function is what
   connects it to a real library.
2. `pmemspec_t::axiom_bytes_uncorrupted` — **an assumption about hardware**: if
   `y` is the CRC of `x` and a read gives back `x_c`, `y_c` with `y_c` the CRC
   of `x_c`, then `x_c == x`. This is the statement that a CRC detects the
   corruptions the device actually produces. It cannot be proved; it is the
   premise that makes checksumming worth doing.
3. `pmemspec_t::axiom_corruption_detecting_boolean` — the same assumption for
   the two-valued flag, with `cdb0_val`/`cdb1_val` set to CRC(b"0") and
   CRC(b"1") so that corruption is assumed unable to turn one into the other.
4–6. `pmemmock_t`'s `new`, `read`, `write` — the volatile stand-in for the
   device. These are the I/O primitives themselves; there is nothing beneath
   them to verify against.

Assumptions 2 and 3 are exactly what the repository rule calls *"an explicit
documented part of the system model"*. Anything this repository proves on top of
`pmemlog` is conditional on them, and the root `README.md` says so where it
states what is proved.

`multilog` and `capybarakv` have their own, and they are **not** enumerated
here because nothing is built on them yet. Do that before depending on either.

## The crash model: 8-byte chunks, not byte atomicity

Worth stating on its own, because it is easy to assume something stronger.

`pmemspec_t::persistence_chunk_size` is **8**, and
`WriteRestrictedPersistentMemory::write` may only be called when the permission
holds for *every* subset of 8-byte chunks having been flushed. A crash part-way
through a write can leave an arbitrary mixture of old and new chunks.

So pmemlog's `append` is **not** atomic in bytes. It is atomic in the *abstract
log* — a crash shows the log before the append or the log after it — and it
earns that with the CRC and the corruption-detecting boolean: a partially
flushed append fails the check, so `recover` reads the state before it. The
permission machinery is what forces this for every reachable crash state rather
than the convenient ones.

Two consequences for anything built on top:

* **The abstract atomicity is exactly as strong as the two assumptions above.**
  It is proved, not assumed — but proved *from* them.
* **A device written directly, bypassing pmemlog, needs a checksum per record
  — alignment is not enough.** Worth spelling out, because "8-byte chunks"
  invites the wrong fix. A write spanning `n` chunks has `2^n` partial outcomes,
  so *no* record wider than eight bytes is atomic under this model however it is
  aligned: padding this repository's seventeen-byte records to twenty-four
  would touch three whole chunks instead of three partial ones and buy nothing,
  since chunks 0 and 2 can land while chunk 1 does not.

  A record wider than a chunk is detectable-or-not, never atomic. The only
  mechanisms are a checksum over the record, or an outer log that already has
  one. This repository's records take the second, which is why they carry no
  checksum of their own and why **the format is only sound inside pmemlog's
  log** — a real constraint on it, not an omission.

* **A file-backed `PersistentMemory` has to supply the 8-byte chunk model**, and
  POSIX does not promise it for a write that crosses a chunk. That is the first
  thing to get right when one is written, and the reason a naive
  `pwrite` + `fsync` implementation would not be enough.

## What it does and does not give us

`AbstractInfiniteLogState` has `append` and `advance_head`. It has no
**truncate**: the tail cannot be cut back. Raft needs exactly that — figure 2's
rule 3 deletes a conflicting entry and everything after it — so the log this
repository builds on top of `pmemlog` records a truncation as an *appended*
record and rebuilds the index on recovery, rather than moving bytes. The
physical log stays append-only, which is what the verified layer below can
support, and the logical log truncates.

`multilog` adds one thing `pmemlog` lacks: an append that lands atomically
across several logs. That is what a journal and the record that fences it would
want, and it is the reason the rest of the tree is here.
