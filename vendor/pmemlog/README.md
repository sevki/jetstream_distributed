# `pmemlog`, vendored

A verified append-only log on persistent memory, taken from Microsoft's
[verified-storage](https://github.com/microsoft/verified-storage) at commit
`41cab95051229ebd457b4eed7fc111e3e7c9099c` (*"Fix nightly-verita, update to
version 2026-09-20"*). MIT licensed; `LICENSE.txt` is upstream's, unaltered.

## Why this is here and not a `git` dependency

Because it has to be *verified*, not merely compiled. `cargo verus verify` only
checks crates that opt in with `[package.metadata.verus] verify = true`, and a
dependency fetched from a git URL is checked against whatever that URL says
today. Vendoring puts the source in the diff, so a change to the storage layer's
proofs is a change to this repository that CI checks — which is the same reason
`Cargo.lock` is committed and `turmoil` is pinned exactly.

It is a separate crate rather than a `src/{algorithm}` module because it is
somebody else's code under somebody else's licence. The one-crate rule is about
*this* repository's protocols; keeping a vendored dependency textually separate
is what makes the boundary between what we prove and what we inherit legible.

## What was taken

`src/lib.rs` and the seven modules it declares. Upstream's suffixes are its
own convention and are kept:

| | |
|---|---|
| `_t` | **trusted.** Read this to decide whether to believe the result: `pmemspec_t` (the persistent-memory model and its two corruption axioms), `infinitelog_t` (the abstract log), `main_t` (the public API and its specifications). |
| `_v` | **verified.** `logimpl_v` (2 278 lines of implementation and proof), `math_v`. |
| neither | `sccf` (the crash-consistency permission trait), `pmemmock_t` (a volatile stand-in for the device, used by tests). |

## What was changed

Two omissions, no edits:

* **`src/main.rs` is not here.** It is a demo binary that re-declares every
  module and then imports them again through the crate name. A vendored
  dependency should be a library; the demo is not evidence about anything.
* **`rust-toolchain.toml` is not here.** Upstream's pins `1.97.1`, which is
  stale — the Verus release its own `Cargo.toml` targets
  (`0.2026.09.20.aef82ed`, via `vstd = "=0.0.0-2026-09-20-0158"`) was built
  against `1.98.1`. The workspace root's pin is the one that applies, and it is
  the right one.

No source file was edited. If one ever is, this section says so with a diff,
because a vendored proof that has been quietly patched is worth less than no
proof at all.

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

## What it does and does not give us

`AbstractInfiniteLogState` has `append` and `advance_head`. It has no
**truncate**: the tail cannot be cut back. Raft needs exactly that — figure 2's
rule 3 deletes a conflicting entry and everything after it — so the log this
repository builds on top of `pmemlog` records a truncation as an *appended*
record and rebuilds the index on recovery, rather than moving bytes. The
physical log stays append-only, which is what the verified layer below can
support, and the logical log truncates.
