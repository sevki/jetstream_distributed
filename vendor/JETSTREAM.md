# `vendor/jetstream`, copied

A copy of the working tree at `~/src/dtsource/vendor/jetstream` (upstream
[sevki/jetstream](https://github.com/sevki/jetstream)). **It is not a clean upstream
checkout and does not match any published commit.** Do not read "vendored" here the
way `vendor/verified-storage` and `vendor/kverus` mean it: those are verbatim at a
pinned commit and CI diffs them. This is not, and CI does not check it.

## What it is

* **Base:** `98ee504ba` (*"Merge pull request #733 from sevki/chore/fuzz-pr-checks"*,
  `git describe`: `v16.3-12-g98ee504ba`), crate version `16.3.1`.
* **Plus local changes on top:** 30 tracked files modified (+1067 / −179) and 18
  untracked files, at the time of the copy. The tracked changes are saved as
  [`jetstream-local-changes.patch`](jetstream-local-changes.patch) (`git diff` against
  the base), so they can be told apart from upstream. They touch every component's
  manifest as well as sources in `jetstream_rpc` (including `context.rs`),
  `jetstream_wireformat` and the facade `src/`. I have not reviewed them.
* **Untracked files** (not in the patch):
  `components/*/README.md` for 9p, codegen, error, http, iroh, libc, macros, quic, rpc,
  ufs and wireformat; `jetstream_http/BUILD.bazel`, `jetstream_quic/BUILD.bazel`;
  `jetstream_rpc/src/context/tests.rs`; `jetstream_wireformat/src/usize_tests.rs`;
  and the `jetstream_wasm` component (`BUILD.bazel`, `Cargo.toml`, `src/lib.rs`).

## What was left out

`.git`, `.direnv` and `.claude` (version control and local environment). Build
output (`pkg/`, `components/jetstream_wasm/pkg/`) is copied but ignored by the
tree's own `.gitignore`, so it will not be committed.

## It has been edited since the copy

The copy in this repository is no longer the same as the source directory. The
`Peer::Actor(String)` variant (and the code and tests that named it) was removed
here, and `rustfmt` was run over some of it, so [`jetstream-local-changes.patch`](jetstream-local-changes.patch)
— a `git diff` of the *source* against its base, taken at the copy — no longer
describes this tree. Regenerate it, or replace it, once the edits settle.

## How it is used

The root `Cargo.toml` asks crates.io for `jetstream = "16.0.0"` and
`jetstream_rpc = "16.0.0"` (the latter as a dev-dependency with the `turmoil`
feature), and a `[patch.crates-io]` table builds `jetstream`, `jetstream_rpc`,
`jetstream_wireformat`, `jetstream_error` and `jetstream_macros` from this directory
instead. The facade reaches its components by path, so every `jetstream_*` crate in
the graph is the same copy; a registry copy of any of them next to these would be a
second `Context`.

* **`fuzz/` has its own table.** A patch applies only at the root of the workspace
  it is in, and `fuzz/` is its own workspace, so its `Cargo.toml` repeats the patch.
  Without it, it resolves crates.io's `16.0.0`, which has no `session` module.
* **It only applies while the versions agree.** The requirement `^16.0.0` accepts this
  copy's `16.3.1`. A copy at `17.x`, or a requirement above `16.3.1`, silently stops
  patching ("patch … was not used in the crate graph" is the warning to watch for),
  and the lockfile has to be updated for a patch change to take effect.
* **It is not a member of this workspace.** It has its own `[workspace]`; build it
  from its own directory if at all. Its own warnings (an unused import in
  `jetstream_rpc`'s `any_server.rs`, for one) are upstream's, not ours.

## Before relying on it

Decide what it is for. If it should track upstream, replace this copy with a clean
checkout at a published commit and pin it as the other two are. If it carries local
work upstream does not have, that work should be upstreamed or the patch kept
reviewed, because as it stands nothing says which half of a behaviour is upstream's.
