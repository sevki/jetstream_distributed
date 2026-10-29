# Verifying locally

```bash
# 1. Install the Rust toolchain that the pinned Verus release was built against
rustup toolchain install 1.98.1-x86_64-unknown-linux-gnu \
  --component rustc-dev,llvm-tools,rust-std,cargo,rustfmt

# 2. Download the pinned Verus release
VERUS=0.2026.09.20.aef82ed
curl -fL -o verus.zip \
  "https://github.com/verus-lang/verus/releases/download/release%2F${VERUS}/verus-${VERUS}-x86-linux.zip"
unzip -q verus.zip && export PATH="$PWD/verus-x86-linux:$PATH"

# 3. Verify
verus --crate-type=lib src/lib.rs
```

CI (`.github/workflows/verify.yml`) runs exactly this on every push and pull
request, so a PR fails if any proof stops verifying.

A second job runs the same crate through `cargo verus verify`, which checks it
against the `vstd` version pinned in `Cargo.toml` rather than the prebuilt one
inside the Verus release. That entry point needs

```toml
[package.metadata.verus]
verify = true
```

in `Cargo.toml`: without it, `cargo verus verify` compiles this crate with
ordinary rustc, verifies only `vstd`, prints *vstd's* `verification results`
line and exits 0. It is a false green that survives a naive grep for the
summary, because a summary is present — just not this crate's. The CI step
therefore requires a summary emitted *after* Cargo starts compiling this
crate. It runs with `--no-default-features`, since `service` is a default feature
and the proof build should not pull Jetstream and tokio in.

A third job, `pmemlog proof check`, verifies the vendored persistent-memory log
(`vendor/verified-storage/pmemlog`) the same way, and checks that the vendored tree is
byte-for-byte Microsoft's at the pinned commit. See [`vendor/README.md`](https://github.com/sevki/jetstream_distributed/blob/main/vendor/README.md).

A fourth job, `Module layering`, needs no toolchain at all:

```bash
python3 -I .github/scripts/check-modules.py
```

It reads the `crate::...` imports and fails on a **cycle** between modules, or when a
**standalone** module (`ownership`, `raft`, `raymond`, `swim`) depends on anything but `id` and the
modules that only describe shapes (`protocol`, `temporal`, `compose`, `membership`). A cycle compiles, so nothing else would notice one: three went unnoticed
until it was looked for. The check asserts that a few edges it knows are true are found,
so a pattern that stops matching fails loudly and does not report "no cycle". Making a
standalone module depend on something is a decision, and it is made by editing the
`STANDALONE` set in that script in the same change.

The services and the simulated-network tests are not verified, only run:

```bash
cargo test                          # the services, tests/, and the unit tests
cargo run --example actor_basic     # two actors behind mailboxes
```
