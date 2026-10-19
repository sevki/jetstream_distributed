# jetstream_distributed

Machine-checked distributed protocols in [Verus](https://github.com/verus-lang/verus)
(ownership, Raymond, Raft, SWIM, a distributed actor and its mailbox) and the
Jetstream services that speak them. `README.md` is the map: what is claimed, what
is proved, and what is not.

## Build, test, verify

```bash
cargo build --tests --examples          # the services are on by default
cargo test                              # services, simulated-network tests, unit tests
cargo clippy --all-targets              # must be clean
cargo doc --no-deps --lib --examples    # must be clean
verus --crate-type=lib src/lib.rs       # the proofs (needs the pinned Verus)
cargo verus verify --no-default-features
```

Verus is pinned (`0.2026.09.20.aef82ed`, with `rust-toolchain.toml` and
`vstd = "=0.0.0-2026-09-20-0158"`). If it is not installed, CI is the check:
`.github/workflows/verify.yml` runs both verification entry points and says what
each guards against. Say so in a review rather than claiming a proof was checked.

Code in `verus!` blocks is shared by two builds, a plain `rustc` one and the Verus
one, so an edit that is fine for one can break the other. File names follow the
vendored verified-storage convention: a `_t.rs` file is **trusted** (the models and
specifications a reader audits, `model_t.rs`, `spec_t.rs`, `fencing_t.rs`,
`temporal_t.rs`) and a `_v.rs` file is **verified** (`steps_v.rs`, `exec_v.rs`,
`registry_v.rs`, `store_v.rs`, `wire_v.rs`, `transfer_v.rs` and everything under
`proofs/`). The module keeps its plain name through `#[path]`, so only the file
name carries the suffix. `src/**/steps_v.rs`, `exec_v.rs`, `registry_v.rs`,
`store_v.rs` and `wire_v.rs` are verified executable code; `service` code
(behind the `service` feature) is plain Rust that Verus never sees.

## Rules the repository holds itself to

* **No escape hatches in `src/`.** `assume`, `admit`, `axiom`, `external_body` and
  friends are rejected by CI. The one documented exception is the vendored
  `pmemlog` (`vendor/README.md`).
* **Nothing vendored is edited.** `vendor/verified-storage` and `vendor/kverus` are
  verbatim copies of upstream at a pinned commit, and CI diffs them. To change one,
  re-vendor from upstream and update the pin in the workflow and in the README that
  describes it (`vendor/README.md`, `vendor/kverus/README.md`).
* **Say what is proved and what is merely tested.** `service::Mailbox` is a
  transcription of the mailbox model, not a refinement; docs must not blur that.
* Add dependencies with `cargo add`, not by editing `Cargo.toml`.

## Reviews

The Verus-specific parts of a review use the vendored KVerus skills in
`vendor/kverus/skills/` (provenance and licence: `vendor/kverus/README.md`). Each
skill is a `SKILL.md` to read and follow; they also install as ordinary agent skills
(`vendor/kverus/skills/` is the directory to point an agent at). A review reads the
diff and **does not change code**: use the review and eval skills, not `kverus-fix`,
`kverus-migrate`, `kverus-spec`, `kverus-strip` or `kverus-run`, which edit.
The same instructions are packaged as a custom agent in
`.github/agents/verus-specialist.agent.md`, which also covers repairing proofs.

### Changes to code inside `verus!` (models, specs, proofs, `steps_v.rs`)

1. Run `kverus-review` on the change:

   ```text
   $kverus-review verify="verus --crate-type=lib src/lib.rs"
   $kverus-review commit=<base> verify="verus --crate-type=lib src/lib.rs"
   ```

   Use that command and **not** CI's, which adds `--triggers-mode silent`: the skill
   looks for Verus's "automatically chose triggers" note, and silent mode hides it.
   It reports four things:

   * **exec-code changes**, classified `semantic-change`, `likely-equivalent` or
     `uncertain`. A `semantic-change` in a `steps_v.rs` is a change to what the
     services run, so it needs a matching change in `proofs/refinement_v.rs` or an
     explanation of why not;
   * **new `=~=`** that `==` would do;
   * **deleted comments** — here these are design rationale, not migration
     provenance;
   * **verification status** and the trigger and `Set::finite` / `new_assuming_finite`
     warnings.

   This repository is not a Rust-to-Verus migration, so ignore the skill's
   `Origin Rust:` preservation-comment column unless the change really does move
   existing Rust into `verus!`.

2. If the change touches a `requires`, `ensures`, invariant or a `spec fn` that a
   theorem depends on, run `kverus-eval` on it. A score below 7/10, or any weakened
   clause, needs a reason in the PR. Weakening a specification so a proof goes through
   is the failure it exists to catch.

3. Check the claims table. A new or changed theorem should appear in `README.md`
   with its name, what it assumes and what it does not say; a theorem that was
   weakened should not still be described as it was.

4. Run CI's escape-hatch grep over the diff by eye: no `assume`, `admit`, `axiom`,
   `external_body`, `external`, or `#[verifier::...]` that skips a check.

### Changes to `service` code and tests (plain Rust)

The KVerus skills do not apply. Review for:

* clippy and `cargo doc` clean, tests run, and tests that would **fail** without
  the change (a test that cannot fail does not guard anything);
* the service calling the verified step functions rather than re-deriving them;
* identity coming from the connection, never from an argument naming the acting node;
* locks: a decision that reads the registry then writes the journal holds one gate
  across both;
* a claim in a doc comment that code does not back, especially "refines",
  "guarantees" and "proved". Cross-check it against `README.md`.

### Changes under `vendor/`

Diff against upstream at the pinned commit; nothing else is acceptable. Anything
that depends on a vendored assumption should say which one (`vendor/README.md`
lists `pmemlog`'s six).

### What a review reports

Findings first, ordered by severity, each with file and line. Then what was run and
what was not (say "Verus was not available" if so), and the verification result of
the command above. Do not report a skill's category as clean unless it was
actually run.
