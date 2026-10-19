# `vendor/kverus`, vendored

The `skills/` directory of [asterinas/KVerus](https://github.com/asterinas/KVerus),
verbatim, at commit `55fb0185e42957ac5f1f6e16c8beb9e2093a3a2e` (*"skills(kverus-strip):
add whole-run rlimit guard and outcome logging (#14)"*), with upstream's `LICENSE`
(MIT, copyright Liu et al.) beside it, unaltered.

These are agent skills for working on Verus code: each directory has a `SKILL.md`
that an agent reads and follows, with scripts and reference material alongside.
Only the skills are taken, not the rest of the KVerus repository (its docs, its
installer, its Python package).

| skill | what it does | edits code? |
|---|---|---|
| `kverus-review` | Reviews a diff for exec-code changes, new `=~=`, deleted comments and verification warnings | no |
| `kverus-eval` | Scores a specification change on whether it weakens or strengthens the spec | no |
| `kverus-semantic-audit` | Compares original Rust with migrated Verus for changed runtime behaviour | no |
| `kverus-common` | Shared Verus syntax and proof-pattern references the others read | no |
| `kverus-common-sync` | Checks `kverus-common` against a Verus checkout | no |
| `kverus-fix`, `kverus-spec`, `kverus-migrate`, `kverus-strip`, `kverus-postprocess`, `kverus-run` | Repair, specify, migrate, simplify and orchestrate | **yes** |

How this repository uses them for reviews is in [`AGENTS.md`](../../AGENTS.md).

## Why it is here and not installed

A review that depends on skills each reviewer happened to install is a review that
varies with the reviewer. Vendoring pins the version, puts any change to it in the
diff, and keeps the instructions in `AGENTS.md` and the skills they name from
drifting apart. It follows the same rule as `vendor/verified-storage`: **verbatim,
at a pinned commit, and CI diffs it** (the job "KVerus skills are unmodified").

## What is not carried over

* The skills' `agents/openai.yaml` files are included because they are in
  `skills/`; nothing here reads them.
* `kverus-postprocess` and `kverus-semantic-audit` run Python scripts. They are
  not run by CI and nothing here depends on them.
* These skills were written for Rust-to-Verus *migration*. Parts of
  `kverus-review` (the `Origin Rust:` preservation comments) assume that, and do
  not apply to a repository that was written in Verus. `AGENTS.md` says which.
