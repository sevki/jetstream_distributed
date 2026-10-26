# Evidence: proved, tested, assumed

Every claim in this repository is in one of three tiers, and the tiers are not
interchangeable. A sentence in this book that says "guarantee" means the first tier
unless it says otherwise.

| Tier | What backs it | Where it lives |
| --- | --- | --- |
| **Proved** | Verus checks a theorem about the model or about verified code | `proofs/`, and the verified executable files |
| **Tested** | Tests, a simulated network, and a fuzzer exercise plain Rust | `service/`, `tests/`, the scheduling code |
| **Assumed** | The proofs rest on it and nothing checks it | the failure model, the vendored log's assumptions, the docs that say so |

## What "proved" is about

The core of the repository is a *model*, and the proofs are about the model. Each
algorithm also has verified executable code (small `u64`-valued functions and the
records they act on), each with a postcondition stated in the model's terms and a
theorem discharging it. That is how the gap between model and code is narrowed: the
service calls the function the theorem is about.

It is narrowed, not closed. The lock around a verified core, the roster, the network and
the scheduler are not under proof. The Reference's
[status section](reference/status.md#status-proven-modelled-future-work)
lists, by name, what is proven, what is modelled and not proven, and what is not modelled
at all.

## Reading the file names

The naming follows the vendored verified-storage convention, and it tells you which tier
a file is in before you open it:

| Suffix | Meaning | Who checks it |
| --- | --- | --- |
| `_t.rs` | **trusted**: the model, the specification, the definitions a claim is stated in | a reader, because no proof checks them against anything |
| `_v.rs` | **verified**: executable code and proofs | Verus |
| none (`service/`) | plain Rust | the tests |

The most important thing to audit in a proof repository is the part nothing checks, so
the trusted files are where to start. The model never imports the specification layer,
so a specification cannot be quietly weakened to fit the model.

## The rules the repository holds itself to

- **No escape hatches.** `assume`, `admit`, `axiom`, `external_body` and friends are
  rejected by CI in `src/`. The one documented exception is the vendored persistent-memory
  log, whose assumptions are listed.
- **Nothing vendored is edited.** The vendored directories are verbatim copies at a pinned
  commit, and CI diffs them.
- **Say what is proved and what is merely tested.** The running mailbox is a transcription
  of the mailbox model, not a refinement; only its queue-and-flags core is verified. A doc
  that blurs that is a bug.

## What CI runs

Every pull request runs the whole of this: both Verus entry points over the crate, the
vendored log's proof check, the service tests, the simulated-network scenarios, a minute of
coverage-guided fuzzing of the protocol search, and a check that the vendored skills are
unmodified.

The simulated network is the part that reaches past the proofs. It runs the executable
protocol under duplicated, reordered, delayed and dropped messages, with runtime oracles
checking the same properties the theorems state, and a search over seeds with the ones that
once broke something kept as a regression replay.

## How to read a claim row

Each row in the Reference's claims tables has the same four parts: a number (`A14`, `MB10`,
`C54`), what is claimed, the name of the Verus theorem, and **what it assumes**. The last
column is the one to read. A theorem with `none` there holds in every state. One that says
`reachability` or `an execution` holds in every state a run can reach. One that names a
hypothesis holds *given it*, and the hypothesis is stated so it can be discharged.

## What this book does not prove

Nothing here is a proof. The chapters explain how the protocols fit and say which of the
Reference's claims each relationship rests on. If a chapter and the Reference disagree
about what is proved, the Reference and the code are right, and the chapter is the thing
to fix.

## Checking it yourself

```text
cargo test                              # services, simulated-network tests, unit tests
verus --crate-type=lib src/lib.rs       # the proofs (needs the pinned Verus)
cargo verus verify --no-default-features
mdbook build book                       # this book
```

Verus is pinned, with the Rust toolchain it was built against. If it is not installed,
CI is the check.
