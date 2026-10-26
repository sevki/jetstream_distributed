# No escape hatches

The proofs in `src/` use no `assume`, `admit`, `external_body`, `axiom`, or any
other way of asserting something Verus did not check. CI enforces it by grep on
every pull request.

## `bit_vector` and `nonlinear_arith` are not escape hatches

`raft::proofs::wire` uses both: `by(bit_vector)` for the little-endian round
trip, `by(nonlinear_arith)` for the division bookkeeping in C32. Neither asserts
anything. They hand the goal to a *different decision procedure* — bit-blasting
for the first, a nonlinear arithmetic solver for the second — because the
default encoding is poor at bits and at multiplication. The obligation is
discharged, not waived: a false goal fails under either.

They are named here because "no escape hatches" should mean something precise,
and a reader who greps for `assume` should also know what `by(...)` does.

## `IdSet` rests on vstd's `HashSet` specification

`id::IdSet` is a `std::collections::HashSet<u128>` — the number inside each
`Id` — whose view is `Set<Id>`, by a `lift` spec function and one lemma that an
id is in the lifted set exactly when its number is in the stored one; the Raft
tally and the composed machine's debts are `IdSet`s. What it promises (`insert`,
`remove`, `contains`, `len`, `is_empty` are the set's) is proved from vstd's
specification of `HashSet`, and that specification is trusted, not proved: in
particular `vstd::std_specs::hash::obeys_key_model::<u128>()`, that the default
hasher behaves as a function on keys. The axiom lives in vstd, so CI's grep over
`src/` does not see it, and it is named here so that nobody has to find it. The
set stores the `u128` and not the `Id` because vstd states that axiom for the
built-in key types only; for a type of ours it could be assumed only with an
`assume`, which CI rejects. The `Vec` scans it replaced rested on `Vec`'s
specification alone.

`Id` itself adds nothing to trust. Its `==` is defined in the language, with
vstd's `PartialEqSpecImpl` (`obeys_eq_spec` is `true` and `eq_spec` is equality
of the numbers), and `id::value::lemma_id_eq` says so.

## The one exception, and it is not in `src/`

`vendor/verified-storage/pmemlog` is [Microsoft's verified persistent-memory
log](https://github.com/microsoft/verified-storage), vendored unmodified, and it
has six. Three are I/O primitives and a CRC computation — the code that actually
touches the device, with nothing beneath it to verify against. **Two are
assumptions about the physical world**, and anything this repository ever proves
on top of that log is conditional on them:

* `axiom_bytes_uncorrupted`: if `y` is the CRC of `x`, and a read gives back
  `x_c` and `y_c` with `y_c` the CRC of `x_c`, then `x_c == x`. This says a CRC
  detects the corruptions the device actually produces. It is not provable and
  it is not free: a device whose corruptions are CRC-preserving violates it, and
  every guarantee resting on it.
* `axiom_corruption_detecting_boolean`: the two flag values `CRC(b"0")` and
  `CRC(b"1")` are far enough apart that corruption cannot turn one into the
  other.

These are stated here rather than buried because the repository's rule is that
an assumption may be *an explicit documented part of the system model* and may
not be a way of making verification pass. These are the former; they are
enumerated one by one in `vendor/README.md`; and the CI grep covers
`src/` and not `vendor/` for exactly this reason, with the reason written into
the workflow.

Nothing in `src/` depends on `vendor/verified-storage/pmemlog` yet. When something does, this
section is where the conditional lives.

There are also no raised solver budgets: no `#[verifier::rlimit]` anywhere. The
long concrete scenarios are kept tractable purely by **splitting** them:

* `scenario_composed_handover` = `handover_phase_release` +
  `handover_phase_request` + `handover_phase_pass_token` +
  `handover_phase_acquire`;
* `scenario_request_and_token_routing` = `routing_phase_requests` +
  `routing_phase_token_hops` + `routing_phase_delivery`, with the token hops
  themselves delegated to `routing_one_hop`, proved once against an abstract
  state.

Each phase hands the intermediate state to the next as an *abstract*
characterisation, so no single query reasons about a dozen nested `Map`/`Set`
literals at once, and every phase verifies within Verus's default budget. Two
phases previously carried `#[verifier::rlimit(40)]`, and between them dominated
the cost of the entire proof run; splitting them removed the need. (`rlimit`
would not have been an escape hatch — it is a solver budget and cannot admit an
unproven fact — but a proof that needs a raised ceiling is usually a proof that
wants splitting.)

Splitting also surfaced a genuine defect in the specification. Reduced to a
single `AssignPrivilege` step, `routing_one_hop` *still* exceeded the solver's
limit — a cost that scaled with nothing in the proof. `verus --profile` named
the cause: `ray_wf` was a **matching loop**. Under the trigger
`r.nodes.contains(n)`, its conclusion `r.nodes.contains(r.holder[n])` matched
that same trigger at `r.holder[n]`, and so on without bound — 171,941
instantiations of one quantifier, 40% of 419,801 in a single proof.

`ray_wf` is now `ray_maps_total` (entries exist, triggered on
`r.nodes.contains(n)`) and `ray_holder_closed` (pointers stay in the cluster,
triggered on `r.holder[n]`). The second trigger fires only for holder pointers
some term already mentions, and its conclusion creates no new `holder[_]` term,
so nothing regenerates it. This mattered beyond speed: a matching loop makes
proofs pass or fail according to how many instantiations the solver burns before
it stumbles on the argument, which is precisely the kind of fragility a proof
suite should not have.

Every quantifier in `src/` has since been audited for the same defect, and three
more were found and fixed: `ray_init`'s non-root clause and `ray_holder_closed`
regenerated each other across two quantifiers, and `valid_execution` /
`composed_valid_execution` walked off the end of a sequence (`tr[i]` introduces
`tr[i + 1]`, which matches the trigger at `i + 1`; the `i < tr.len() - 1`
antecedent is checked *after* instantiation, so it does not stop e-matching).
Both now use multi-triggers naming the terms that must already exist.

The same care applies to `assert forall`, which carries whatever trigger is
written at the assertion site — `lemma_ray_frame_inv` and `lemma_reachable_step`
had each rebuilt a loop locally that the specification no longer contained.

**What that audit is and is not.** It is manual inspection plus the absence of
resource-limit blowups; it is not a check anything enforces, and the distinction
matters because nothing would fail if a future quantifier reintroduced a loop
until it happened to exhaust a budget. Of the 176 quantifiers in `src/`, 151
carry an explicit `#[trigger]` or `#![trigger …]`; the remaining 25 rely on
Verus's inference, and are the ones where the inferred trigger is a single
application term with nothing to regenerate (`exists|s| step(pre, post, s)` and
the like). CI additionally passes `--triggers-mode silent`, which suppresses the
notes Verus would otherwise print about automatically chosen triggers — good for
signal-to-noise in the log, and worth knowing before treating the build's
silence as evidence about triggers. It is not.

CI greps `src/` for the real escape hatches and fails the build if any appear.
Everything the proofs rely on that is not derived is a modelled transition or an
explicitly documented entry in the failure-model table above.

That grep now runs over a `src/` that also holds two Jetstream services, and it
still means what it said. The services are behind a feature that is off when the
proofs are checked, so Verus never compiles them and none of them needs a
`#[verifier::external]` to be kept out — which is why the feature exists rather
than being a packaging preference. If a service ever did need one, this grep
would fail the build, and that is the right outcome: an unverified module inside
a verified crate should be excluded by the build, not waved through by an
attribute.
