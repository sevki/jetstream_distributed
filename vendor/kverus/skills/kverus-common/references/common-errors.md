# Common Verification Error Repairs

Sources:
- `source/docs/guide/src/requires_ensures.md`
- `source/docs/guide/src/smt_failures.md`
- `source/docs/guide/src/while.md`
- `source/docs/guide/src/checklist.md`
- `source/docs/guide/src/develop_proofs.md`
- `source/docs/guide/src/overflow.md`
- `source/docs/guide/src/extensional_equality.md`
- `source/docs/guide/src/recursion.md`

## Triage Order

1. Identify the failed obligation: postcondition, precondition, assertion, invariant entry, invariant preservation, overflow, termination, or syntax/mode error.
2. Locate the smallest related code element: current function, called lemma, spec helper, loop, or direct dependency.
3. Check Verus notes, especially recommendation failures and trigger notes.
4. Re-run verification after each meaningful edit.

## Failed Postcondition

Likely causes:

- The function body computes the right value but the proof context lacks a bridge fact.
- A called function's `ensures` is too weak.
- A loop invariant does not summarize enough state at loop exit.

Preferred repairs:

```rust
assert(intermediate_fact);
```

or introduce/call a focused lemma if the fact is reusable or inductive.

During proof development, `assume` can isolate which missing fact would make progress. Do not leave assumptions in complete proof work unless the active task explicitly permits trusted assumptions.

## Precondition Not Satisfied

Likely causes:

- Caller has the fact, but SMT needs it surfaced.
- Bounds or mode-specific facts are not in scope.
- Loop isolation dropped facts from the enclosing function.

Preferred repairs:

```rust
assert(required_bound);
callee(arg);
```

For calls inside loops, copy relevant enclosing `requires` clauses into loop invariants.

## Loop Invariant Failure

Distinguish two failures:

- Fails on entry: invariant is too strong for initial values.
- Fails at end of body: invariant is not preserved or needs a post-update assertion.

Common missing invariants:

- Bounds: `0 <= i <= n`.
- Function preconditions used inside the loop.
- Relation between exec state and spec model.
- Frame facts about unchanged fields.
- Accumulated quantified facts over processed indices.

See `invariants.md`.

## Arithmetic Overflow or Underflow

Likely causes:

- Exec integer operation needs bounded proof.
- Loop body lacks a bound invariant.
- Nonlinear arithmetic fact is unavailable to the default solver.

Preferred repairs:

```rust
assert(x <= limit);
assert(x * y <= bound) by (nonlinear_arith)
    requires
        x <= x_bound,
        y <= y_bound;
```

Use `by (bit_vector)` for bitwise/truncation facts.

## Mode Error

Symptoms include inability to call a `spec` or `proof` function from the current context, or ghost values leaking into exec code.

Preferred repairs:

- Move proof-only calls into a `proof { ... }` block.
- Use `Tracked<T>` or `Ghost<T>` wrappers for ghost/tracked values crossing exec signatures.
- Unwrap `Tracked<T>` or `Ghost<T>` values with the pattern forms shown in `ghost-tracked.md`.

See `ghost-tracked.md`.

## Quantifier or Trigger Failure

Likely causes:

- The quantified fact is true but not instantiated.
- Trigger is absent, too broad, or not present in the goal expression.

Preferred repairs:

```rust
assert(is_even(s[i]));
```

or prove a quantified assertion with:

```rust
assert forall|i: int| 0 <= i < n implies P(i) by {
    lemma_for_i(i);
};
```

See `quantifiers.md`.

## Termination Failure

For recursive proof/spec functions, add a `decreases` clause that follows the structurally decreasing argument or measure:

```rust
proof fn lemma(i: nat)
    decreases i
{
    if i > 0 {
        lemma((i - 1) as nat);
    }
}
```
