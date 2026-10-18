# Loop, Recursive, and Type Invariants

Sources:
- `source/docs/guide/src/while.md`
- `source/docs/guide/src/invariants.md`
- `source/docs/guide/src/recursion.md`
- `source/docs/guide/src/recursion_loops.md`
- `source/docs/guide/src/reference-type-invariants.md`

## Core Rule

Verus verifies loops modularly. A loop does not automatically inherit all facts from the surrounding function. If the loop body or exit proof needs a function precondition, copy that fact into the loop invariant.

Pattern:

```rust
while i < n
    invariant
        0 <= i <= n,
        precondition_needed_inside_loop,
        accumulator == model(i),
{
    ...
}
```

## Build an Invariant Set

For most loops, add invariants in this order:

1. Index bounds, with the post-iteration endpoint included: `0 <= i <= n`.
2. Function preconditions needed inside the loop.
3. Relation between executable state and spec model.
4. Bounds needed to rule out overflow/underflow.
5. Frame facts for values not modified by the loop.
6. Quantified facts summarizing processed elements.

## Entry vs Preservation

If an invariant fails on entry, it is too strong for the initial state or needs initialization proof.

If it fails at the end of the body, preserve it by adding a local assertion after the update:

```rust
let old_model = model(i);
...
assert(model(i + 1) == update(old_model, x));
```

## Exit Reasoning

Make invariants strong enough that the negated loop condition gives the desired final index relation.

Example:

```rust
while i < n
    invariant
        i <= n,
{
    i = i + 1;
}
// Here Verus can combine i <= n with !(i < n) to prove i == n.
```

Do not write `i < n` as an invariant when the loop is supposed to finish with `i == n`.

## Accumulator Model

Tie each mutable accumulator to a spec expression over the processed prefix:

```rust
invariant
    sum == spec_sum(seq@.take(i as int)),
```

When preservation fails, expose sequence equalities:

```rust
let next = seq@.take((i + 1) as int);
assert(seq@.take(i as int) == next.drop_last());
assert(seq[i as int] == next.last());
```

## Overflow Bounds

Executable arithmetic needs bounds. Add loop invariants that bound each arithmetic operand, not only the final result.

Example shapes:

```rust
invariant
    fib(i as nat) <= u64::MAX,
    cur == fib(i as nat),
    prev == fib((i - 1) as nat),
```

If the bound relies on monotonicity, introduce a lemma and call it in a `proof { ... }` block before the arithmetic operation.

## Quantified Progress

For loops over arrays, slices, sequences, maps, or sets, summarize processed elements:

```rust
invariant
    forall|j: int| 0 <= j < i ==> P(#[trigger] seq@[j]),
```

Choose triggers that appear in later goals. If Verus does not instantiate the invariant, assert a trigger-shaped expression near the goal.

## Recursion and Decreases

Recursive proof/spec functions usually require `decreases` when the structural decrease is not obvious:

```rust
proof fn lemma(i: nat, j: nat)
    requires
        i <= j,
    decreases j - i
{
    if i < j {
        lemma(i, (j - 1) as nat);
    }
}
```

For induction, split base cases explicitly, then make recursive lemma calls that match the decreases measure.

## Type Invariants for Model Values

When a datatype carries an intrinsic validity invariant, decide between a
type-level invariant and explicit predicate contracts:

- Prefer `#[verifier::type_invariant]` when every construction of the type is
  valid and every operation preserves the invariant — thin wrappers with range
  bounds as well as structural bounds on containers. Verus inserts the proof
  obligations automatically at constructor expressions, field assignments, and
  calls taking `&mut X`; every consumer then obtains the fact with the builtin
  pseudo-lemma `use_type_invariant` instead of threading validity through each
  contract:

  ```rust
  struct Range {
      start: u64,
      end: u64,
  }

  impl Range {
      #[verifier::type_invariant]
      spec fn type_inv(self) -> bool {
          self.start <= self.end
      }
  }
  ```

  Constraints: the type must be a struct or enum declared in the same crate
  with no fields public outside it, and the invariant applies to exec objects
  and tracked-mode ghost objects, not to spec objects. In exec functions, call
  `use_type_invariant(&x)` inside a `proof` block on a tracked or exec
  variable. Keep the invariant function as private as possible.

- Keep the invariant as an explicit `inv()` spec predicate (or an `Inv`-style
  proof trait) threaded through contracts when either of these holds:
  - The invariant is transiently broken. Type invariants have no supported
    "temporarily broken" state; a constructor that fills in a default and
    repairs it in a later statement is checked mid-sequence. The guide's
    field-borrow workaround restructures the executable code, which
    `exec-code-preservation.md` rules out, so state the operation with
    `old(self).inv()` and `final(self).inv()` contracts instead and keep the
    intermediate state internal.
  - Mutating operations may panic. A type invariant charges every exit path
    of a mutator that takes `&mut X` with restoring the invariant, which
    couples the invariant to the method's panic behavior. Explicit contracts
    leave panic behavior to each method's own `requires`/`ensures` and
    `no_unwind` claims.

- One predicate, one mechanism: once a type carries a `type_invariant`, remove
  an `impl Inv` or `inv()` contract stating the same fact and migrate callers
  from `requires inv()` threading to `use_type_invariant`. Keeping both forks
  one fact into two proof paths whose definitions drift apart.

- Weakening the invariant and restating a single clause as per-method
  postconditions is a third lever when one clause causes the problems above;
  it trades implicit strength for explicit per-method guarantees.

- Use a separate `wf(...)` predicate only for well-formedness relations that
  depend on another value. Making fields private provides representation
  hiding, but it does not cause Verus to establish `inv()` automatically.
