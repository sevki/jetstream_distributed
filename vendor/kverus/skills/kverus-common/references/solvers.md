# Specialized Solvers

Sources:
- `source/docs/guide/src/assert_by_compute.md`
- `source/docs/guide/src/bitvec.md`
- `source/docs/guide/src/nonlinear.md`

Use the narrowest solver that matches the fact. Attach a prover mode either
to a single `assert(...) by (mode)` or to a whole `proof fn ... by (mode)`;
callers of a `by(mode)` proof fn discharge its preconditions with the normal
solver, and the proved fact is then available everywhere.

Bitwise facts — the default mode treats `&`, `|`, `^`, `<<`, `>>` as
uninterpreted:

```rust
assert((x & y) == (y & x)) by (bit_vector);
```

`bit_vector` bit-blasts integers to Z3 bit-vectors: ideal for bitwise
operations, decent for bounded-integer arithmetic, unable to reason about
symbolic `int` values; for `usize`/`isize` it verifies both 32- and 64-bit
encodings unless the platform size is configured. It is also the easiest way
to reason about truncation (`a as u32 == a & 0xffff_ffff`; the `add`, `sub`,
`mul` helpers truncate automatically).

Fully computable spec facts:

```rust
assert(pow(2, 8) == 256) by (compute_only);
```

`assert(e) by (compute)` runs the internal interpreter and lets Z3 finish
whatever the simplification leaves; `compute_only` requires the interpreter
to reduce the expression all the way to `true`, avoiding dependence on Z3
heuristics — prefer it when full stability matters. The interpreted
expression must be in spec mode and does not inherit ambient context. The
interpreter's runtime is capped by `--rlimit`; annotate recursive spec
functions with `#[verifier::memoize]` when result caching is needed (naive
Fibonacci, for example).

Nonlinear integer arithmetic — the default mode is linear-only, so `x * y`
with symbolic operands is uninterpreted there:

```rust
assert(x * y <= 100) by (nonlinear_arith)
    requires
        x <= 10,
        y <= 10,
        0 <= x,
        0 <= y;
```

`nonlinear_arith` is general-purpose but unpredictable. For equational
congruence facts (of the shape `(a - x) % b == 0`), `proof fn ... by(integer_ring)`
is decidable: `int` parameters only, no inequalities or division, function
calls treated as uninterpreted (unfold needed definitions in `requires`), and
it requires Singular to be installed. A common pattern combines them: an
`integer_ring` helper lemma supplies the modular-equality core, and the main
`by(nonlinear_arith)` lemma discharges the bounds.

Important: `bit_vector`, `compute`/`compute_only`, and `nonlinear_arith`
assertions do not inherit ambient facts — only a variable's type range comes
for free. Supply everything else explicitly through the assertion's
`requires` or move the concrete expression inside the assertion.
