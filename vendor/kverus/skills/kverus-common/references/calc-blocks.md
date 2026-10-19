# Structured Calculation

Sources:
- `source/docs/guide/src/calc.md`

Use `calc!` when proving a transitive chain:

```rust
calc! {
    (==)
    a; {
        lemma_step_1();
    }
    b; {
        lemma_step_2();
    }
    c;
}
```

Each step's proof is restricted to that step, and the surrounding function
sees only the outer relation `a_1 R a_n` — intermediate expressions and their
proofs do not pollute the outer proof context. `calc!` supports transitive
relations such as `==` and `<=`.

An intermediate step may use a more precise relation than the top-level one
(for example `==` or `<` steps inside a `<=` chain); the per-step relations
are checked for consistency with the top-level relation, so an inconsistent
one is reported as an error.

Use this for algebraic equality, ordering chains, and readability around intermediate expressions.
