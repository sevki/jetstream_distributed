# Localize Proof Context

Sources:
- `source/docs/guide/src/assert_by.md`

Use `assert(F) by { ... }` when the proof needs temporary facts that should not pollute the rest of the function:

```rust
assert(goal) by {
    lemma_a(x);
    lemma_b(x);
};
```

This is usually better than exposing many quantified facts globally.

The proof `P` sees the ambient facts while proving `F`, but everything `P`
established except `F` is dropped after the closing brace:
`lemma_A(); assert(F) by { lemma_B(); }; assert(G);` is encoded to the solver
like `(A && B ==> F) && (A ==> G)`.

Compared with extracting an auxiliary lemma, `assert ... by` avoids reworking
which context the fact needs as `requires` and adding a lemma signature;
prefer a real lemma when the fact is reused across functions.
