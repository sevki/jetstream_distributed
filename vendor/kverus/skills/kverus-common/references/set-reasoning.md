# Set Reasoning Patterns

Sources:
- `source/vstd/pervasive.rs:218-232` (`assert_by_contradiction!` macro)
- `source/vstd/multiset.rs:269-272` (contradiction pattern in practice)
- `source/vstd/iset.rs:756-760` (contradiction for extensional equality)
- `source/docs/guide/src/llmforverusproof.md:185-210`
- `source/docs/guide/src/extensional_equality.md` (auto-promotion of `==` to `=~=`)
- `source/docs/guide/src/modes.md` (exec/spec/proof mode system, derived for non-auto-promotion contexts)

## Non-membership by Contradiction

To prove `!A.contains(m)` when the direct assertion fails, use proof by contradiction. This is the standard approach when subset relationships are not in the SMT context:

```rust
if A.contains(m) {
    // derive membership in a set known NOT to contain m
    superset.intro_lemma(m, witness);
    assert(false);  // contradiction with !superset.contains(m)
}
```

Alternatively, use the built-in macro:

```rust
assert_by_contradiction!(!A.contains(m), {
    superset.intro_lemma(m, witness);
});
```

Reference: `source/vstd/pervasive.rs` defines `assert_by_contradiction!` as equivalent to `if !b { proof; assert(false); }`.

## Set Extensional Equality via Bidirectional Forall

The extensional equality operator `=~=` checks equivalence for collection types like `Seq`, `Set`, and `Map` by proving that the collections contain equal elements. Note that by default, Verus promotes `==` to `=~=` inside assert, ensures, and invariant, so `assert(s1 == s2)` actually means `assert(s1 =~= s2)`. There is no need to explicitly use `=~=` in these contexts.

### Auto-promotion of `==` to `=~=`

Verus auto-promotes `==` to `=~=` only in specific syntactic contexts. The table below lists each context and whether `=~=` can be safely replaced by `==`:

| Context | Replaceable? | Reason |
|---------|-------------|--------|
| Inside `assert(...)` | `replaceable` | Auto-promotion applies; `==` is equivalent. |
| Inside `ensures` clause | `replaceable` | Auto-promotion applies. |
| Inside `invariant` clause | `replaceable` | Auto-promotion applies. |
| Inside `spec fn` return expression | `replaceable` | Spec function `==` is also auto-promoted to extensional equality. |
| Inside `if` condition | `required` | Auto-promotion does NOT apply in conditions; `=~=` is needed for extensional check. |
| Inside `requires` clause | `required` | `requires` does not auto-promote. |
| Inside `recommends` clause | `required` | `recommends` does not auto-promote. |
| In a `proof` variable assignment | `required` | Assignment contexts do not auto-promote. |
| Inside `assert(...) by { ... }` body | Context-dependent | The `by` block is proof code; if the assertion target is `assert(a =~= b)`, it may be needed for the proof strategy, but if the intent is extensional equality and it appears inside an `assert`, `==` auto-promotes. Default to `replaceable` unless the `by` block relies on `=~=` for trigger control. |

To prove `S1 == S2` when sets are constructed differently (e.g., recursive union vs. predicate), prove both containment directions explicitly:

```rust
assert(S1 == S2) by {
    assert forall|m: Mapping| S1.contains(m) implies S2.contains(m) by {
        S1.elimination_lemma(m);  // extract witness from S1
        let i = choose|i| ...;
        S2.introduction_lemma(m, i);  // introduce into S2
    };
    assert forall|m: Mapping| S2.contains(m) implies S1.contains(m) by {
        S2.elimination_lemma(m);
        let i = choose|i| ...;
        S1.introduction_lemma(m, i);
    };
};
```
