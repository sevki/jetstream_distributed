# Opaque and Reveal

Sources:
- `source/docs/guide/src/opaque.md`

If unfolding a spec function causes timeouts or bad automation, use `opaque` on the function and reveal it only inside focused proof blocks:

```rust
reveal(f);
assert(f(x) == expected);
```

Use `closed spec` for module abstraction: the body stays available to
module-local proofs while other modules reason through public lemma exports.
`opaque` hides the body even in the current module, so use `opaque`/`reveal`
for controlling automation and verification performance, not modularity.
