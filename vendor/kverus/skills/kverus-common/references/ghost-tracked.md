# Ghost, Tracked, Views, and Erasure

Sources:
- `source/docs/guide/src/ghost_vs_exec.md`
- `source/docs/guide/src/erasure.md`
- `source/docs/guide/src/reference-var-modes.md`
- `source/docs/guide/src/reference-proof-signature.md`
- `source/docs/guide/src/assert-mut-ref.md`
- `source/docs/guide/src/mutable-references.md`

## Variable Modes

Verus has three variable modes:

- `exec`: compiled value.
- `ghost`: erased value used for specifications and proofs.
- `tracked`: erased proof resource used linearly for permissions/tokens.

Mode availability:

| Context | Default variable mode | Can use ghost | Can use tracked | Can use exec |
| ------- | --------------------- | ------------- | --------------- | ------------ |
| `spec`  | ghost                 | yes           | no              | no           |
| `proof` | ghost                 | yes           | yes             | no           |
| `exec`  | exec                  | yes           | yes             | yes          |

## Exec Code Restrictions

`ghost` and `tracked` variables may be declared in exec code, but assignments to them must happen in proof context:

```rust
fn f() {
    let ghost mut x = 0;
    proof {
        x = 1;
    }
}
```

Use `proof { ... }` for proof calls from exec functions.

## `Tracked<T>` and `Ghost<T>`

Use wrapper types when ghost/tracked values need to cross exec function boundaries.

Parameter unwrapping:

```rust
fn f(Tracked(tok): Tracked<Token>, Ghost(model): Ghost<Model>) {
    proof {
        lemma(tok, model);
    }
}
```

Return unwrapping:

```rust
let (Tracked(tok), Ghost(model)) = make_resources();
```

The guide shows pattern matching as the primary way to unwrap these wrappers at function boundaries. For ordinary abstract views, `expr@` is shorthand for `expr.view()`.

## Proof Function Signatures

Tracked parameter:

```rust
proof fn consume(tracked tok: Token)
```

Tracked return:

```rust
proof fn make() -> (tracked tok: Token)
```

Mixed return:

```rust
proof fn split() -> (tracked ret: (Tracked<Token>, Ghost<Model>))
```

Pattern matching:

```rust
let tracked (Tracked(tok), Ghost(model)) = split();
```

## Mode Marker Hygiene

Use `ghost` and `tracked` markers where they communicate or enforce a mode
boundary, not on every value whose mode the context already determines:

- Prefix proof-only fields inside executable structs with `ghost_` or
  `tracked_` so their erasure and ownership role are visible at the
  declaration:

  ```rust
  pub struct Foo {
      value: u64,
      tracked_permission: Tracked<Permission>,
      ghost_model: Ghost<Model>,
  }
  ```

- Do not repeat the mode marker on every field of a `ghost struct`. A
  `tracked struct` is `tracked` by default; mark only the fields that are not
  linear ownerships as `ghost`.
- Within proof functions, pass and return tracked resources with `tracked`
  binders (see Proof Function Signatures); do not wrap each component of an
  all-tracked proof tuple in `Tracked<_>`. Reserve `Tracked<T>` and
  `Ghost<T>` for executable or mixed-mode boundaries where erased values must
  cross an exec signature.

## Erasure and Imports

Ghost code is erased before compilation. Guard imports or verifier-only attributes that exist only for verification:

```rust
#[cfg(verus_only)]
use crate::ghost_mod::ghost_fn;

#![cfg_attr(verus_only, verus::loop_isolation(false))]
```

Do not use `cfg(verus_only)` to change executable behavior; that can make verification unsound with respect to compiled code.

## Common Repairs

Symptom: cannot call proof/spec code directly from exec update.

Use:

```rust
proof {
    lemma(x@);
}
```

Symptom: inner value of `Tracked<T>` or `Ghost<T>` is unavailable at a function boundary.

Use:

```rust
fn f(Tracked(x): Tracked<X>, Ghost(y): Ghost<Y>) {
}
```

Symptom: tracked resource moved or duplicated incorrectly.

Repair by following linear ownership: pass tracked tokens by `tracked` value when consuming, by `tracked &` or `tracked &mut` when borrowing/mutating, and use library split/join methods rather than copying.

Symptom: `expression has mode spec, expected mode proof` when assigning a spec
collection update, such as `Set::insert`, to a ghost or tracked field.

Repair by looking for proof-mode operations such as `tracked_insert`,
`tracked_push`, split/join methods, or checked constructors. If none applies,
reconsider the representation or report the proof as blocked. Treat it as a
trusted boundary only when the value necessarily packages a concrete opaque or
external resource; do not use `assume` to bypass the mode mismatch.
