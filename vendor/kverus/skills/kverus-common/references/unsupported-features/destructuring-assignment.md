# Destructuring Assignment

**Status:** Not supported
**Category:** Expressions
**Guide ref:** `source/docs/guide/src/features.md` — Expressions and Statements

## What's unsupported

Verus does not support [destructuring assignment](https://doc.rust-lang.org/reference/expressions/operator-expr.html#destructuring-assignments) — assigning to a pattern of already-declared variables on the left-hand side of `=`.

```rust
let mut a;
let mut b;
// REJECTED by Verus
(a, b) = (1, 2);

let mut point = Point { x: 0, y: 0 };
// REJECTED by Verus
Point { x, y } = Point { x: 1, y: 2 };
```

Note: this is distinct from `let` destructuring, which **is** supported.

## Workarounds

### 1. Use `let` bindings (rebinding)

```rust
let (a, b) = (1, 2); // supported — this is a let-destructure, not assignment
```

### 2. Assign fields individually

```rust
let mut a: u64 = 0;
let mut b: u64 = 0;
let pair = (1u64, 2u64);
a = pair.0;
b = pair.1;
```

### 3. Assign struct fields individually

```rust
let mut point = Point { x: 0, y: 0 };
let new_point = Point { x: 1, y: 2 };
point.x = new_point.x;
point.y = new_point.y;
```

### 4. Shadow with a new `let`

If you don't need to mutate the same binding later:

```rust
let a = 0u64;
let b = 0u64;
// later:
let (a, b) = compute_pair();
```

## Edge cases

- `let (a, b) = expr;` works fine — only re-assignment to existing variables via pattern is rejected.
- Nested destructuring assignment (`(a, (b, c)) = ...`) is also unsupported.
- Slice destructuring assignment (`[a, b] = arr;`) is unsupported.
