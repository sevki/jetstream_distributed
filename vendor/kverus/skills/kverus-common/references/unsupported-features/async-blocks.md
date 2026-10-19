# Async Blocks

**Status:** Not supported
**Category:** Expressions
**Guide ref:** `source/docs/guide/src/features.md` — Expressions and Statements

## What's unsupported

Verus rejects `async { ... }` block expressions. These create anonymous `Future` values, which Verus has no model for.

```rust
// REJECTED by Verus
let fut = async {
    let x = some_async_op().await;
    x + 1
};
```

## Workarounds

### 1. Replace with synchronous block

If the async block is used purely for composition (no actual I/O), replace with a regular block or closure.

```rust
// Instead of async block, use a regular closure or block
let result = {
    let x = some_sync_op();
    x + 1
};
```

### 2. Move async blocks to unverified code

Keep the entire async block in an unverified orchestration layer and call verified functions only with supported plain values. The following is architecture pseudocode, not Verus-checked async code:

```rust
// Unverified layer.
let result = async {
    let input = some_async_op().await;
    verified_compute(input)
}
.await;
```

## Edge cases

- `async move { ... }` is equally unsupported.
- Hiding an async block in `external_body` makes its behavior unchecked; use such a boundary only when the active task explicitly permits it and no unsupported type crosses the verified signature.

## Related

- [async-functions.md](async-functions.md)
- [await.md](await.md)
