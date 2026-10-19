# `await` Expressions

**Status:** Not supported
**Category:** Expressions
**Guide ref:** `source/docs/guide/src/features.md` — Expressions and Statements

## What's unsupported

Verus rejects `.await` expressions. Since async functions and async blocks are unsupported, there is no context in which `.await` could appear in verified code.

```rust
// REJECTED by Verus
async fn example() {
    let data = fetch().await; // `.await` is unsupported
}
```

## Workarounds

### 1. Move `.await` to unverified orchestration

Keep `.await` and the future in an unverified layer. Feed the completed, supported value into a verified function. This is architecture pseudocode, not Verus-checked async code:

```rust
// Verified computation.
fn process(data: &Vec<u8>) -> (result: u64) {
    // verified logic
}

// Unverified orchestration.
async fn example() -> u64 {
    let data = fetch().await;
    process(&data)
}
```

### 2. Boundary pattern

Structure the crate so all `.await` calls live in unverified async glue code, while verified functions receive and return plain values.

## Edge cases

- `.await` on a pinned future is doubly unsupported (`Pin` is also unsupported).
- Putting `block_on` inside `external_body` does not verify the runtime, future, panic, or I/O behavior; it is a trusted boundary and requires explicit task permission.

## Related

- [async-functions.md](async-functions.md)
- [async-blocks.md](async-blocks.md)
- [pin.md](pin.md)
