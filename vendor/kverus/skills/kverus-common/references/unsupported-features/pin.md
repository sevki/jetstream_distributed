# `Pin`

**Status:** Not supported
**Category:** Types / Standard Library
**Guide ref:** `source/docs/guide/src/features.md` — Types and standard library functionality

## What's unsupported

Verus has no model for `std::pin::Pin<P>`. The type cannot be used in verified code — not as a parameter, return type, struct field, or local variable.

```rust
use std::pin::Pin;

// REJECTED by Verus
fn process(pinned: Pin<&mut MyStruct>) {
    // ...
}
```

## Workarounds

### 1. Use regular references

If pinning is only needed for async (e.g., `Future::poll`), and you've moved async out of the verified boundary, replace `Pin<&mut T>` with `&mut T` in the verified interface.

```rust
// Illustrative verified-interface shape; `is_valid` is a project spec method.
fn process(data: &mut MyStruct) -> (result: u64)
    requires data.is_valid(),
    ensures data.is_valid(),
{
    // verified logic
}
```

`old(...)` belongs in post-state reasoning; do not use `old(data)` in a `requires` clause.

### 2. Keep `Pin` outside the verified boundary

If an async runtime or dependency requires `Pin`, keep the pinned value and polling operation in an unverified crate or module. Exchange only Verus-supported plain values with verified code. An `external_body` does not make an unsupported type usable in a verified signature, and introducing any trusted wrapper still requires permission from the active task skill and a separately audited contract.

### 3. Avoid self-referential types

The main Rust use case for `Pin` is self-referential types. In verified code, redesign data structures to avoid self-references — use indices or handles instead of internal pointers.

## Edge cases

- `Pin<Box<T>>` is also unsupported, even though `Box<T>` is supported.
- `Unpin` trait bounds are ignored by Verus but the `Pin` wrapper itself is still rejected.
- If a dependency's API requires `Pin`, isolate that API outside the verified boundary; do not assume an `external_body` signature containing `Pin` will type-check.

## Related

- [async-functions.md](async-functions.md)
- [await.md](await.md)
