# User-Defined Destructors (`Drop`)

**Status:** Not supported
**Category:** Traits
**Guide ref:** `source/docs/guide/src/features.md` — Traits

## What's unsupported

Verus does not support the `Drop` trait. You cannot implement `Drop` for types used in verified code, and types that implement `Drop` cannot be reasoned about in specifications.

```rust
// REJECTED by Verus
impl Drop for MyResource {
    fn drop(&mut self) {
        self.cleanup();
    }
}
```

## Why

`Drop` introduces implicit control flow (destructor calls at scope exit) that complicates Verus's reasoning about ownership and resource lifetimes. The verifier cannot model when and in what order destructors run.

## Workarounds

### 1. Explicit cleanup method

Replace `Drop` with an explicit `close` / `destroy` / `release` method that the caller must invoke:

```rust
struct MyResource {
    handle: u64,
}

impl MyResource {
    fn release(self) -> (result: Result<(), Error>)
        requires self.is_valid(),
    {
        // cleanup logic
    }
}
```

### 2. `external_body` type with drop

If you need RAII semantics at runtime, define the type as `external_body`:

```rust
#[verifier::external_body]
struct FileHandle {
    // Verus doesn't inspect this
}

// Drop impl lives in unverified code
#[verifier::external]
impl Drop for FileHandle {
    fn drop(&mut self) {
        // actual cleanup
    }
}
```

### 3. Use `vstd` tracked types

For verified resource management, use `vstd`'s ghost/tracked permission types (e.g., `Tracked<Perm>`), which model resource lifecycle in the proof without relying on `Drop`.

### 4. Wrapper pattern

Wrap a drop-bearing type inside `external_body` and expose a verified interface:

```rust
#[verifier::external_body]
struct Guard { /* MutexGuard or similar */ }

#[verifier::external_body]
fn unlock(guard: Guard)
{
    drop(guard); // explicit drop in unverified code
}
```

## Edge cases

- Types containing fields that implement `Drop` may also cause issues.
- `ManuallyDrop<T>` is usable in some contexts but Verus has limited support.
- `std::mem::drop(x)` as an explicit call is distinct from the trait — it just moves `x` and lets it go out of scope, but Verus still can't reason about the `Drop::drop` call.
- Derive macros that implicitly generate `Drop` (rare, but some proc macros do this) will be rejected.

## Related

- [debug-serde-traits.md](debug-serde-traits.md)
