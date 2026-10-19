# Async Functions

**Status:** Not supported
**Category:** Items
**Guide ref:** `source/docs/guide/src/features.md` — Items

## What's unsupported

Verus cannot verify `async fn` declarations. The verifier rejects any function declared with the `async` keyword.

```rust
// REJECTED by Verus
async fn fetch_data(url: &str) -> Result<Vec<u8>, Error> {
    // ...
}
```

## Workarounds

### 1. Put async orchestration in an unverified layer

Keep the `async fn`, runtime, I/O, and `.await` operations outside the verified crate or module. Pass plain, supported values to verified computation. This is an architecture sketch; the async function itself is not checked by Verus:

```rust
// Verified computation: no async types or operations.
fn decode(bytes: &Vec<u8>) -> (result: u64) {
    // verified logic
}

// Unverified orchestration layer.
async fn fetch_and_decode(url: &str) -> Result<u64, Error> {
    let bytes = fetch_data(url).await?;
    Ok(decode(&bytes))
}
```

Do not use an `external_body` synchronous wrapper merely to hide async syntax. Such a wrapper would introduce an unchecked contract and may still expose unsupported types.

### 2. Factor async out of verified boundary

Keep all async code outside the verified crate entirely. Verified code handles pure computation; the unverified async layer orchestrates I/O.

## Edge cases

- `async fn` in trait definitions is also unsupported.
- `async` closures are unsupported (see also [async-blocks.md](async-blocks.md)).
- Even if the function body contains no `.await`, the `async` keyword alone causes rejection.

## Related

- [async-blocks.md](async-blocks.md)
- [await.md](await.md)
