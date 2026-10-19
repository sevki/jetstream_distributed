# `transmute`

**Status:** Not supported
**Category:** Unsafe
**Guide ref:** `source/docs/guide/src/features.md` — Unsafe

## What's unsupported

Verus does not support `std::mem::transmute` or any form of type-punning. The verifier cannot reason about reinterpreting memory as a different type.

```rust
// REJECTED by Verus
fn u64_to_bytes(val: u64) -> [u8; 8] {
    unsafe { std::mem::transmute(val) }
}

// REJECTED by Verus
fn reinterpret<T, U>(val: T) -> U {
    unsafe { std::mem::transmute(val) }
}
```

Also unsupported:
- `std::mem::transmute_copy`
- `union`-based type punning for reinterpretation (note: `union` itself is supported for other uses)
- Pointer casts used for type punning (`*const T as *const U` then dereference)

## Workarounds

### 1. Explicit conversion functions

Write typed conversion functions that Verus can verify:

```rust
fn u64_to_bytes(val: u64) -> (result: [u8; 8])
    ensures
        result[0] == (val & 0xff) as u8,
        // ... remaining byte specs
{
    [
        (val & 0xff) as u8,
        ((val >> 8) & 0xff) as u8,
        ((val >> 16) & 0xff) as u8,
        ((val >> 24) & 0xff) as u8,
        ((val >> 32) & 0xff) as u8,
        ((val >> 40) & 0xff) as u8,
        ((val >> 48) & 0xff) as u8,
        ((val >> 56) & 0xff) as u8,
    ]
}
```

### 2. `to_le_bytes` / `from_le_bytes` via `external_body`

```rust
#[verifier::external_body]
fn u64_to_le_bytes(val: u64) -> (bytes: [u8; 8])
    ensures bytes == spec_u64_to_le_bytes(val),
{
    val.to_le_bytes()
}

#[verifier::external_body]
fn u64_from_le_bytes(bytes: [u8; 8]) -> (val: u64)
    ensures val == spec_u64_from_le_bytes(bytes),
{
    u64::from_le_bytes(bytes)
}
```

### 3. Use `as` casts for numeric conversions

For simple numeric reinterpretation (e.g., `u32` <-> `i32`), use `as` casts, which Verus partially supports:

```rust
let signed: i32 = unsigned_val as i32;
```

### 4. `external_body` for zero-cost transmutes

When you need transmute for FFI or performance and can specify the contract:

```rust
#[verifier::external_body]
fn bytes_to_header(buf: &[u8; 64]) -> (header: &Header)
    requires buf_matches_header_layout(buf@),
    ensures header == spec_parse_header(buf@),
{
    unsafe { std::mem::transmute(buf) }
}
```

## Edge cases

- `std::mem::zeroed::<T>()` is also problematic — Verus may reject it.
- `MaybeUninit<T>` is partially supported in some contexts but `assume_init()` (which is conceptually a transmute) requires care.
- Safe wrappers like `bytemuck::cast` are still rejected since Verus doesn't know about them.
- `transmute` inside `external_body` is fine — Verus doesn't inspect those bodies.
