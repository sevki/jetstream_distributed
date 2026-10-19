# Standard Traits: `Debug`, `serde::Serialize`

**Status:** Not supported
**Category:** Traits
**Guide ref:** `source/docs/guide/src/features.md` — Traits

## What's unsupported

Verus does not support `Debug`, `Display`, or `serde::Serialize` / `serde::Deserialize` trait implementations in verified code. This includes both manual implementations and `#[derive(...)]`.

```rust
// REJECTED by Verus
#[derive(Debug)]
struct Point {
    x: u64,
    y: u64,
}

// REJECTED by Verus
impl std::fmt::Debug for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Point({}, {})", self.x, self.y)
    }
}

// REJECTED by Verus
#[derive(serde::Serialize, serde::Deserialize)]
struct Config {
    name: String,
    value: u64,
}
```

## Workarounds

### 1. Use `#[verifier::external]` on derive or impl

Mark the trait implementation as external so Verus ignores it:

```rust
#[verifier::external]
impl std::fmt::Debug for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Point({}, {})", self.x, self.y)
    }
}
```

### 2. Conditional derive with `cfg_attr`

Use `verus_keep_ghost` or a custom feature flag to conditionally derive:

```rust
#[cfg_attr(not(verus_keep_ghost), derive(Debug, serde::Serialize))]
struct Point {
    x: u64,
    y: u64,
}
```

### 3. Put derives in a separate unverified module

Define the struct in the verified module; implement Debug/Serialize in an unverified companion module.

### 4. Manual `to_string` via `external_body`

```rust
#[verifier::external_body]
fn point_to_string(p: &Point) -> (s: String)
{
    format!("Point({}, {})", p.x, p.y)
}
```

## Edge cases

- `#[derive(Clone, Copy, PartialEq, Eq)]` **is** supported — only formatting/serialization traits are unsupported.
- `Display` is unsupported for the same reasons as `Debug`.
- `serde` proc-macro generated code is rejected because Verus cannot analyze it.
- `Hash` derivation may work for simple types but is not officially supported.
- Trait objects `dyn Debug` are doubly problematic (trait objects are only partially supported).

## Related

- [printing-io.md](printing-io.md)
- [drop.md](drop.md)
