# Hardware Intrinsics

**Status:** Not supported
**Category:** Types / Standard Library
**Guide ref:** `source/docs/guide/src/features.md` — Types and standard library functionality

## What's unsupported

Verus does not support hardware intrinsics — SIMD operations, architecture-specific instructions, and inline assembly. This includes:

- `std::arch::*` (e.g., `_mm256_add_epi32`, `_mm_prefetch`)
- `core::arch::*`
- `asm!` / `global_asm!` macros
- Any CPU-specific intrinsic functions

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

// REJECTED by Verus
unsafe fn simd_add(a: __m256i, b: __m256i) -> __m256i {
    _mm256_add_epi32(a, b)
}
```

## Workarounds

### 1. Scalar fallback in verified code

Write the equivalent operation using standard arithmetic that Verus can verify, and use intrinsics only in unverified performance-critical paths.

```rust
// Verified scalar version
fn add_arrays(a: &[u32], b: &[u32], out: &mut [u32])
    requires
        a.len() == b.len(),
        b.len() == out.len(),
    ensures
        forall|i: int| 0 <= i < a.len() ==> out@[i] == a@[i] + b@[i],
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> out@[j] == a@[j] + b@[j],
    {
        out[i] = a[i] + b[i];
        i += 1;
    }
}
```

### 2. `external_body` for intrinsic path

Wrap the SIMD/intrinsic code in `external_body` with spec that mirrors the verified scalar version:

```rust
#[verifier::external_body]
fn add_arrays_fast(a: &[u32], b: &[u32], out: &mut [u32])
    requires
        a.len() == b.len(),
        b.len() == out.len(),
    ensures
        forall|i: int| 0 <= i < a.len() ==> out@[i] == a@[i] + b@[i],
{
    // SIMD implementation at runtime
    unimplemented!()
}
```

### 3. Verified-then-swap pattern

Verify the scalar implementation, then at link time or via feature flags, swap in the intrinsic version behind the same spec contract.

## Edge cases

- `#[target_feature(enable = "...")]` attributes are ignored by Verus but the intrinsic calls inside are still rejected.
- Inline assembly (`asm!`) is rejected even inside `unsafe` blocks.
- `core::hint::black_box` and similar compiler hints are also unsupported.
