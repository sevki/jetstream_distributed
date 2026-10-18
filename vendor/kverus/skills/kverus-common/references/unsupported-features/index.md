# Unsupported Rust Features in Verus

Quick index of Rust features that Verus does **not** support.
Each file contains a description, code examples showing the unsupported pattern,
recommended workarounds, and edge cases.

Source: `source/docs/guide/src/features.md` (Verus Guide — Supported Rust Features)

**Last synced with guide: 2026-05-13**

## Items

| Feature | File | Category |
|---------|------|----------|
| Async functions | [async-functions.md](async-functions.md) | Items |
| Async blocks | [async-blocks.md](async-blocks.md) | Expressions |
| `await` expressions | [await.md](await.md) | Expressions |
| Destructuring assignment | [destructuring-assignment.md](destructuring-assignment.md) | Expressions |
| Function pointer types | [function-pointer-types.md](function-pointer-types.md) | Types |
| `Pin` | [pin.md](pin.md) | Types / Std Library |
| Hardware intrinsics | [hardware-intrinsics.md](hardware-intrinsics.md) | Types / Std Library |
| Printing / I/O | [printing-io.md](printing-io.md) | Types / Std Library |
| Standard traits (`Debug`, `serde::Serialize`) | [debug-serde-traits.md](debug-serde-traits.md) | Traits |
| User-defined destructors (`Drop`) | [drop.md](drop.md) | Traits |
| `Mutex` / `RwLock` (std library) | [std-mutex-rwlock.md](std-mutex-rwlock.md) | Multi-threading |
| `transmute` | [transmute.md](transmute.md) | Unsafe |
