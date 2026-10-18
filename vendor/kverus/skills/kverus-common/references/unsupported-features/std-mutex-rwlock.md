# `Mutex` / `RwLock` (Standard Library)

**Status:** Not supported
**Category:** Multi-threading
**Guide ref:** `source/docs/guide/src/features.md` — Multi-threading

## What's unsupported

Verus does not support `std::sync::Mutex` or `std::sync::RwLock`. These types cannot be used in verified code because Verus cannot reason about their locking semantics and interior mutability.

```rust
use std::sync::Mutex;

// REJECTED by Verus
fn increment(counter: &Mutex<u64>) {
    let mut guard = counter.lock().unwrap();
    *guard += 1;
}
```

## Workarounds

### 1. Use vstd verified lock implementations

Current vstd provides `RwLock`, whose constructor takes an invariant predicate and whose handles must be released explicitly. This example follows `source/vstd/rwlock.rs`:

```rust
use vstd::prelude::*;
use vstd::rwlock::RwLock;

fn example() {
    let lock = RwLock::<u64, spec_fn(u64) -> bool>::new(
        5,
        Ghost(|v| v == 5 || v == 13),
    );

    let (value, write_handle) = lock.acquire_write();
    assert(value == 5 || value == 13);
    write_handle.release_write(13);
}
```

See: `source/vstd/rwlock.rs` and [vstd `rwlock` documentation](https://verus-lang.github.io/verus/verusdoc/vstd/rwlock/index.html).

### 2. Isolate a standard-library lock

If runtime compatibility requires `std::sync::Mutex` or `RwLock`, keep it in an unverified module and expose only supported values or a project-reviewed abstraction. Do not present an `external_body` wrapper as a verified lock: the lock semantics, poisoning, guard lifetime, panic behavior, and synchronization effects remain unchecked. Any trusted wrapper requires explicit permission from the active task and a contract audit.

### 3. Use vstd atomics for simple counters

For atomic integer operations, vstd provides verified atomic types:

```rust
use vstd::atomic_ghost::*;

// AtomicU64 with ghost state for verification
```

See: [vstd atomic_ghost documentation](https://verus-lang.github.io/verus/verusdoc/vstd/atomic_ghost/index.html)

## Edge cases

- `MutexGuard` and `RwLockReadGuard` / `RwLockWriteGuard` are also unsupported (they come from std).
- `parking_lot::Mutex` and similar third-party locks are equally unsupported.
- `Condvar` is unsupported.
- vstd's `RwLock` and atomics have different APIs — they are not drop-in replacements for `std::sync` types.
- `Mutex::new()` in a `static` (via `OnceLock` or `lazy_static!`) is unsupported on multiple levels.

## Related

- [drop.md](drop.md) — `MutexGuard` relies on `Drop` for unlock
- Verus guide: `source/docs/guide/src/concurrency.md`
- Verus guide: `source/docs/guide/src/interior_mutability.md`
