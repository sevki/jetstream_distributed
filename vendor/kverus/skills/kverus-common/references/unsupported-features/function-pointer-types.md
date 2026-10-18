# Function Pointer Types

**Status:** Not supported
**Category:** Types
**Guide ref:** `source/docs/guide/src/features.md` — Types and standard library functionality
**Executable-function refs:** `source/docs/guide/src/exec_funs_as_values.md`, `examples/guide/higher_order_fns.rs`

## What's unsupported

Verus does not support function pointer types (`fn(T) -> U`). You cannot store, pass, or invoke bare function pointers in verified code.

```rust
// REJECTED by Verus
fn apply(f: fn(u64) -> u64, x: u64) -> u64 {
    f(x)
}

// REJECTED by Verus
let fp: fn(u64) -> u64 = my_function;
```

## Workarounds

### 1. Use a generic executable-function value

Verus supports reasoning about executable function values through `Fn`/`FnOnce` and the builtin `call_requires` and `call_ensures`. Preserve the function argument's contract rather than using an unconstrained generic call:

```rust
fn apply(f: impl Fn(u64) -> u64, x: u64) -> (result: u64)
    requires
        call_requires(f, (x,)),
    ensures
        call_ensures(f, (x,), result),
{
    f(x)
}
```

### 2. Use `spec_fn` for spec-mode function values

In specifications, use the `spec_fn` type:

```rust
proof fn example(f: spec_fn(u64) -> u64)
    requires f(0) == 1,
{
    // ...
}
```

### 3. Use `external_body` dispatch

If runtime function-pointer dispatch cannot be represented with supported function values or an enum, an `external_body` dispatcher is a trusted boundary, not a verified workaround. Add one only when the active task explicitly permits it and after specifying the dispatch semantics; the following shape is illustrative only:

```rust
#[verifier::external_body]
fn dispatch(table: &FnTable, op: Op, arg: u64) -> (result: u64)
{
    unimplemented!()
}
```

### 4. Use an enum-based dispatch

Replace function pointer tables with an enum and a match:

```rust
enum Operation {
    Add,
    Multiply,
}

fn dispatch(op: Operation, a: u64, b: u64) -> (result: u64)
{
    match op {
        Operation::Add => a + b,
        Operation::Multiply => a * b,
    }
}
```

## Edge cases

- `fn()` types in struct fields are rejected.
- Casting a function item to `fn(...)` pointer type is rejected.
- Closures that don't capture anything still cannot be coerced to `fn(...)` in Verus.
- `extern "C" fn(...)` pointer types are also unsupported.
