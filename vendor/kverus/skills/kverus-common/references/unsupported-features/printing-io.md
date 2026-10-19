# Printing / I/O

**Status:** Not supported
**Category:** Types / Standard Library
**Guide ref:** `source/docs/guide/src/features.md` — Types and standard library functionality

## What's unsupported

Verus does not model I/O operations. This includes all printing macros, file I/O, network I/O, and standard streams.

```rust
// REJECTED by Verus
fn log_value(x: u64) {
    println!("value = {}", x);      // unsupported
    eprintln!("error!");             // unsupported
    std::fs::write("out.txt", "x"); // unsupported
}
```

Unsupported items include:
- `println!`, `print!`, `eprintln!`, `eprint!`, `format!`
- `dbg!`
- `std::io::*` (`Read`, `Write`, `BufReader`, `stdin`, `stdout`, etc.)
- `std::fs::*`
- `std::net::*`

## Workarounds

### 1. Remove I/O from verified code

The cleanest approach: verified functions compute results, unverified code handles I/O.

```rust
// Verified: pure computation
fn compute_result(input: &[u64]) -> (result: u64)
    ensures result == spec_compute(input@),
{
    // ...
}

// Unverified: I/O
fn main() {
    let input = read_input();       // unverified
    let result = compute_result(&input);  // verified
    println!("{}", result);         // unverified
}
```

### 2. Trusted `external_body` boundary for logging

Use this only when the active task permits a trusted boundary and the project accepts unchecked logging behavior:

```rust
#[verifier::external_body]
fn debug_log(msg: &str)
{
    eprintln!("[DEBUG] {}", msg);
}
```

With no postconditions, callers derive no functional result facts from `debug_log`, but Verus still does not check its body, termination, panic behavior, or side effects. This remains a trusted boundary.

### 3. Unverified adapter for result-bearing I/O

Keep result-bearing filesystem or network operations in an unverified adapter. The following is architecture pseudocode, not a Verus-checked example:

```rust
// Unverified crate or module.
fn write_bytes(path: &str, data: &[u8]) -> std::io::Result<()> {
    std::fs::write(path, data)
}
```

If verified callers need a contract for such an adapter, design and review that trusted contract under `../proof-engineering-and-trust-boundaries.md`; do not infer filesystem semantics from this sketch.

## Edge cases

- `format!` is unsupported because it relies on `Debug`/`Display` traits (see [debug-serde-traits.md](debug-serde-traits.md)).
- `write!` / `writeln!` to a `Vec<u8>` or `String` buffer is also unsupported.
- `panic!` with format args is unsupported; `panic!("literal")` may work in some contexts.
- Test code may be excluded by a project's Verus configuration, but do not assume every `#[test]` function is automatically outside verification; check the active command.

## Related

- [debug-serde-traits.md](debug-serde-traits.md)
