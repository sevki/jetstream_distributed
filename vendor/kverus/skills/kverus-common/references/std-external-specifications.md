# Standard-Library External Specifications

Source scope: Rust standard library and Verus guide

Sources:

- `source/docs/guide/src/reference-assume-specification.md`
- `source/docs/guide/src/reference-unwind-sig.md`

Use this reference when verified code calls a `std`, `core`, or `alloc` API for
which the active vstd has no sufficient specification. Also load
`proof-engineering-and-trust-boundaries.md`. An `assume_specification` is a
trusted contract for an implementation Verus does not verify; it is not a proof
of the implementation.

## Establish That a Specification Is Missing

Start from fresh verifier output and the exact call site.

1. Record the qualified API, receiver type, generic instantiation, and diagnostic.
2. Search the active Verus checkout's `source/vstd`, especially `std_specs`, and
   the repository's external-spec modules for that API and related operations.
3. Check imports, feature gates, registered broadcast groups, trait bounds, and
   the preconditions of any existing specification. Do not create a second
   contract merely because the existing one is not in scope or its obligations
   are unproved.
4. Confirm that the API's types and language features are supported by the
   active Verus version. A specification cannot make an unsupported type or Rust
   feature verifiable by itself.

## Read the Matching Rust Source

Identify the exact toolchain with `rustc --version --verbose` and locate its
sysroot with `rustc --print sysroot`. Prefer the installed `rust-src` files under
`library/core`, `library/alloc`, and `library/std`. If they are unavailable, use
the upstream Rust source pinned to the toolchain's commit or release; do not use
an unpinned latest implementation for an older compiler.

Read all of the following before drafting the contract:

- the public function or method implementation
- its doc comments, safety section, panic section, and examples that define behavior
- delegated helpers, trait methods, or intrinsics needed to understand effects
- relevant type invariants and ownership or aliasing behavior
- every success, failure, empty, boundary, and panic/unwind path used by callers

Record the toolchain version, source path, item name, and relevant comment or
documentation section in the external spec's module or item comments. Paraphrase
the behavior; do not paste large portions of Rust's source or documentation.

## Design the Contract

Match the executable API exactly: use its qualified path, generics, lifetimes,
allocator parameters, trait bounds, receiver, arguments, and return type.

- Use `requires` only for actual safety, validity, ordering, aliasing, or
  non-panic obligations supported by the API. Do not invent a strong precondition
  solely to make the current caller verify.
- Use `ensures` for the smallest source-supported semantics required for useful
  modular reasoning. Cover both successful and unsuccessful results.
- For immutable operations, relate results to the input's existing vstd view.
- For mutation through `&mut`, cursors, guards, or returned mutable references,
  relate `old(...)` and `final(...)` states and preserve unaffected state.
- Introduce an `external_type_specification`, view model, or prophetic final-state
  function only when the external type or borrow protocol requires it.
- Use a proved bridge lemma for consequences derivable from existing models.
  Use an axiom or broadcast axiom only for a genuine external semantic fact, and
  keep any broadcast group narrow.
- Model panic and unwind behavior from the source. Do not claim `no_unwind` for
  a path that can panic; express the real non-panic condition or the repository's
  conditional panic model.
- Do not encode caller-local invariants, ownership facts, or desired proof
  conclusions as library behavior. Reject vacuous contracts and guarantees that
  are stronger than the source supports.

Prefer extending an existing model shared by neighboring operations.

## Placement and Review

Use the repository's dedicated external-spec library and module exports.

Before editing, establish the proposed API, location, source basis, contract,
models, panic behavior, and TCB impact.

## Validate and Report

After adding or changing the contract:

1. Verify the external-spec library or its narrowest documented target.
2. Verify the original failing module and check every affected call site.
3. Run the repository's full verification gate.
4. Check that no duplicate external specification was introduced and that
   failure or mutation branches are not left unconstrained.
5. Report the qualified API, exact spec location, Rust version and source basis,
   focused and full command results, and residual TCB boundary.

Verification success proves that clients are consistent with the assumed
contract. It does not prove that the Rust standard-library implementation meets
that contract; future toolchain or vstd changes require re-auditing it.
