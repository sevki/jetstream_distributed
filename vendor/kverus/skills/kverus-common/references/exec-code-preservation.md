# Executable Code Preservation

Source scope: KVerus migration and review policy

Use this rule whenever a KVerus task adds, removes, or rewrites executable Rust
relative to the original source. It does not apply to changes confined to `spec`,
`proof`, ghost/tracked state, Verus attributes, or comments.

## Required Comment

Place one block comment immediately before the modified executable code. For a pure
removal with no replacement, keep the comment at the original location. The comment
must contain, in this order:

1. A brief, concrete reason why the executable code must differ. Name the relevant
   Verus or vstd limitation when there is one; avoid vague statements such as "needed
   for verification."
2. The original Rust code, introduced by the exact label `Origin Rust:`.

Preserve the original code accurately enough to compare control flow, calls,
arguments, operators, and side effects. A single comment may cover one contiguous
modified block. Do not use a distant comment or rely only on Git history.

Preferred form:

```rust
/* `Range::len` is unspecced by vstd.
 * Origin Rust: while curr_range.len() < count && curr_range.end < self.bitset.len() {
 */
```

For a multi-line original, continue it on subsequent `*` lines. For newly added
executable code with no corresponding original statement, use
`Origin Rust: <none; new executable code>`.

## Review Rule

Treat an executable modification as noncompliant when its preservation comment is
missing, is not immediately adjacent, does not use a block comment, omits either the
reason or `Origin Rust:`, puts the original before the reason, or does not faithfully
represent the original code. Review semantic equivalence separately; a compliant
comment does not establish that runtime behavior is preserved.

## Import Layout for Verification-Added Imports

Lay out verification-added imports above the imports inherited from the
executable source, in blank-line separated groups:

```rust
use vstd::{
    laws_cmp::{obeys_cmp_ord, obeys_partial_cmp},
    laws_eq::obeys_eq_spec_properties,
};
use other_crate::{decode_pod, from_bytes_spec};

use crate::models::{CpuId, MemoryRegion};

// Imports inherited from the original source, unchanged:
use ...;
```

The first group collects the new spec/proof imports from dependency crates;
the second holds this file's local spec model imports; the last block is the
original import list, left unchanged. The blank lines are load-bearing: the
formatter alphabetizes `use` declarations only within a contiguous run and
never across a blank line (the unstable import-grouping options are ignored
on the stable toolchain). Drop the separator and the whole run is
alphabetized, sinking the local spec imports among the original imports and
pushing the dependency imports to the bottom.

Within each group, combine definitions from the same crate into one `use`
statement, including definitions from different modules of that crate. Do not
merge a newly added spec/proof `use` of a crate into a pre-existing
executable `use` of that same crate; the blank-line separation between the
verification-added groups and the original import list takes precedence over
this merging for such pairs.
