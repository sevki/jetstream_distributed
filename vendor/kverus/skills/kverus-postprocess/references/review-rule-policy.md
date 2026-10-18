# KVerus Postprocess Review Rule Policy

## Static Seed Rules

These static rules come from KVerus review practice and repository constraints:

- If an axiom is proved, rename it from `axiom_xxx` to `lemma_xxx`.
- Comments should describe properties and obligations, not the proof technique used to discharge them.
- Avoid adding unnecessary comments; preserve existing useful property-oriented rustdoc unless the code no longer matches it.
- Do not use `#[allow(deprecated)]` or broad `#[allow(...)]` attributes to bypass verification or compiler warnings without a narrow justification.
- Avoid changing executable source behavior or moving definitions solely to make proofs easier.
- Prefer idiomatic Verus expressions, for example `item matches Pattern ==> cond` over `match item { Pattern => cond, _ => true }`.
- Avoid unnecessary casts in spec/proof code, especially `as int` when the expression is already in spec integer mode.
- Avoid accidental reverts of recently merged cleanup changes.
- Delegate redundant-assert simplification to `kverus-strip` when a targeted verification command is available, then run the configured formatter before presenting final proof-sensitive changes.

## Dynamic Rule Refresh

The postprocess refresh command queries the GitHub API for recent pull-request review comments and issue comments from the configured `--rule-repo`. Recent commit subjects are optional low-confidence context and are fetched only when explicitly requested.

A comment is treated as a high-confidence rule only when:

- The GitHub `author_association` is `COLLABORATOR`, `MEMBER`, or `OWNER`; and
- The body contains normative review language such as `should`, `should not`, `please`, `do not`, `shall not`, `unnecessary`, `prefer`, `can be written`, `revert`, `keep`, or `remove`; and
- The body is relevant to proof style, trusted boundaries, comments, formatting, warnings, source parity, or verification hygiene.

Commit subjects are lower confidence than review comments. They are collected as context and may produce informational hints, but should not produce hard errors by themselves.

Successful refreshes are cached for 72 hours by default. Normal postprocess checks consume the cache without network access. When a cache is stale or missing, delegate a bounded `--refresh-only` operation to a subagent and continue the main workflow. GitHub failures must preserve the previous cache; do not retry, wait for a rate-limit reset, or block proof work.

## Severity

- `ERROR`: The change should not be submitted as-is.
- `WARN`: The change needs human review and usually should be fixed.
- `INFO`: Context for the final response or manual review.

Dynamic rules should default to `WARN` unless they match an existing hard static rule such as new cheating code or changes outside the verification scope.

## Automation Boundary

The scripts should not remove comments, rename functions, or rewrite specifications. The wrapper may delegate redundant-assert simplification to `kverus-strip` and run the configured formatter; assert simplification may edit proof code only by removing a proof `assert` when the configured verification command still succeeds. If no verification command is configured, simplification must run in dry-run mode.
