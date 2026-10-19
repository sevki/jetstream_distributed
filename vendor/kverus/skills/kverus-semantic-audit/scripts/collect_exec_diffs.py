#!/usr/bin/env python3
"""Collect normalized executable-code diffs for Rust vs Verus audits."""

from __future__ import annotations

import argparse
import difflib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

VISIBILITY_RE = re.compile(r"\bpub(?:\([^)]*\))?")
SIGNATURE_RE = re.compile(
    r"^(?:(?:pub(?:\([^)]*\))?|unsafe|async|const|extern(?:\s+\"[^\"]+\")?)\s+)*"
    r"(?P<kind>fn|trait|struct|enum|union|type|const|static|mod)\s+"
    r"(?:mut\s+)?(?P<name>[A-Za-z_][A-Za-z0-9_]*)\b"
)
IMPL_RE = re.compile(r"\bimpl\b")
USE_RE = re.compile(r"\buse\s+(?P<name>.+?);?$")

KEY_TOKEN_FIELDS = (
    "visibility",
    "unsafe",
    "async",
    "const_fn",
    "extern",
    "abi",
    "mut_static",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rust-dir", required=True, type=Path)
    parser.add_argument("--verus-dir", required=True, type=Path)
    parser.add_argument("--out-dir", required=True, type=Path)
    return parser.parse_args()


def list_rs_files(root: Path) -> dict[str, Path]:
    files: dict[str, Path] = {}
    for path in root.rglob("*.rs"):
        if any(part in {".git", "target"} for part in path.parts):
            continue
        rel = path.relative_to(root).as_posix()
        files[rel] = path
    return files


def strip_line_comment(line: str) -> str:
    in_str = False
    escape = False
    for i, ch in enumerate(line):
        if escape:
            escape = False
            continue
        if ch == "\\":
            escape = True
            continue
        if ch == '"':
            in_str = not in_str
            continue
        if not in_str and line[i : i + 2] == "//":
            return line[:i]
    return line


def brace_delta(text: str) -> int:
    text = strip_line_comment(text)
    return text.count("{") - text.count("}")


def is_verus_noise(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return True
    if stripped.startswith("//"):
        return True
    if stripped in {"verus! {", "verus!"}:
        return True
    if stripped == "}":
        return True
    if stripped.startswith("#[verifier::"):
        return True
    if stripped.startswith("#[allow(") or stripped.startswith("#![allow("):
        return True
    if re.match(r"^(requires|ensures|invariant|decreases|recommends)\b", stripped):
        return True
    if stripped.startswith(
        ("requires ", "ensures ", "invariant ", "decreases ", "recommends ")
    ):
        return True
    return False


def starts_spec_like_block(line: str) -> bool:
    stripped = line.strip()
    if not stripped or stripped.startswith("//"):
        return False
    if "{" not in stripped:
        return False
    return bool(
        re.match(
            r"^(pub(\([^)]*\))?\s+)?(open\s+spec|closed\s+spec|spec|proof)\b",
            stripped,
        )
        or re.match(r"^(let\s+)?(tracked|ghost)\b", stripped)
    )


def normalize_code(path: Path) -> list[str]:
    normalized: list[str] = []
    skip_depth = 0

    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.rstrip()
        stripped = line.strip()

        if skip_depth > 0:
            skip_depth += brace_delta(line)
            if skip_depth <= 0:
                skip_depth = 0
            continue

        if starts_spec_like_block(line):
            skip_depth = brace_delta(line)
            if skip_depth < 0:
                skip_depth = 0
            continue

        if is_verus_noise(line):
            continue

        line = strip_line_comment(line).strip()
        if not line:
            continue

        line = re.sub(r"\b(exec|proof|spec)\s+fn\b", "fn", line)
        line = re.sub(r"\btracked\s+", "", line)
        line = re.sub(r"\bghost\s+", "", line)
        line = re.sub(r"\s+", " ", line)
        normalized.append(line)

    return normalized


def visibility_token(line: str) -> str:
    match = VISIBILITY_RE.search(line)
    return match.group(0) if match else "private"


def signature_tokens(line: str) -> dict[str, object]:
    abi_match = re.search(r'\bextern\s+"([^"]+)"', line)
    return {
        "visibility": visibility_token(line),
        "unsafe": bool(re.search(r"\bunsafe\b", line)),
        "async": bool(re.search(r"\basync\b", line)),
        "const_fn": bool(re.search(r"\bconst\s+fn\b", line)),
        "extern": bool(re.search(r"\bextern\b", line)),
        "abi": abi_match.group(1) if abi_match else None,
        "mut_static": bool(re.search(r"\bstatic\s+mut\b", line)),
    }


def extract_key_token_index(lines: list[str]) -> dict[str, dict[str, object]]:
    """Extract critical declaration tokens from normalized executable lines.

    This is intentionally lightweight. The goal is to flag review targets such
    as `unsafe fn` becoming `fn` or `pub(crate)` becoming `pub`; the auditor
    should inspect the source directly before final classification.
    """

    index: dict[str, dict[str, object]] = {}
    seen: dict[str, int] = {}

    for line_no, line in enumerate(lines, start=1):
        match = SIGNATURE_RE.search(line)
        if match:
            kind = match.group("kind")
            name = match.group("name")
        elif use_match := USE_RE.search(line):
            kind = "use"
            name = use_match.group("name")
        elif IMPL_RE.search(line):
            kind = "impl"
            name = re.sub(r"\s*\{.*$", "", line)
        else:
            continue

        base_key = f"{kind}:{name}"
        ordinal = seen.get(base_key, 0) + 1
        seen[base_key] = ordinal
        key = f"{base_key}#{ordinal}"
        index[key] = {
            "kind": kind,
            "name": name,
            "line": line_no,
            "text": line,
            "tokens": signature_tokens(line),
        }

    return index


def key_token_changes(
    rust_norm: list[str], verus_norm: list[str]
) -> list[dict[str, object]]:
    rust_index = extract_key_token_index(rust_norm)
    verus_index = extract_key_token_index(verus_norm)
    changes: list[dict[str, object]] = []

    for key in sorted(set(rust_index) & set(verus_index)):
        rust_item = rust_index[key]
        verus_item = verus_index[key]
        changed = {
            field: {
                "rust": rust_item["tokens"][field],
                "verus": verus_item["tokens"][field],
            }
            for field in KEY_TOKEN_FIELDS
            if rust_item["tokens"][field] != verus_item["tokens"][field]
        }
        if changed:
            changes.append(
                {
                    "key": key,
                    "kind": rust_item["kind"],
                    "name": rust_item["name"],
                    "rust_line": rust_item["line"],
                    "verus_line": verus_item["line"],
                    "rust_text": rust_item["text"],
                    "verus_text": verus_item["text"],
                    "changes": changed,
                }
            )

    return changes


def safe_report_name(rel_path: str) -> str:
    return rel_path.replace("/", "__") + ".md"


def write_file_diff(
    rel_path: str,
    rust_path: Path,
    verus_path: Path,
    rust_norm: list[str],
    verus_norm: list[str],
    token_changes: list[dict[str, object]],
    out_file: Path,
) -> None:
    diff = "\n".join(
        difflib.unified_diff(
            rust_norm,
            verus_norm,
            fromfile=f"rust/{rel_path}",
            tofile=f"verus/{rel_path}",
            lineterm="",
        )
    )
    out_file.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        f"# Executable Diff: `{rel_path}`",
        "",
        f"- Rust: `{rust_path}`",
        f"- Verus: `{verus_path}`",
        "",
        "This is a normalized diff intended to guide semantic review. Inspect the source files directly before final classification.",
        "",
    ]
    if token_changes:
        lines.extend(["## Key Token Changes", ""])
        for change in token_changes:
            changed_fields = ", ".join(sorted(change["changes"].keys()))
            lines.extend(
                [
                    f"- `{change['key']}` changed `{changed_fields}`",
                    f"  - Rust: `{change['rust_text']}`",
                    f"  - Verus: `{change['verus_text']}`",
                ]
            )
        lines.append("")
    lines.extend(["```diff", diff, "```", ""])
    out_file.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    rust_dir = args.rust_dir.resolve()
    verus_dir = args.verus_dir.resolve()
    out_dir = args.out_dir.resolve()

    if not rust_dir.is_dir():
        raise SystemExit(f"rust-dir is not a directory: {rust_dir}")
    if not verus_dir.is_dir():
        raise SystemExit(f"verus-dir is not a directory: {verus_dir}")

    out_dir.mkdir(parents=True, exist_ok=True)
    diff_dir = out_dir / "file_diffs"
    diff_dir.mkdir(parents=True, exist_ok=True)

    rust_files = list_rs_files(rust_dir)
    verus_files = list_rs_files(verus_dir)
    all_rel_paths = sorted(set(rust_files) | set(verus_files))

    files = []
    for rel_path in all_rel_paths:
        rust_path = rust_files.get(rel_path)
        verus_path = verus_files.get(rel_path)
        entry = {
            "path": rel_path,
            "rust_path": str(rust_path) if rust_path else None,
            "verus_path": str(verus_path) if verus_path else None,
            "status": "matched",
            "has_exec_diff": False,
            "has_key_token_diff": False,
            "key_token_changes": [],
            "diff_report": None,
        }

        if rust_path is None:
            entry["status"] = "missing-rust"
        elif verus_path is None:
            entry["status"] = "missing-verus"
        else:
            rust_norm = normalize_code(rust_path)
            verus_norm = normalize_code(verus_path)
            token_changes = key_token_changes(rust_norm, verus_norm)
            entry["has_key_token_diff"] = bool(token_changes)
            entry["key_token_changes"] = token_changes
            if rust_norm != verus_norm:
                report = diff_dir / safe_report_name(rel_path)
                write_file_diff(
                    rel_path,
                    rust_path,
                    verus_path,
                    rust_norm,
                    verus_norm,
                    token_changes,
                    report,
                )
                entry["has_exec_diff"] = True
                entry["diff_report"] = str(report)

        files.append(entry)

    index = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "rust_dir": str(rust_dir),
        "verus_dir": str(verus_dir),
        "out_dir": str(out_dir),
        "totals": {
            "rust_files": len(rust_files),
            "verus_files": len(verus_files),
            "matched_files": sum(1 for f in files if f["status"] == "matched"),
            "missing_rust": sum(1 for f in files if f["status"] == "missing-rust"),
            "missing_verus": sum(1 for f in files if f["status"] == "missing-verus"),
            "files_with_exec_diff": sum(1 for f in files if f["has_exec_diff"]),
            "files_with_key_token_diff": sum(
                1 for f in files if f.get("has_key_token_diff")
            ),
        },
        "files": files,
    }

    (out_dir / "audit_index.json").write_text(
        json.dumps(index, indent=2), encoding="utf-8"
    )
    (out_dir / "README.audit.txt").write_text(
        "Generated by collect_exec_diffs.py. Review audit_index.json and file_diffs/*.md, then write semantic audit reports.\n",
        encoding="utf-8",
    )

    print(json.dumps(index["totals"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
