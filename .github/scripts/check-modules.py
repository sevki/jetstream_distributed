#!/usr/bin/env python3
"""Check the crate's module layering before anything is built.

The repository's claim is that each protocol stands alone and composes. A cycle
between modules compiles, so nothing else stops one appearing, which is how three
of them hid (`compute`/`scheduling`, and `ownership` with both `raymond` and
`composed`). This reads the `use crate::...` lines and the `crate::...` paths in
`src/`, builds the graph whose nodes are the modules `src/lib.rs` declares, and
checks, without building or a network:

* **No cycle.** No two modules depend on each other, directly or through others.
* **Standalone modules stay standalone.** The modules in `STANDALONE` may depend
  only on `VOCABULARY`: `id` and the modules that only describe shapes (the
  `protocol` every model fills in, `temporal`, the `compose` and `membership`
  contracts). Adding an edge from one of them to anything else fails here, which is
  the point: that is a decision, and it is made by editing these sets in the same
  change, where a reviewer sees it.
* **The vocabulary stays a vocabulary.** A shape module may depend only on other shape
  modules, so that "depends on the contract" never smuggles in a dependency on a
  protocol.
* **The extraction is not blind.** Every edge in `KNOWN_EDGES` must be found. A
  pattern that stops matching would otherwise report "no cycle" for any graph, and
  the first version of this check, written by hand, did exactly that.

Comments are ignored (block comments nest, as in Rust), a `cfg` gate is not (an edge
behind a feature is an edge), and a grouped import (`use crate::{ a::X, b::Y }`)
counts for each module it names. A relative path (`super::raymond::X`, `super::super::
{a::X}`) is resolved against the module its file is in, so it counts exactly when the
`crate::` spelling of the same path would.

Exits non-zero, listing each problem, if any check fails.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "src"

# Modules that stand alone: each may depend only on VOCABULARY.
STANDALONE = {"ownership", "raft", "swim"}

# `id`, and the modules that only describe shapes and import no protocol. A name
# here that is not (yet) a module of `src/lib.rs` is fine; one that is must obey.
VOCABULARY = {"id", "protocol", "temporal", "compose", "membership"}

# Edges that are true today and that the extraction must find. If one of these
# stops being true, edit it out here; if the check stops finding one that is true,
# the check is broken.
KNOWN_EDGES = {
    ("composed", "ownership"),
    ("composed", "raymond"),
    ("raymond", "ownership"),
    ("scheduling", "compute"),
    ("actor", "ownership"),
}

MOD_DECL = re.compile(r"^\s*pub\s+mod\s+(\w+)\s*;")
PATH_ATTR = re.compile(r'^\s*#\[path\s*=\s*"([^"]+)"\s*\]')
CRATE_PATH = re.compile(r"\bcrate::(\w+)")
CRATE_GROUP = re.compile(r"\bcrate::\{")
# `super::super::name` (not preceded by `::`, so a path in the middle of another is
# not read from its tail), and the same followed by a group.
SUPER_PATH = re.compile(r"(?<![\w:])((?:super::)+)(\w+)")
SUPER_GROUP = re.compile(r"(?<![\w:])(?:super::)+\{")


def modules() -> dict[str, list[Path]]:
    """The modules `src/lib.rs` declares, as name -> the files that are in them."""
    found: dict[str, list[Path]] = {}
    path_attr = None
    for line in (SRC / "lib.rs").read_text().splitlines():
        m = PATH_ATTR.match(line)
        if m:
            path_attr = m.group(1)
            continue
        m = MOD_DECL.match(line)
        if m:
            name = m.group(1)
            if path_attr is not None:
                files = [SRC / path_attr]
            elif (SRC / name).is_dir():
                files = sorted((SRC / name).rglob("*.rs"))
            else:
                files = [SRC / f"{name}.rs"]
            found[name] = files
            path_attr = None
        elif not line.strip().startswith("#["):
            path_attr = None
    return found


CHAR_LITERAL = re.compile(r"'(?:\\.[^']*|[^\\'])'")


def strip_comments(text: str) -> str:
    """The text with `//` comments and (nesting) `/* */` comments removed.

    Strings and character literals are kept, and what is inside them is not read
    as a comment.
    """
    out = []
    i = 0
    n = len(text)
    while i < n:
        two = text[i : i + 2]
        ch = text[i]
        if two == "//":
            while i < n and text[i] != "\n":
                i += 1
        elif two == "/*":
            depth = 1
            i += 2
            while i < n and depth:
                if text[i : i + 2] == "/*":
                    depth += 1
                    i += 2
                elif text[i : i + 2] == "*/":
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
        elif ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i : j + 1])
            i = j + 1
        elif ch == "'":
            m = CHAR_LITERAL.match(text, i)
            if m:
                out.append(m.group(0))
                i = m.end()
            else:
                out.append(ch)
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def group_targets(text: str, opener: "re.Pattern[str]" = CRATE_GROUP) -> set[str]:
    """The names at the top level of each group that `opener` matches the start of."""
    targets: set[str] = set()
    for m in opener.finditer(text):
        depth = 1
        i = m.end()
        item = []
        while i < len(text) and depth:
            ch = text[i]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    break
            if depth == 1 and ch == ",":
                targets.add("".join(item).strip())
                item = []
            elif depth == 1:
                item.append(ch)
            i += 1
        targets.add("".join(item).strip())
    heads = set()
    for t in targets:
        h = re.match(r"(\w+)", t)
        if h:
            heads.add(h.group(1))
    return heads


def depth(f: Path) -> int:
    """How many modules deep the module a file defines is, the crate root being 0.

    `src/ownership/mod.rs` is `ownership`, 1; `src/ownership/model_t.rs` and
    `src/ownership/proofs/mod.rs` are 2; a file directly in `src/` is 1.
    """
    parts = f.relative_to(SRC).parts
    if len(parts) == 1:
        return 1
    return len(parts) - 1 if f.stem == "mod" else len(parts)


def relative_targets(text: str, d: int) -> set[str]:
    """The top-level modules that `super::` paths in a file at depth `d` reach."""
    targets: set[str] = set()
    for m in SUPER_PATH.finditer(text):
        if d - m.group(1).count("super") == 0:
            targets.add(m.group(2))
    # A group's supers are counted from the text before its brace.
    for m in SUPER_GROUP.finditer(text):
        if d - m.group(0).count("super") == 0:
            lone = re.compile(re.escape(m.group(0)))
            targets |= group_targets(text[m.start() :], lone)
    return targets


def graph(mods: dict[str, list[Path]]) -> dict[str, dict[str, set[str]]]:
    """module -> {module it depends on -> where}."""
    edges: dict[str, dict[str, set[str]]] = {m: {} for m in mods}
    for name, files in mods.items():
        for f in files:
            if not f.exists():
                continue
            text = strip_comments(f.read_text())
            targets = set(CRATE_PATH.findall(text)) | group_targets(text)
            targets |= relative_targets(text, depth(f))
            for t in targets:
                if t in mods and t != name:
                    edges[name].setdefault(t, set()).add(str(f.relative_to(ROOT)))
    return edges


def cycles(edges: dict[str, dict[str, set[str]]]) -> list[list[str]]:
    """The strongly connected components with more than one module (Tarjan)."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on: set[str] = set()
    stack: list[str] = []
    out: list[list[str]] = []
    counter = [0]

    def visit(v: str) -> None:
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in edges[v]:
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                out.append(sorted(comp))

    for v in sorted(edges):
        if v not in index:
            visit(v)
    return out


def main() -> int:
    problems: list[str] = []
    mods = modules()
    edges = graph(mods)

    for src, dst in sorted(KNOWN_EDGES):
        if dst not in edges.get(src, {}):
            problems.append(
                f"the check did not find the edge {src} -> {dst}, which is true: "
                "either the extraction is broken or KNOWN_EDGES is stale"
            )

    for comp in cycles(edges):
        detail = []
        for a in comp:
            for b in comp:
                if b in edges[a]:
                    where = sorted(edges[a][b])[0]
                    detail.append(f"    {a} -> {b}  ({where})")
        problems.append("modules depend on each other: " + ", ".join(comp) + "\n" + "\n".join(detail))

    for m in sorted(STANDALONE):
        if m not in mods:
            problems.append(f"STANDALONE names {m}, which is not a module of src/lib.rs")
            continue
        for dep, where in sorted(edges[m].items()):
            if dep not in VOCABULARY:
                problems.append(
                    f"{m} is standalone but depends on {dep} ({sorted(where)[0]}); "
                    f"it may use only {sorted(VOCABULARY)}"
                )

    for m in sorted(VOCABULARY & set(mods)):
        for dep, where in sorted(edges[m].items()):
            if dep not in VOCABULARY:
                problems.append(
                    f"{m} only describes a shape but depends on {dep} ({sorted(where)[0]}); "
                    f"a shape module may use only {sorted(VOCABULARY)}"
                )

    if problems:
        print(f"{len(problems)} problem(s):")
        for p in problems:
            print(f"* {p}")
        return 1
    n = sum(len(v) for v in edges.values())
    print(f"module graph ok: {len(mods)} modules, {n} edges, no cycle")
    return 0


if __name__ == "__main__":
    sys.exit(main())
