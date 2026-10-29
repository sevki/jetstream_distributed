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
  `protocol` every model fills in, `temporal`, the `compose`, `membership` and `identity`
  contracts). Adding an edge from one of them to anything else fails here, which is
  the point: that is a decision, and it is made by editing these sets in the same
  change, where a reviewer sees it.
* **The vocabulary stays a vocabulary.** A shape module may depend only on other shape
  modules, so that "depends on the contract" never smuggles in a dependency on a
  protocol.
* **The extraction is not blind.** Every edge in `KNOWN_EDGES` must be found. A
  pattern that stops matching would otherwise report "no cycle" for any graph, and
  the first version of this check, written by hand, did exactly that.

Comments are ignored, a `cfg` gate is not (an edge behind a feature is an edge), and
a grouped import (`use crate::{ a::X, b::Y }`) counts for each module it names.

Exits non-zero, listing each problem, if any check fails.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "src"

# Modules that stand alone: each may depend only on VOCABULARY.
STANDALONE = {"ownership", "raft", "raymond", "swim"}

# `id`, and the modules that only describe shapes and import no protocol. A name
# here that is not (yet) a module of `src/lib.rs` is fine; one that is must obey.
VOCABULARY = {"id", "protocol", "temporal", "compose", "membership", "identity"}

# Edges that are true today and that the extraction must find. If one of these
# stops being true, edit it out here; if the check stops finding one that is true,
# the check is broken.
KNOWN_EDGES = {
    ("composed", "ownership"),
    ("composed", "raymond"),
    ("scheduling", "compute"),
    ("actor", "ownership"),
}

MOD_DECL = re.compile(r"^\s*pub\s+mod\s+(\w+)\s*;")
PATH_ATTR = re.compile(r'^\s*#\[path\s*=\s*"([^"]+)"\s*\]')
CRATE_PATH = re.compile(r"\bcrate::(\w+)")
CRATE_GROUP = re.compile(r"\bcrate::\{")


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


def strip_comments(text: str) -> str:
    """The text with `//` comments and `/* */` comments removed, strings kept."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    out = []
    for line in text.splitlines():
        in_str = False
        escaped = False
        cut = len(line)
        for i, ch in enumerate(line):
            if in_str:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_str = False
            elif ch == '"':
                in_str = True
            elif ch == "/" and line[i : i + 2] == "//":
                cut = i
                break
        out.append(line[:cut])
    return "\n".join(out)


def group_targets(text: str) -> set[str]:
    """The modules named at the top level of each `crate::{ ... }` group."""
    targets: set[str] = set()
    for m in CRATE_GROUP.finditer(text):
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


def graph(mods: dict[str, list[Path]]) -> dict[str, dict[str, set[str]]]:
    """module -> {module it depends on -> where}."""
    edges: dict[str, dict[str, set[str]]] = {m: {} for m in mods}
    for name, files in mods.items():
        for f in files:
            if not f.exists():
                continue
            text = strip_comments(f.read_text())
            targets = set(CRATE_PATH.findall(text)) | group_targets(text)
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
