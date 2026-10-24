#!/usr/bin/env python3
"""Check the book's links before it is built.

The book does not repeat the README's claims; it links to them. That only works if
the links keep pointing at something, so this checks, without a network:

* every chapter in `book/src/SUMMARY.md` exists, and every chapter is listed;
* every relative link between chapters resolves, and so does its `#anchor`;
* every link to `README.md#anchor` names a heading the README really has.

Exits non-zero, listing each problem, if any check fails.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "book" / "src"
README = ROOT / "README.md"
README_URL = "https://github.com/sevki/jetstream_distributed/blob/main/README.md"

HEADING = re.compile(r"^(#{1,6})\s+(.*?)\s*#*\s*$")
LINK = re.compile(r"\]\(([^)\s]+)\)")


def slug(text: str) -> str:
    """The anchor GitHub and mdBook both give a heading."""
    text = re.sub(r"`", "", text)
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = text.strip().lower()
    text = re.sub(r"[^\w\- ]", "", text)
    return text.replace(" ", "-")


def anchors(path: Path) -> set[str]:
    """Every heading anchor in `path`, with repeats numbered as GitHub does."""
    seen: dict[str, int] = {}
    found: set[str] = set()
    fenced = False
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.lstrip().startswith("```"):
            fenced = not fenced
            continue
        if fenced:
            continue
        m = HEADING.match(line)
        if not m:
            continue
        base = slug(m.group(2))
        n = seen.get(base, 0)
        seen[base] = n + 1
        found.add(base if n == 0 else f"{base}-{n}")
    return found


def links(path: Path):
    """Every link target in `path`, skipping fenced code."""
    fenced = False
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if line.lstrip().startswith("```"):
            fenced = not fenced
            continue
        if fenced:
            continue
        for m in LINK.finditer(line):
            yield number, m.group(1)


def main() -> int:
    problems: list[str] = []
    readme_anchors = anchors(README)

    summary = SRC / "SUMMARY.md"
    listed = {target for _, target in links(summary) if target.endswith(".md")}
    for target in sorted(listed):
        if not (SRC / target).is_file():
            problems.append(f"SUMMARY.md: {target} does not exist")
    for chapter in sorted(SRC.glob("*.md")):
        if chapter.name != "SUMMARY.md" and chapter.name not in listed:
            problems.append(f"{chapter.name}: not listed in SUMMARY.md")

    for chapter in sorted(SRC.glob("*.md")):
        for number, target in links(chapter):
            where = f"{chapter.name}:{number}"
            if target.startswith(README_URL):
                _, _, anchor = target.partition("#")
                if anchor and anchor not in readme_anchors:
                    problems.append(f"{where}: README has no heading #{anchor}")
            elif "://" in target or target.startswith("mailto:"):
                continue
            else:
                name, _, anchor = target.partition("#")
                if not name:
                    if anchor and anchor not in anchors(chapter):
                        problems.append(f"{where}: no heading #{anchor} in this page")
                    continue
                dest = SRC / name
                if not dest.is_file():
                    problems.append(f"{where}: {name} does not exist")
                elif anchor and anchor not in anchors(dest):
                    problems.append(f"{where}: {name} has no heading #{anchor}")

    for problem in problems:
        print(problem)
    if problems:
        print(f"{len(problems)} problem(s)")
        return 1
    print(f"book links ok: {len(list(SRC.glob('*.md')))} files, "
          f"{len(readme_anchors)} README anchors known")
    return 0


if __name__ == "__main__":
    sys.exit(main())
