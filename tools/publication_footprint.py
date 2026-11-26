#!/usr/bin/env python3
"""Compare the actual final declaration graph with the source import closure.

This script is deliberately read-only with respect to Lean sources. It
writes lists and a report in proof-dependencies/. It does not claim that
declaration-unreachable modules can be deleted or that the import closure
is minimal. Run after the Lean dependency exporter and its summariser.
"""
from __future__ import annotations

import csv
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "proof-dependencies"
ENTRY = "HC4.FinalEquivalence"


def module_name(path):
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def strip_comments(source):
    # Preserve newlines, handle nested Lean block comments and string literals.
    out = []
    i = depth = 0
    quoted = False
    while i < len(source):
        c = source[i]
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif quoted:
            out.append(c)
            i += 1
            if c == "\\" and i < len(source):
                out.append(source[i])
                i += 1
            elif c == '"':
                quoted = False
        elif pair == "/-":
            out.append(" ")
            depth = 1
            i += 2
        elif pair == "--":
            j = source.find("\n", i)
            i = len(source) if j < 0 else j
        else:
            if c == '"':
                quoted = True
            out.append(c)
            i += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(out)


def imports(path):
    # This repository uses ordinary one-line Lean imports. Also handle
    # module-system visibility/meta prefixes and multiple names on a line.
    source = strip_comments(path.read_text(encoding="utf-8"))
    for line in source.splitlines():
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", line)
        if m:
            yield from m.group(1).split()


def main():
    paths = subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=ROOT, text=True
    ).split("\0")
    sources = {
        module_name(ROOT / p): ROOT / p for p in paths
        if p.endswith(".lean") and (p == "HC4.lean" or p.startswith("HC4/"))
    }
    closure, todo = set(), [ENTRY]
    while todo:
        m = todo.pop()
        if m in closure:
            continue
        closure.add(m)
        for dep in imports(sources[m]):
            if dep in sources:
                todo.append(dep)
            elif dep == "HC4" or dep.startswith("HC4."):
                raise ValueError(f"Unresolved local import {dep} in {m}")

    with (OUT / "final-hc4-nodes.tsv").open(encoding="utf-8", newline="") as f:
        used = {row["module"] for row in csv.DictReader(f, delimiter="\t")}
    missing = used - closure
    if missing:
        raise ValueError(f"Declaration owners missing from parsed import closure: {sorted(missing)}")
    groups = {
        "source-import-closure": closure,
        "declaration-owners": used,
        "import-only-modules": closure - used,
        "outside-import-closure": set(sources) - closure,
    }
    for name, modules in groups.items():
        (OUT / (name + ".txt")).write_text(
            "".join(m + "\n" for m in sorted(modules)), encoding="utf-8"
        )
    report = [
        "# Publication source footprint",
        "",
        f"Entry module: {ENTRY}",
        "",
        f"- Total HC4 source modules: {len(sources)}",
        f"- Final declaration owners: {len(used)}",
        f"- Static local import closure: {len(closure)}",
        f"- Imported modules without a reachable declaration: {len(closure - used)}",
        f"- Source modules outside the static import closure: {len(set(sources) - closure)}",
        "",
        "This is a static source-import diagnostic, not a certified minimal",
        "library. It handles the repository's ordinary one-line import syntax.",
        "Only a clean build of a separately staged subset can certify that",
        "the remaining files suffice. No Lean sources have been changed.",
    ]
    (OUT / "publication-footprint.md").write_text("\n".join(report) + "\n", encoding="utf-8")
    print("\n".join(report))


if __name__ == "__main__":
    main()
