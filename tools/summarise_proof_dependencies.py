#!/usr/bin/env python3
"""Summarise a Lean declaration dependency export (standard library only).

Run after: lake env lean tools/ExportProofDependencies.lean
Edges point from a declaration to the declaration it references.
The raw TSVs retain external and generated declarations and edge kinds.
The HC4-only projections retain direct edges with two HC4-owned endpoints.
"""
from __future__ import annotations

import csv
import json
from collections import Counter, defaultdict
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "proof-dependencies"
FINAL = "HC4.StatementAudit.jc2_iff_hc4_explicit"
CORE = "HC4.Polynomial.hc4_of_planarJC2"


def read_tsv(name):
    with (OUT / name).open(encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def write_tsv(name, fields, rows):
    with (OUT / name).open("w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f, delimiter="\t", lineterminator="\n")
        writer.writerow(fields)
        writer.writerows(rows)


def local(module):
    return module == "HC4" or module.startswith("HC4.")


def reachable(root, adj):
    seen, todo = set(), [root]
    while todo:
        n = todo.pop()
        if n not in seen:
            seen.add(n)
            todo.extend(adj[n] - seen)
    return seen


def dot(name, vertices, edges):
    with (OUT / name).open("w", encoding="utf-8") as f:
        f.write("digraph dependencies {\n  rankdir=LR;\n")
        for v in sorted(vertices):
            f.write(f"  {json.dumps(v, ensure_ascii=False)};\n")
        for a, b in sorted(edges):
            f.write(f"  {json.dumps(a, ensure_ascii=False)} -> {json.dumps(b, ensure_ascii=False)};\n")
        f.write("}\n")


def main():
    records = read_tsv("nodes.tsv")
    nodes = {row["declaration"]: row for row in records}
    if len(nodes) != len(records):
        raise ValueError("Duplicate node names")
    edges = {(r["source"], r["target"], r["relation"]) for r in read_tsv("edges.tsv")}
    adj = defaultdict(set)
    for a, b, _ in edges:
        if a not in nodes or b not in nodes:
            raise ValueError(f"Unresolved dependency: {a} -> {b}")
        adj[a].add(b)

    tracked = subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=ROOT, text=True
    ).split("\0")
    project_modules = {
        ".".join(Path(p).with_suffix("").parts) for p in tracked
        if p.endswith(".lean") and (p == "HC4.lean" or p.startswith("HC4/"))
    }
    local_all = {n for n, r in nodes.items() if local(r["module"])}
    lines = [
        "# Declaration dependency audit",
        "",
        "Reachability follows the constants in checked declaration types and values,",
        "including opaque values and inductive constructors, using Lean's axiom",
        "collection convention. This is not an import graph or a minimal proof.",
        "Edges point from a declaration to its dependency. Inductive dependencies",
        "can create cycles. Private/generated declarations are retained.",
        "",
    ]
    for label, root in [("final", FINAL), ("core", CORE)]:
        if root not in nodes:
            raise ValueError(f"Root missing: {root}")
        used = reachable(root, adj)
        own = used & local_all
        modules = {nodes[n]["module"] for n in own}
        local_edges = {(a, b, k) for a, b, k in edges if a in own and b in own}
        module_edges = {
            (nodes[a]["module"], nodes[b]["module"])
            for a, b, _ in local_edges if nodes[a]["module"] != nodes[b]["module"]
        }
        counts = Counter(nodes[n]["module"] for n in own)
        kinds = Counter(nodes[n]["kind"] for n in own)
        axioms = sorted(n for n in used if nodes[n]["kind"] == "axiom")
        lines.extend([
            f"## {label}: {root}", "",
            f"- Reachable declarations (all libraries): {len(used)}",
            f"- HC4-owned reachable declarations: {len(own)}",
            f"- HC4-owned defining modules: {len(modules)}",
            f"- HC4 source modules with no reachable declaration: {len(project_modules - modules)}",
            f"- HC4-only typed edges: {len(local_edges)}",
            f"- HC4 declaration kinds: {dict(sorted(kinds.items()))}",
            f"- Reachable axiom-kind declarations: {', '.join(axioms) or '(none)'}",
            "",
            "| Defining module | Reachable declarations |",
            "|---|---:|",
            *(f"| {m} | {count} |" for m, count in sorted(counts.items(), key=lambda p: (-p[1], p[0]))),
            "",
        ])
        write_tsv(f"{label}-hc4-nodes.tsv", ["declaration", "module", "kind"],
                  ((n, nodes[n]["module"], nodes[n]["kind"]) for n in sorted(own)))
        write_tsv(f"{label}-hc4-edges.tsv", ["source", "target", "relation"], sorted(local_edges))
        write_tsv(f"{label}-unused-modules.tsv", ["module"], ((m,) for m in sorted(project_modules - modules)))
        dot(f"{label}-hc4.dot", own, {(a, b) for a, b, _ in local_edges})
        dot(f"{label}-modules.dot", modules, module_edges)

    lines.extend([
        "## Interpretation",
        "",
        "Unused means no declaration from that source module was reached under",
        "this traversal. It does not mean the module can safely be removed:",
        "imports, notation, elaboration, tactics, instances and other declarations",
        "can still be needed to rebuild the source. Do not prune source files",
        "without separately testing a clean rebuild. The local graphs are",
        "induced subgraphs, not a transitive reduction or a mathematical outline.",
        "",
    ])
    (OUT / "summary.md").write_text("\n".join(lines), encoding="utf-8")
    print("\n".join(lines[:12]))
    print(f"Wrote {OUT / 'summary.md'} and HC4-only declaration/module graphs.")


if __name__ == "__main__":
    main()
