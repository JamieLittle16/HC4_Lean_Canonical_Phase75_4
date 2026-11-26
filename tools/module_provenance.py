#!/usr/bin/env python3
"""Date the actual final-proof module owners against the pre-Tang checkpoint.

Run after tools/summarise_proof_dependencies.py. Read-only Git queries;
writes the audit to proof-dependencies/module-provenance.tsv.
The baseline is a verified repository snapshot before our first recorded
discussion of Tang (2026-11-25 21:03 UTC), not a claim about paper priority.
"""
import csv
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "proof-dependencies"
BASE = "90b9d97e2937b34c12c2ab845a404048f4a3c4b1"

def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()

def tree(ref):
    files = {}
    for row in git("ls-tree", "-r", ref, "--", "HC4", "HC4.lean").splitlines():
        meta, path = row.split("\t", 1)
        mode, kind, blob = meta.split()
        if kind == "blob":
            files[path] = blob
    return files

def dates(path):
    fmt = "%aI%x09%cI%x09%H"
    added = git("log", "--follow", "--diff-filter=A", "--format=" + fmt, "HEAD", "--", path)
    latest = git("log", "-1", "--format=" + fmt, "HEAD", "--", path)
    return (added.splitlines()[-1].split("\t") if added else ["", "", ""],
            latest.split("\t") if latest else ["", "", ""])

def main():
    git("merge-base", "--is-ancestor", BASE, "HEAD")
    before, now = tree(BASE), tree("HEAD")
    with (OUT / "final-hc4-nodes.tsv").open(encoding="utf-8", newline="") as f:
        counts = Counter(r["module"] for r in csv.DictReader(f, delimiter="\t"))
    modules, declarations = Counter(), Counter()
    with (OUT / "module-provenance.tsv").open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(["module", "reachable_declarations", "baseline_status",
                    "first_recorded_author_date", "first_recorded_committer_date",
                    "first_recorded_addition", "last_author_date", "last_committer_date", "last_change"])
        for module, n in sorted(counts.items()):
            path = module.replace(".", "/") + ".lean"
            if path not in now:
                raise ValueError(f"Missing module source at HEAD: {path}")
            status = ("absent_at_baseline" if path not in before else
                      "unchanged_since_baseline" if before[path] == now[path]
                      else "changed_since_baseline")
            first, last = dates(path)
            w.writerow([module, n, status, *first, *last])
            modules[status] += 1
            declarations[status] += n
    print("Baseline:", BASE, git("show", "-s", "--format=%cI", BASE))
    print("HEAD:", git("rev-parse", "HEAD"))
    for status in sorted(modules):
        print(f"{status}: {modules[status]} modules, {declarations[status]} reachable declarations")
    print("Wrote", OUT / "module-provenance.tsv")
    print("Counts classify module snapshots, not the individual lemma's origin or mathematical novelty.")

if __name__ == "__main__":
    main()
