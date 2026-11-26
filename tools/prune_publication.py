#!/usr/bin/env python3
"""First-stage publication pruning: preserve the actual local import closure.

Dry run by default. --apply stages deletion of unreachable HC4 source
modules, replaces the research umbrella and audit with focused entry points,
and leaves all non-HC4 files alone. It never changes retained proof modules.
The archive branch preserves the research snapshot. Rebuild before committing.
"""
from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

from publication_footprint import imports

ROOT = Path(__file__).resolve().parents[1]
ROOTS = (
    "HC4.FinalEquivalence",
    "HC4.Polynomial.RationalMapAffinePlane",
)
BRANCH = "publication/palomar"
ARCHIVE = "origin/archive/research-2026"
SNAPSHOT = "fe55e3fbb6da0b034f8dd2cc434d262047533ed7"
AUDIT_NAMES = (
    "HC4.Polynomial.hc4_of_planarJC2",
    "HC4.StatementAudit.planarJC2_iff_hessianFour_injective",
    "HC4.StatementAudit.referenceJC2_iff_referenceHC4",
    "HC4.StatementAudit.jc2_iff_hc4_explicit",
    "HC4.Polynomial.RankThreeCubic.rationalMap_affinePlane",
)


def git(*args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=ROOT, text=True
    ).strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true",
                        help="stage pruning on publication/palomar only")
    args = parser.parse_args()
    paths = git("ls-files", "-z").split("\0")
    sources = {
        ".".join(Path(p).with_suffix("").parts): ROOT / p
        for p in paths
        if p.endswith(".lean") and (p == "HC4.lean" or p.startswith("HC4/"))
    }
    if not sources:
        raise SystemExit("No tracked HC4 modules found")
    closure: set[str] = set()
    todo = list(ROOTS)
    while todo:
        name = todo.pop()
        if name in closure:
            continue
        if name not in sources:
            raise SystemExit(f"Missing local module: {name}")
        if name in ("HC4", "HC4.Audit"):
            raise SystemExit(f"Proof imports research umbrella/audit: {name}")
        closure.add(name)
        for dep in imports(sources[name]):
            if dep == "HC4" or dep.startswith("HC4."):
                if dep not in sources:
                    raise SystemExit(f"Unresolved import {dep} in {name}")
                todo.append(dep)

    keep = closure | {"HC4", "HC4.Audit"}
    remove = sorted(str(sources[m].relative_to(ROOT))
                    for m in sources.keys() - keep)
    print(f"Tracked HC4 source modules: {len(sources)}")
    print(f"Transitive proof import closure: {len(closure)}")
    print(f"Retained including new umbrella and audit: {len(keep)}")
    print(f"Removable research modules: {len(remove)}")
    print("Non-HC4 tracked Lean files (not pruned):")
    for p in paths:
        if p.endswith(".lean") and p != "HC4.lean" and not p.startswith("HC4/"):
            print(f"  {p}")
    out = ROOT / "proof-dependencies"
    out.mkdir(exist_ok=True)
    (out / "publication-retained-modules.txt").write_text(
        "".join(m + "\n" for m in sorted(keep)), encoding="utf-8")
    (out / "publication-removable-files.txt").write_text(
        "".join(p + "\n" for p in remove), encoding="utf-8")
    if not args.apply:
        print("Dry run only: no tracked files changed.")
        return

    if git("branch", "--show-current") != BRANCH:
        raise SystemExit(f"Refusing to prune outside {BRANCH}")
    if git("status", "--porcelain", "--untracked-files=no"):
        raise SystemExit("Commit or restore tracked changes before pruning.")
    if git("rev-parse", ARCHIVE) != SNAPSHOT:
        raise SystemExit("Archive ref does not match the preserved snapshot; fetch/check it.")
    subprocess.run(["git", "merge-base", "--is-ancestor", SNAPSHOT, "HEAD"],
                   cwd=ROOT, check=True)
    # Ensure every removed source has the same archived content.
    archive_paths = set(git("ls-tree", "-r", "--name-only", SNAPSHOT).splitlines())
    for p in remove:
        if p not in archive_paths:
            raise SystemExit(f"Not archived: {p}")
    changed = set(git("diff", "--name-only", SNAPSHOT, "HEAD", "--",
                      "HC4", "HC4.lean").splitlines())
    if changed.intersection(remove):
        raise SystemExit("Some proposed deletions differ from archived sources.")
    for i in range(0, len(remove), 150):
        subprocess.run(["git", "rm", "--", *remove[i:i + 150]],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    (ROOT / "HC4.lean").write_text(
        "".join(f"import {m}\n" for m in ROOTS), encoding="utf-8")
    audit = ["import HC4", "import Lean.Util.CollectAxioms", ""]
    audit += [f"#print axioms {name}" for name in AUDIT_NAMES]
    audit += ["", "run_cmd do",
              "  let allowed : List Lean.Name := [" + chr(96)*2 +
              "propext, " + chr(96)*2 + "Classical.choice, " +
              chr(96)*2 + "Quot.sound]",
              "  for decl in [" + ",\n      ".join(chr(96)*2 + n for n in AUDIT_NAMES) + "] do",
              "    for dep in (← Lean.collectAxioms decl) do",
              "      unless allowed.contains dep do",
              '        throwError "Unexpected logical dependency {dep} in {decl}"', ""]
    (ROOT / "HC4/Audit.lean").write_text("\n".join(audit), encoding="utf-8")
    git("add", "--", "HC4.lean", "HC4/Audit.lean")
    print("Pruning staged. No retained proof module changed.")
    print("Remove project .lake/build, rebuild, then run the focused audit before committing.")


if __name__ == "__main__":
    main()
