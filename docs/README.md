# HC4 Lean documentation hub

This directory is the authoritative navigation layer for the current HC4 Lean development. The repository is cumulative, so documentation is split by responsibility rather than duplicating one giant status file.

## Core documents

1. [`CURRENT_STATE.md`](CURRENT_STATE.md) — **current theorem-level status**. Read this first to see what is closed, what is superseded, and the exact live frontier before unrestricted HC4.
2. [`PROOF_PATHS.md`](PROOF_PATHS.md) — **branch-by-branch route map** from the carrier/hypotheses you have to the next canonical Lean interface. Includes the full A19.49–A19.70 chain, global termination, Rees, balanced affine RationalRigidity, confinement, codimension-two and planar/JC2 routes.
3. [`PROOF_ARCHITECTURE.md`](PROOF_ARCHITECTURE.md) — **mathematical architecture**: unrestricted entry, the single raw-defect recursion, A19.45 global/local split, zero-clock terminal architecture, balance-free Newton geometry and RationalRigidity boundaries.
4. [`CANONICAL_OWNERS.md`](CANONICAL_OWNERS.md) — **reuse registry**. Check this before introducing a generic definition, structure, support filter, state transition, or theorem family.
5. [`GLOSSARY_AND_INVARIANTS.md`](GLOSSARY_AND_INVARIANTS.md) — **carrier and invariant glossary**. Distinguishes source/presented/recentered/top-face/first-contact/ray objects, clocks, repair provenance, balance, homogeneity and planar/codimension-two terminology.
6. [`MODULE_CATALOG.md`](MODULE_CATALOG.md) — **human subsystem catalog** for `Polynomial`, `Toric`, `Newton`, `RationalRigidity`, `Valuation`, JC2 bridges and older reusable layers.
7. [`HISTORICAL_AND_SUPERSEDED_ROUTES.md`](HISTORICAL_AND_SUPERSEDED_ROUTES.md) — **old-route map**. Explains which older proved interfaces are reusable alternatives, superseded reductions, or merely historical checkpoints.
8. [`PROOF_CHANGE_CHECKLIST.md`](PROOF_CHANGE_CHECKLIST.md) — **pre-patch checklist** for duplicate avoidance, provenance, termination and integration checks.

## Exhaustive generated indexes

Run:

```bash
python3 tools/generate_proof_inventory.py
```

This generates directly from the Lean checkout:

- [`generated/LEAN_MODULE_INDEX.md`](generated/LEAN_MODULE_INDEX.md) — every Lean module, path, module-doc purpose, A18/A19 labels, direct imports, reverse importers and declarations;
- [`generated/DECLARATION_INDEX.md`](generated/DECLARATION_INDEX.md) — declaration-to-module lookup with repeated spellings highlighted;
- [`generated/LOCAL_IMPORT_EDGES.md`](generated/LOCAL_IMPORT_EDGES.md) — the local import DAG adjacency list.

CI checks freshness with:

```bash
python3 tools/generate_proof_inventory.py --check
```

## Before writing new infrastructure

Use this order:

```text
CURRENT_STATE
  -> is the gap actually still live?
PROOF_PATHS
  -> is there already a route from this exact carrier?
CANONICAL_OWNERS
  -> who owns the concept?
DECLARATION_INDEX
  -> does the spelling already exist?
LEAN_MODULE_INDEX
  -> search mathematical synonyms and reverse importers
Lean source
  -> compare exact types, carriers and hypotheses
```

Only then introduce a new generic owner.

## Documentation authority

When documents disagree:

1. Lean source and elaborated theorem types;
2. fresh generated indexes;
3. `CURRENT_STATE.md`;
4. `PROOF_PATHS.md` and `PROOF_ARCHITECTURE.md`;
5. `CANONICAL_OWNERS.md` and `GLOSSARY_AND_INVARIANTS.md`;
6. current PR/commit history;
7. historical phase-status files.

A green build means the imported development elaborates. It does not by itself mean unrestricted HC4 is complete.

## Maintenance rule

Every substantial new Lean module should document: **carrier, consumes, produces, preserves, does not assume, and role** (owner/carrier/adapter/split/reduction/closure/contradiction).

If a change alters the live frontier, update `CURRENT_STATE.md` and `PROOF_PATHS.md`. If it introduces reusable infrastructure, update `CANONICAL_OWNERS.md`. If it supersedes a route, update `HISTORICAL_AND_SUPERSEDED_ROUTES.md`. Regenerate the machine index whenever Lean source changes.

Root `FORMALISATION_STATUS_PHASE*.md`, `FORMALISATION_LEDGER.md`, and `CERTIFICATION_STATUS.md` are historical archaeology, not current missing-lemma lists.