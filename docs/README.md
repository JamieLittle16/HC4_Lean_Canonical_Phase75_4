# HC4 Lean documentation hub

This directory is the **authoritative navigation layer** for the current HC4 Lean development.

The repository has grown through many cumulative phases and now contains a large amount of reusable algebraic, Newton-geometric, RationalRigidity, and valuation/state-machine infrastructure. Historical `FORMALISATION_STATUS_PHASE*.md` files at the repository root record useful checkpoints, but they are **not current architecture documents** and must not be used to decide whether infrastructure already exists.

## Read these first

1. [`PROOF_ARCHITECTURE.md`](PROOF_ARCHITECTURE.md) — the mathematical and Lean proof paths from an unrestricted collision to the current terminal frontier.
2. [`CANONICAL_OWNERS.md`](CANONICAL_OWNERS.md) — where important concepts, structures, and helper APIs are defined. Check this before introducing a new definition or theorem family.
3. [`PROOF_CHANGE_CHECKLIST.md`](PROOF_CHANGE_CHECKLIST.md) — required workflow before adding new proof infrastructure.
4. [`MODULE_CATALOG.md`](MODULE_CATALOG.md) — human-oriented map of module families and the active A18/A19 final-assembly chain.
5. [`generated/README.md`](generated/README.md) — specification for the exhaustive machine-generated module, declaration, and import-DAG indexes.

Generate or refresh the exhaustive indexes with:

```bash
python3 tools/generate_proof_inventory.py
```

This writes:

- `docs/generated/LEAN_MODULE_INDEX.md`
- `docs/generated/DECLARATION_INDEX.md`
- `docs/generated/LOCAL_IMPORT_EDGES.md`

If generated indexes are committed in a checkout, check that they are current with:

```bash
python3 tools/generate_proof_inventory.py --check
```

The generator uses only the Python standard library and scans the Lean source tree. It records every module's imports, module documentation title, A18/A19 labels, declarations, and reverse importers. This is the reproducible source of truth for **every file**, while the hand-written documents explain how those files fit together mathematically.

## Documentation authority

When documents disagree, use this order:

1. Lean source and its imports/types.
2. Generated module/declaration indexes, when freshly generated.
3. These `docs/` architecture documents.
4. Current PR description and commit history.
5. Historical phase-status files.

A green build proves only that the imported development elaborates. It does not by itself mean that every historical manuscript goal or the unrestricted HC4 theorem has been closed. The architecture document distinguishes verified infrastructure, reductions, and the current live frontier.

## Repository areas

The major proof domains are:

- `HC4/Polynomial/` — polynomial representations, weighted initial forms, support predicates, substitutions, rank-three line/pencil realisations, and univariate reconstruction.
- `HC4/Toric/` — four-variable toric exponents, facets, rays, balance arithmetic, and boundary combinatorics.
- `HC4/Newton/` — finite-support Newton selection, first contact, exposed vertices, cross-facet carriers, boundary strata, Schur/Hessian local geometry, and endpoint transitions.
- `HC4/RationalRigidity/` — rank-three rational/projective rigidity, autonomous-polynomial reductions, fixed-direction/fixed-point contradictions, and terminal line obstructions.
- `HC4/Valuation/` — scale-aware states, Smith/Schur episodes, restart/progress machinery, Rees constructions, provenance, rank-one termination, and final A18/A19 assembly.
- `HC4/LinearAlgebra/`, `HC4/MongeAmpere/`, `HC4/FacetRigidity/`, `HC4/ClassifiedFamilies/`, `HC4/QuasiTranslation/` — reusable foundational and older classification layers.
- `HC4.lean` — root aggregator. Its explicit final-assembly imports are useful CI coverage, but the generated import graph is the better navigation tool.

## Maintenance rule

Every new substantial Lean module should contain a `/-! ... -/` module docstring stating:

- the mathematical purpose;
- what previous theorem/module it consumes;
- what exact interface it exports;
- which hypotheses it deliberately does **not** add;
- whether it is a generic reusable lemma, a carrier/adapter, a reduction, a contradiction, or an assembly theorem.

If a new module creates a concept that future work is likely to reuse, add it to `CANONICAL_OWNERS.md`. If it changes the live proof path, update `PROOF_ARCHITECTURE.md` and `MODULE_CATALOG.md` in the same commit.