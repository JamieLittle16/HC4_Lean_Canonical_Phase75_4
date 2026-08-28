# HC4 Lean

Cumulative Lean formalisation for the HC4 programme, including the current A18/A19 canonical Smith/Rees/final-assembly development.

The repository has grown through many historical phases. **Do not use old `FORMALISATION_STATUS_PHASE*.md` files as the current proof map.** They are retained as historical checkpoints.

## Start here

The authoritative documentation hub is [`docs/README.md`](docs/README.md).

For current work, the key documents are:

- [`docs/CURRENT_STATE.md`](docs/CURRENT_STATE.md) — exact theorem-level current status and live frontier;
- [`docs/PROOF_PATHS.md`](docs/PROOF_PATHS.md) — branch-by-branch proof routes and exact file chains;
- [`docs/PROOF_ARCHITECTURE.md`](docs/PROOF_ARCHITECTURE.md) — mathematical architecture and the current global/local split;
- [`docs/CANONICAL_OWNERS.md`](docs/CANONICAL_OWNERS.md) — canonical owners for reusable definitions and theorem families;
- [`docs/GLOSSARY_AND_INVARIANTS.md`](docs/GLOSSARY_AND_INVARIANTS.md) — carrier/clock/provenance vocabulary and invariants;
- [`docs/MODULE_CATALOG.md`](docs/MODULE_CATALOG.md) — human map of subsystem and final-assembly module families;
- [`docs/HISTORICAL_AND_SUPERSEDED_ROUTES.md`](docs/HISTORICAL_AND_SUPERSEDED_ROUTES.md) — interpretation of older proved routes and superseded reductions;
- [`docs/PROOF_CHANGE_CHECKLIST.md`](docs/PROOF_CHANGE_CHECKLIST.md) — duplicate-avoidance, provenance, termination and compile checklist.

## Exhaustive per-file documentation

Generate the source-derived proof inventory with:

```bash
python3 tools/generate_proof_inventory.py
```

It produces:

- [`docs/generated/LEAN_MODULE_INDEX.md`](docs/generated/LEAN_MODULE_INDEX.md) — every Lean file, imports, reverse importers, module purpose, A18/A19 labels and declarations;
- [`docs/generated/DECLARATION_INDEX.md`](docs/generated/DECLARATION_INDEX.md) — declaration lookup and repeated declaration spellings;
- [`docs/generated/LOCAL_IMPORT_EDGES.md`](docs/generated/LOCAL_IMPORT_EDGES.md) — local import DAG.

CI checks that these generated files match the Lean checkout before building.

## Current architectural rules

- The global rank-one recursion is already owned by `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace` and is well founded on strict natural `rawDefect` decrease.
- Successful positive Rees steps are ordinary edges of that existing trace, not a second termination mechanism.
- A19.45 proves that positive reached rank-three geometry gives outer global macro progress; a globally terminal reached state is therefore at literal raw defect zero.
- The live local terminal is the producer-free zero strict-low carrier and its singular maximal top face.
- Older torus-balanced cross-facet affine-line infrastructure remains reusable, but the unrestricted zero-clock route uses the newer balance-free finite-support cross-facet/ray machinery.
- Source, presented, recentered, top-face, first-contact, lower-carrier and ray support witnesses must not be interchanged without an explicit transport theorem.
- Generic definitions live with their representation (`HC4.Polynomial`, `HC4.Newton`, `HC4.Valuation`, `HC4.RationalRigidity`) rather than with whichever downstream module consumes them most often.

Read `docs/CANONICAL_OWNERS.md` and search the generated declaration index before introducing a new generic-looking declaration.

## Build

Focused module:

```bash
lake env lean HC4/path/to/File.lean
```

Full project:

```bash
lake build
```

Certification snapshot where applicable:

```bash
./verify.sh
```

## Historical documents

`FORMALISATION_LEDGER.md`, `CERTIFICATION_STATUS.md`, and the numbered `FORMALISATION_STATUS_PHASE*.md` files are historical records. Their old “missing” lists are not authoritative for the current branch.