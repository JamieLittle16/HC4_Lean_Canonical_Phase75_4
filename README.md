# HC4 Lean

Cumulative Lean formalisation for the HC4 programme, including the current A18/A19 canonical Smith/Rees/final-assembly development.

The repository has grown through many historical phases. **Do not use old `FORMALISATION_STATUS_PHASE*.md` files as the current proof map.** They are retained as historical checkpoints.

## Start here

Current documentation lives in [`docs/README.md`](docs/README.md):

- [`docs/PROOF_ARCHITECTURE.md`](docs/PROOF_ARCHITECTURE.md) — mathematical proof routes and the live A18/A19 assembly chain.
- [`docs/CANONICAL_OWNERS.md`](docs/CANONICAL_OWNERS.md) — canonical owners for reusable definitions and theorem families; read before adding infrastructure.
- [`docs/PROOF_CHANGE_CHECKLIST.md`](docs/PROOF_CHANGE_CHECKLIST.md) — duplicate-avoidance, provenance, termination, and compile checklist.
- [`docs/MODULE_CATALOG.md`](docs/MODULE_CATALOG.md) — human-oriented map of subsystem and final-assembly module families.

For an exhaustive index of **every Lean file**, its imports, module-doc purpose, A18/A19 labels, reverse importers, and declarations, run:

```bash
python3 tools/generate_proof_inventory.py
```

This generates `docs/generated/LEAN_MODULE_INDEX.md`, `DECLARATION_INDEX.md`, and `LOCAL_IMPORT_EDGES.md` directly from the checkout.

## Build

The normal integration check is:

```bash
lake build
```

For a focused module while developing:

```bash
lake env lean HC4/path/to/File.lean
```

For certification snapshots, `./verify.sh` remains the stronger repository-level verification entry point where applicable.

## Architectural rules

The current final assembly has several deliberately distinct routes. In particular:

- the global rank-one recursion is already owned by `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace` and is well founded only on strict natural `rawDefect` decrease;
- successful positive Rees steps are ordinary edges of that existing trace, not a second termination mechanism;
- older torus-balanced cross-facet affine-line infrastructure remains valid, but the unrestricted zero-clock route uses the newer balance-free finite-support cross-facet/ray machinery;
- source, presented, recentered, top-face, first-contact, lower-carrier, and ray support witnesses must not be interchanged without an explicit transport theorem;
- generic definitions live with their representation (`HC4.Polynomial`, `HC4.Newton`, `HC4.Valuation`, `HC4.RationalRigidity`) rather than with whichever downstream module happens to consume them most often.

Read `docs/CANONICAL_OWNERS.md` before introducing a new generic-looking declaration. The recent final-assembly import collisions are exactly the kind of issue this registry and generated declaration index are intended to prevent.

## Historical documents

`FORMALISATION_LEDGER.md`, `CERTIFICATION_STATUS.md`, and the numbered `FORMALISATION_STATUS_PHASE*.md` files are historical records from earlier snapshots. Their old “missing” lists are not authoritative for the present branch. Use the current Lean source and `docs/` navigation instead.