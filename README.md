# HC4 Lean

Cumulative Lean formalisation of determinant-one Hessian gradient injectivity in four variables, with canonical Smith/Rees reductions and independent transverse-rigidity research.

**The full unrestricted theorem is not claimed complete.** The conditional JC2 route, local transverse-cap results and paper candidates have distinct statuses.

## Start here

- [Current proof status](docs/CURRENT_STATE.md)
- [Exact proof paths and source interfaces](docs/PROOF_PATHS.md)
- [Next research steps](docs/NEXT_STEPS.md)
- [Documentation hub](docs/README.md)
- [Canonical mathematical owners](docs/CANONICAL_OWNERS.md)

The [historical index](docs/archive/README.md) preserves older phase and handoff checkpoints without treating them as current research plans.

## Build and verify

```bash
lake build HC4.Polynomial.TransverseLeadingFirstCorrection
lake build
lake env lean HC4/Audit.lean
```

Run `./verify.sh` for the broader verification script (it also invokes dependency update/cache, negative control and proof escape-hatch scanning). See the actual commit's CI status; an inventory export is not a Lean build.

## Find existing mathematics

Run `python3 tools/generate_proof_inventory.py` for the generated [module index](docs/generated/LEAN_MODULE_INDEX.md), [declaration index](docs/generated/DECLARATION_INDEX.md) and [local imports](docs/generated/LOCAL_IMPORT_EDGES.md). Check these before introducing a new generic definition or theorem. The canonical source tree is `HC4/`, with root aggregate `HC4.lean` and the separate negative control.

Preserve actual-source and collision provenance; reuse the existing raw-defect termination machinery. Keep the exact hypotheses of every endpoint visible and distinguish a source declaration, a verified build and an unverified paper argument.
