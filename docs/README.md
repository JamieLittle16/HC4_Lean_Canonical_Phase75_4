# HC4 documentation hub

Start here for the current proof, not a historical phase diary.

1. [CURRENT_STATE.md](CURRENT_STATE.md) — exact target/status distinctions.
2. [PROOF_AND_CONTRIBUTION_AUDIT.md](PROOF_AND_CONTRIBUTION_AUDIT.md) — consolidated result, proof architecture, dependency statistics and attribution.
3. [PROOF_PATHS.md](PROOF_PATHS.md) — current proof interfaces and historical routes.
4. [NEXT_STEPS.md](NEXT_STEPS.md) — immediate research tasks and verification discipline.
5. [CANONICAL_OWNERS.md](CANONICAL_OWNERS.md) — existing owners; search before introducing new machinery.
6. [research/](research/) — detailed mathematical arguments; status labels within each note may be historical.
7. [archive/](archive/) — pinned historical handoff index.
8. [generated/](generated/) — source-derived module, declaration and import indexes.

Supporting references: [proof architecture](PROOF_ARCHITECTURE.md), [glossary](GLOSSARY_AND_INVARIANTS.md), [module catalog](MODULE_CATALOG.md), [historical routes](HISTORICAL_AND_SUPERSEDED_ROUTES.md), [change checklist](PROOF_CHANGE_CHECKLIST.md). The older architecture/route references describe the A18/A19 development and are not live proof-status ledgers.

## Working rules

Read the current state, exact route and canonical owners; search the generated declaration and module indexes; then inspect exact Lean types and imports. Preserve source/collision provenance and the existing raw-defect termination mechanism. Keep conditional HC4, unrestricted HC4, and local cap theorems separate.

Generate indexes with `python3 tools/generate_proof_inventory.py`. The CI workflow regenerates them for diagnostics; the inventory-export workflow may commit changes. Index generation is not Lean verification.

For every new endpoint, record carrier, hypotheses, conclusion, role, remaining integration obligations and exact build status. Update current state/paths/next steps when they change. Lean source and elaborated theorem types take precedence over prose; historical snapshots are never current missing-lemma lists.
