# Publication preparation

## Verified baseline

- Research archive: [fe55e3fb](https://github.com/JamieLittle16/HessianConjecture4/tree/archive/research-2026).
- Earlier independently reproduced equivalence: [1377de42](https://github.com/JamieLittle16/HessianConjecture4/actions/runs/45855370863).
- Reduced publication checkpoint: [a559ee2d](https://github.com/JamieLittle16/HessianConjecture4/commit/a559ee2ddc898fc6c9e8105b500757b9c45628bd), with maintainer-reported successful builds and endpoint audits.
- 229 tracked HC4 modules (227 transitive proof imports plus umbrella and audit), 231 tracked Lean files including the exporter and negative control.
- Lean 4.24.0 remains pinned. The reduced project needs a fresh-host reproduction; this is separate from the earlier verified result.

## Before migrating

- Regenerate source inventory and final/core declaration reports using tracked source files.
- Preserve the historical audit and attribution, including Tang and the Mathlib backport notices. Archive superseded research documentation rather than rewrite its history.
- Check tracked scripts and workflows for references to deleted historical modules.
- The author approved Apache 2.0 for the project; root LICENSE and NOTICE are present. The vendored Mathlib files retain their Apache 2.0 licence in HC4/Backport/LICENSE.
- Run a fresh-host build and all five endpoint axiom checks. Do not clear local project caches after every incremental edit.

## Palomar migration

Create a separate migration branch from the verified reduced checkpoint. Recheck Palomar's current toolchain and submission rules at https://palomar-registry.org/how-to-submit before upgrading. Port the source to a supported Lean/Mathlib version and the required module system without weakening statements. Reassess the vendored Luroth development against the new Mathlib version. Keep the deliberately false negative control out of the submitted Lean source set (retain it as a generated test). Prepare independently written challenge statements, solutions, metadata and comparator configuration; verify all required endpoints with the supported verifier. Submission and registration remain outstanding.

The mathematical manuscript is a review draft, not a claim of priority or independent journal validation.
