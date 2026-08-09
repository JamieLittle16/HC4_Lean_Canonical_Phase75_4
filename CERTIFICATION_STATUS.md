# Certification status — canonical Phase 75.2

## What is certified by the current development

The cumulative source contains the complete Phase 75.2 complementary-edge
rigidity wrapper and all of its downstream dependencies. The supplied audit
log records only standard Lean foundations (`propext`, `Classical.choice`, and
`Quot.sound`, as applicable) for the Phase 75 endpoint theorem.

The source also contains substantial verified infrastructure for:

- invariant/toric exponent arithmetic;
- weighted initial forms and Hessian determinant compatibility;
- first-contact/Newton boundary selection machinery;
- explicit rank-three pencil determinant identities;
- complementary logarithmic/moment determinant algebra;
- the actual `MvPolynomial` substitution bridge;
- explicit inverses for the two classified polynomial gradient families;
- exceptional-grading arithmetic and boundary-cycle combinatorics.

## What is not yet certified

There is currently no top-level theorem in the source deriving the paper's
classification directly from the full manuscript hypotheses (invariant
potential, prescribed quadratic part, and constant Hessian determinant).
`HC4/MainAssembly.lean` begins only after one of the two classified gradient
formulae has already been obtained.

Consequently this snapshot is **not yet a machine-checked proof of the full
first/symmetric-gradings paper**.

The principal remaining manuscript-level obligations are tracked in
`FORMALISATION_LEDGER.md`.

## Static reconstruction audit

For this cleaned snapshot:

- all local `HC4.*` imports resolve;
- no `sorry`, `admit`, project `axiom`, or `unsafe` tokens occur in `HC4` Lean
  sources;
- the project contains the pinned toolchain, Lake files, root aggregator,
  audit file, verification scripts, and negative control;
- the Phase 75 source hashes agree with the Phase 75.2 manifest supplied in
  the user's infrastructure archive.

A fresh `./verify.sh` run on this exact cleaned ZIP remains the authoritative
kernel/reproducibility check.
