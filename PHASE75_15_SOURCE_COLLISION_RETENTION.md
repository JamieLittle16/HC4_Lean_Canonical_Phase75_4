# Phase 75.15 — Source-level exact collision at rigid closing

## Purpose

The rigid closing clock of Phase 75.14 is obtained from an evaluated Hessian/
Schur four-block.  A terminal associated-graded polynomial fibre, however,
must be extracted from the actual polynomial family and its source-lattice
filtration.  This patch restores the marked exact-collision data on the very
same defect-preserving Smith exposure family used by the rigid clock.

## New module: `CanonicalSmithDefectExposureCollision`

For a section whose transverse special coordinates vanish, ramification by
`alignedSmithRamificationIndex = 20` followed by one symmetric Smith step
`(2,2)` is integral on the section.  The proof uses the existing exact section
orders and the already-proved aligned section-divisibility theorem.

The transformed section keeps its special point because a single Smith step
is strictly before every positive transverse section wall.

For every canonical lossless/departure frontier the patch therefore defines

- `defectSmithExposureLeftSection`;
- `defectSmithExposureRightSection`;

and proves

- exact family-gradient collision on `defectSmithExposureFamily`;
- left special point remains `0`;
- right special point remains `e0`;
- the two special points remain distinct;
- full ordinary source homogeneity is preserved.

## New module: `RigidClosingExactCollisionSource`

`RigidClosingExactCollisionSourceData f` packages, for one actual frontier:

- the provenance-preserving `RigidClosingCertificate`;
- full source homogeneity;
- exact Hessian defect `20 * f.defect`;
- exact moving gradient collision on the actual exposure family;
- canonical distinct reductions `0` and `e0`;
- equality of the special fibre with the retained rigid Smith packet.

Every `RigidClosingCertificate` canonically yields this record.

## Terminal interface refinement

`HasRigidClosingTerminalExtraction f` now consumes
`RigidClosingExactCollisionSourceData f`, not a bare evaluated matrix-closing
certificate.  This prevents a later proof from silently identifying an
evaluated Hessian clock with a global Newton/Rees associated-graded potential.

The existing JC2 consumer theorem is unchanged mathematically: once terminal
associated-graded collision data are constructed, the closing branch is
contradictory and rank-two progress follows.

## Remaining exact obligation

This patch deliberately does **not** assert that the evaluated Schur closing
order supplies an integral global diagonal Rees weight on every monomial of
the family.  That source-support/lattice exposure is the remaining terminal
construction.  It must be proved from the retained source data rather than
introduced as an assumption.

## Audit

No `sorry`, `admit`, `unsafe`, or new `axiom` occurs in the patch.
