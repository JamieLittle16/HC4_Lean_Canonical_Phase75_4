# Phase 93.76 — Lossless Smith Frontier

Built over green Phase 93.75.

The full-source audit found that the former local predicate
`HasCanonicalSmithRepairOrTerminal` intentionally forgets exactly the
geometry needed by the remaining first-departure theorem.

The source already contains a stronger theorem:
`homogeneous_exactAxisCollision_symmetricMinimal_canonicalRepair`.
It retains the balanced Smith subface, nonzero persistent packet support,
the rigid rank-one certificate, and the actual rank-two escalation
certificate.

This phase threads that stronger result through all three local branches:

- primitive zero-Smith source;
- pure coefficient first wall;
- no genuine wall / primitive transformed family.

The new structure `CanonicalSmithLosslessFrontier` retains the actual
family and transformed marked sections in addition to the complete Smith
packet data.

The new dispatcher
`alignedSmith_zeroSection_geometricDispatcher_lossless`
has only:
- the lossless local frontier; or
- a separated right-section wall.

Combining it with green Phase 93.74 gives
`alignedSmith_zeroSection_closedGeometricStep_lossless`.

Strong induction on the true determinant defect then proves
`canonicalGeometricRestart_reachesLosslessSmithFrontier`.

The remaining local interface is now exactly
`CanonicalLosslessSmithFrontierExhaustionUnderJC2`.

Unlike the former compact interface, its input contains enough geometry to
state and prove the missing first-departure / rank-two Rees extraction
without reconstructing data which had already been erased.

No theorem from the green geometric restart stack is weakened or replaced.
