# Phase 78 changelog

## Added

`HC4/Polynomial/AutonomousODEPoleOrder.lean`

The file defines shifted Euler differentiation after translating a nonzero
root and proves exact lowest-order coefficient identities corresponding to
the manuscript's pole-order calculation in Lemma 4.1.

## Scope

Phase 78 does **not** yet prove the full autonomous polynomial right-hand side
has degree at most two.  It supplies the local nonvanishing/order certificate
needed for that next coefficient comparison.


## Phase 78.1

- Fixed rewrite ordering in `shiftedEuler_X_pow_succ_mul`.
- No theorem statements or hypotheses changed.
