# Phase 77.2 fixes

This is a two-point proof-engineering repair of the Phase-77.1 candidate.
No theorem statement or mathematical hypothesis is changed.

Changes in `HC4/Polynomial/AutonomousODEQuadraticRigidity.lean`:

1. In the `A = -1` two-term conclusion, avoid a global `rw [hqC]` after
   proving `q = C (q.coeff 0)`.  The global rewrite also changed the
   coefficient expression on the theorem's right-hand side to
   `(C (q.coeff 0)).coeff 0`.  A two-step `calc` now rewrites only the
   polynomial factor and then commutes the constant polynomial past `X^m`.
2. In the `J >= 2` contradiction, give `Nat.cast_sub` an explicit equality
   type in the ambient field `K`, eliminating the unresolved
   `AddGroupWithOne` metavariable from the Phase-77.1 build.

All earlier Phase-77.1 repairs and the Phase-76 rank-three Hessian bridge are
unchanged.
