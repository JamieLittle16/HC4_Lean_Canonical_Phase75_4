# Phase 75.12.8 — right-chart entrywise constant-coefficient transport

This patch removes the four deterministic-timeout proofs in
`RigidPacketZeroSchurBridge.lean`.

Instead of expanding the right-chart active determinant and cleared Schur
expressions while `Equiv.swap 1 2` is still present, the proof now:

1. applies coefficient-at-zero entrywise to the ten fields of a
   `GeneralFourBlock (Polynomial K)`;
2. proves once that coefficient-at-zero commutes with `activeDet`, `schurA`,
   `schurB`, and `schurC`;
3. proves entrywise that the constant fibre of an evaluated Hessian four-block
   is the four-block of the evaluated special-fibre Hessian;
4. simplifies the four concrete values of `rigidRightChartPerm` before any
   Schur polynomial is formed;
5. obtains the four right-chart specialization theorems by short rewrites.

No theorem statements, geometric hypotheses, or endpoint claims are changed.
The purpose is proof-term size/performance only.
