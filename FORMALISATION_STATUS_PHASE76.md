# Formalisation status — Phase 76 candidate

## Green baseline

Canonical Phase 75.2 is user-verified green.  In particular, complementary
edge rigidity is closed end-to-end.

## Phase 76 target

The symmetric-gradings manuscript rank-three proof uses the logarithmic core

`e e^T + eta w w^T - diag(e)`

with `v=(0,v2,v3,v4)` and `e=v+rho*w`.  This patch formalises the cleared
rank-three determinant identity and connects it to the generic moment core
already verified in Phase 72.

A green Phase 76 does **not** yet prove complete rank-three edge rigidity.  It
closes the Hessian-to-autonomous-equation bridge.  The remaining front-half
obligation is the univariate autonomous rational-rigidity argument forcing the
separated/binomial ODE; the reconstruction from that ODE is already verified
in `AutonomousODEReconstruction.lean`.
