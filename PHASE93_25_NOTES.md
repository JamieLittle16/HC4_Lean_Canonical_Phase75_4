# Phase 93.25 — TerminalConformalFace

## New module

    HC4/Newton/TerminalConformalFace.lean

Phases 93.22--93.24 are green through the actual terminal Hessian bridge.

This phase packages them into the exact local terminal dichotomy.

Definitions:

    IsScalarIntegralWeight
    IsNonScalarIntegralWeight
    IsNontrivialIntegralWeight
    HasConformalQuadraticWeight
    HasNonScalarTerminalConformalFace

Main facts:

1. weighted homogeneity implies
       [X_i X_j]F != 0 -> lambda_i + lambda_j = d;

2. actual terminal Hessian nondegeneracy gives
       F != 0
   and the conformal quadratic-weight certificate;

3. scalar + nontrivial weight invokes the green scalar terminal theorem,
   giving
       F != 0 AND HasPureQuadraticSupport F;

4. non-scalar weight produces an explicit non-scalar conformal terminal
   certificate, without assuming any torus endpoint theorem;

5. `terminalConformalFace_dichotomy` gives the exhaustive local split.

This is intentionally the local `TerminalConformalFace` layer only.
The next module should be `TerminalDirectRankJump`: connect the non-scalar
certificate to the exact existing conformal-torus endpoint theorem, and
combine the scalar branch with terminal collision.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
