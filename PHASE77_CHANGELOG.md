# Phase 77 — quadratic autonomous ODE coefficient rigidity

New file: `HC4/Polynomial/AutonomousODEQuadraticRigidity.lean`.

Phase 77.1 repairs the initial candidate without changing its statements:
explicit coefficient-goal normalisation; top-product coefficients through
`Polynomial.coeff_mul_degree_add_degree`; cast-safe `A=-1` arithmetic; and a
`Nat.cast_sub` proof of the positive-reciprocal contradiction.
