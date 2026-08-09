# Formalisation status after Phase 79 candidate

## Already kernel-verified before this candidate

- Phase 75.2: complementary-edge rigidity in manuscript endpoint form.
- Phase 76: rank-three logarithmic-Hessian / moment bridge to the autonomous
  scalar equation.
- Phase 77.3: coefficient rigidity once the autonomous polynomial is
  quadratic.
- Phase 78.1: exact local pole-order coefficients at a translated nonzero
  root.

## Phase 79 candidate

Phase 79 attempts to certify the missing local quadraticity implication:

    shifted polynomial autonomous ODE at a genuine nonzero root
        -> natDegree R <= 2.

This is done by a finite coefficient comparison, not Laurent series or
projective geometry.

## Still not claimed after Phase 79

Even if Phase 79 is green, the complete rank-three theorem still requires
bridges from the actual rank-three rational function to the polynomial
shifted ODE used here, in particular:

1. eliminate finite poles of the rational autonomous right-hand side;
2. transport the equation to a nonzero root of the edge polynomial;
3. connect the manuscript infinity cases to the Phase 77 quadratic
   coefficient theorems and then to the existing binomial-pencil obstruction;
4. handle the equal-ordinary-degree homogeneous branch (currently tied to
   the Gordan--Noether / torus-stability obligation).

No unrestricted HC4 claim is made.

## Phase 79.1 repair

The first Phase 79 build exposed one proof-engineering error only: an
associativity rewrite was oriented backwards before `Polynomial.coeff_C_mul`.
Phase 79.1 reverses that one rewrite.  The degree-bound theorem and all of its
hypotheses are unchanged.
