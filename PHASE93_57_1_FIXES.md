# Phase 93.57.1 — Exact defect extraction proof fixes

The first Phase 93.57 build exposed three local Lean proof issues.

## 1. Explicit `induction_on'` motive

Mathlib's `MvPolynomial.induction_on'` has the form

    induction_on' p monomial add

with an implicit predicate `P : MvPolynomial σ R -> Prop`.

`apply` could not infer that predicate from the goal. The proof now supplies
the exact coefficient-covariance motive explicitly using

    refine MvPolynomial.induction_on' (P := fun Q => ...) Q ?_ ?_.

## 2. Divisibility witness orientation

`a ∣ b` expects an equality of the form

    b = a * witness.

`integralKernelBlowup_defect_factor_equation` already has precisely that
orientation, so the proof now uses `hfactor`, not `hfactor.symm`.

## 3. Constant-polynomial coefficient simplification

The coefficient divisibility theorem produces

    coeff 0 (C (tau^Delta)).

The proof now invokes the exact simp theorem

    MvPolynomial.coeff_zero_C

to reduce this to `tau^Delta`.

No theorem statements, assumptions, or mathematics are changed.
