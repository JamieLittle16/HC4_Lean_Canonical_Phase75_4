# Phase 93.69.1 — systematic elaboration fix

This patch addresses the first build of the large Phase 93.69 endpoint
normalisation.

The errors were concentrated in six proof-engineering classes rather than
new mathematical gaps.

## 1. Homogeneity

Mathlib's `MvPolynomial.IsHomogeneous D` is coefficientwise: every nonzero
supported monomial must have total weight `D`.

The Smith and common-factor homogeneity proofs now use the already-proved
support-containment theorems directly, instead of calling a nonexistent
`degree_eq_sum_deg_support` API.

## 2. Exact common-factor defect

The exponent normalisation now uses `n * 4` in the exact syntactic shape
created by `pow_mul`.

## 3. Primitive factorisations

Calls to `polynomialParameterPrimitivePart_spec` are fully instantiated
with the concrete coefficient and its nonzero proof.  This avoids Lean
trying to rewrite a metavariable pattern.

## 4. Zero-residual coefficient

The exact residual-order proof now:
- rewrites `smithFamilyCoefficientOrder` to the local `v` explicitly;
- preserves the original equality orientation;
- normalises the ramified coefficient into a named factorisation;
- expands `X^(p+q)` in the direction matching the target.

The special-fibre membership is also assigned an explicit target type
before forming the existential tuple.

## 5. Section walls

The source exponent is proved by finite-coordinate case analysis.
`choose_spec` is used in the correct orientation and the final target is
changed definitionally to the local quotient `q`.

The generic dependent `if c = a` theorem has been replaced by separate
left/right section-wall theorems.

## 6. No-wall exact coefficient and final boundary API

The minimal zero-grade coefficient theorem now binds the support proof
explicitly as a dependent existential.  This removes the invalid
`by assumption` from its theorem statement.

The residual section-boundary certificate is now a simple left/right
disjunction rather than a dependent `if`, removing the missing Decidable
instance and the downstream elaboration/sorry cascade.

The no-wall collision section-integrality proofs unfold
`parameterRamificationSection` before simplifying the known zero transverse
coordinates.

No theorem is weakened mathematically; the boundary certificate is merely
represented more transparently.

No `sorry`, `admit`, `axiom`, or `unsafe` appears in the source.
