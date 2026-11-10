import HC4.Valuation.QuadraticTransverseCapRatFuncDerivationX
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-!
# First concrete construction of the rational X-derivative

The generic-rank-three quadratic source has already supplied the
exact polynomial matrix Riccati equation. The only differential
infrastructure still missing is the actual derivation d/dx on K(x).

This module starts from the classical quotient rule

  (p/q)' = (p' q - p q')/q².

The key first point is representation-independence: replacing
(p,q) by (a p,a q), a != 0, leaves the displayed quotient
unchanged. This is exactly the invariance needed by pinned
mathlib's `RatFunc.liftOn'` constructor.

The resulting function on RatFunc is a candidate derivative.
Its additive, Leibniz and K-linear laws will be proved separately
before it is upgraded to a `Derivation K (RatFunc K) (RatFunc K)`.
This module never assumes the candidate is a derivation.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- The rational quotient-rule expression, including the case of a
zero denominator (where field division returns zero). -/
noncomputable def quadraticTransverse_ratQuotientXDerivative
    (p q : Polynomial K) : RatFunc K :=
  let f : Polynomial K →+* RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K)
  (f (Polynomial.derivative p) * f q -
      f p * f (Polynomial.derivative q)) / (f q) ^ 2

/-- Scaling an arbitrary polynomial fraction numerator and denominator
by the same nonzero polynomial does not change the quotient
derivative. This is the exact `RatFunc.liftOn'` well-definedness law. -/
theorem quadraticTransverse_ratQuotientXDerivative_scale
    (p q a : Polynomial K)
    (hq : q ≠ 0)
    (ha : a ≠ 0) :
    quadraticTransverse_ratQuotientXDerivative (a * p) (a * q) =
      quadraticTransverse_ratQuotientXDerivative p q := by
  let f : Polynomial K →+* RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K)
  have hfa : f a ≠ 0 := RatFunc.algebraMap_ne_zero ha
  have hfq : f q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hnum :
      (f (Polynomial.derivative (a * p)) * f (a * q) -
        f (a * p) * f (Polynomial.derivative (a * q))) =
      (f a) ^ 2 *
        (f (Polynomial.derivative p) * f q -
          f p * f (Polynomial.derivative q)) := by
    simp only [Polynomial.derivative_mul, map_add, map_mul]
    ring
  have hden :
      (f (a * q)) ^ 2 = (f a)^2 * (f q)^2 := by
    rw [map_mul, mul_pow]
  dsimp [quadraticTransverse_ratQuotientXDerivative]
  rw [hnum, hden]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hfa)

/-- The quotient rule, well-defined on the actual rational function
field via the pinned `RatFunc.liftOn'` scaling-invariance API.
This is a FUNCTION, not yet a K-derivation. -/
noncomputable def quadraticTransverse_ratFuncCandidateXDerivative
    (z : RatFunc K) : RatFunc K :=
  RatFunc.liftOn' z
    (fun p q : Polynomial K =>
      quadraticTransverse_ratQuotientXDerivative p q)
    (fun {p q a} hq ha =>
      quadraticTransverse_ratQuotientXDerivative_scale p q a hq ha)

/-- The rational derivative candidate has the expected quotient
rule on nonzero-denominator polynomial fractions. -/
theorem quadraticTransverse_ratFuncCandidateXDerivative_mk
    (p q : Polynomial K)
    (hq : q ≠ 0) :
    quadraticTransverse_ratFuncCandidateXDerivative (RatFunc.mk p q) =
      quadraticTransverse_ratQuotientXDerivative p q := by
  have hzero : ∀ p : Polynomial K,
      quadraticTransverse_ratQuotientXDerivative p 0 =
        quadraticTransverse_ratQuotientXDerivative 0 1 := by
    intro p
    simp [quadraticTransverse_ratQuotientXDerivative]
  exact RatFunc.liftOn'_mk p q
    (fun r s : Polynomial K =>
      quadraticTransverse_ratQuotientXDerivative r s)
    hzero
    (fun {r s a} hs ha =>
      quadraticTransverse_ratQuotientXDerivative_scale r s a hs ha)

/-- On embedded polynomials, the rational quotient-rule candidate
agrees exactly with the already-existing formal polynomial derivative.
This is the first compatibility law needed for the eventual
K-derivation. -/
theorem quadraticTransverse_ratFuncCandidateXDerivative_polynomial
    (p : Polynomial K) :
    quadraticTransverse_ratFuncCandidateXDerivative
        ((algebraMap (Polynomial K) (RatFunc K)) p) =
      (algebraMap (Polynomial K) (RatFunc K))
        (Polynomial.derivative p) := by
  rw [← RatFunc.mk_one p]
  rw [quadraticTransverse_ratFuncCandidateXDerivative_mk p 1 one_ne_zero]
  simp [quadraticTransverse_ratQuotientXDerivative]

/-- In particular, the quotient-rule candidate differentiates the
genuine rational indeterminate X to 1. To qualify as a
`Derivation`, its additive and product rules must still be proved. -/
theorem quadraticTransverse_ratFuncCandidateXDerivative_X :
    quadraticTransverse_ratFuncCandidateXDerivative
      (RatFunc.X : RatFunc K) = 1 := by
  have hX :
      (RatFunc.X : RatFunc K) =
        (algebraMap (Polynomial K) (RatFunc K)) Polynomial.X := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    simp
  rw [hX, quadraticTransverse_ratFuncCandidateXDerivative_polynomial]
  simp

end

end HC4.Valuation
