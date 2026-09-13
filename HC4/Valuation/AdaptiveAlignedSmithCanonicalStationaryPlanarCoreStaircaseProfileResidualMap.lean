import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# A19.R13: staircase residual commutes with coefficient-ring maps

The other-facet Schur calculation is most naturally carried out over the
integral transverse coefficient ring `MvPolynomial (Fin 3) K`.  The existing
terminal rigidity package deliberately works over its fraction field, where
nonzero transverse coefficients become scalars without cancellation.

This file isolates the representation change: Euler differentiation, the
falling second Euler operator, and hence the complete binary staircase
residual commute with a coefficient ring homomorphism.  The final A19 adapter
can therefore prove the residual identity before localization and transport it
in one step.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u v
variable {K : Type u} {L : Type v}
variable [Field K] [CharZero K] [Field L] [CharZero L]

/-- Euler differentiation is natural under coefficient-ring maps. -/
@[simp]
theorem map_eulerDerivative
    (phi : K →+* L) (h : Polynomial K) :
    Polynomial.map phi (eulerDerivative h) =
      eulerDerivative (Polynomial.map phi h) := by
  simp [eulerDerivative]

/-- The falling second Euler operator is natural under coefficient-ring maps. -/
@[simp]
theorem map_binaryStaircaseProfileSecondEuler
    (phi : K →+* L) (h : Polynomial K) :
    Polynomial.map phi (binaryStaircaseProfileSecondEuler h) =
      binaryStaircaseProfileSecondEuler (Polynomial.map phi h) := by
  unfold binaryStaircaseProfileSecondEuler
  simp

/-- **Naturality of the stationary binary staircase residual.** -/
@[simp]
theorem map_binaryStaircaseProfileResidual
    (phi : K →+* L) (D r : ℕ) (h : Polynomial K) :
    Polynomial.map phi (binaryStaircaseProfileResidual D r h) =
      binaryStaircaseProfileResidual D r (Polynomial.map phi h) := by
  unfold binaryStaircaseProfileResidual
  simp

/-- A zero residual over the source coefficient field transports to every
coefficient-ring extension, in particular to the fraction-field profile used
by A19.115. -/
theorem binaryStaircaseProfileResidual_map_eq_zero
    (phi : K →+* L) (D r : ℕ) (h : Polynomial K)
    (hzero : binaryStaircaseProfileResidual D r h = 0) :
    binaryStaircaseProfileResidual D r (Polynomial.map phi h) = 0 := by
  rw [← map_binaryStaircaseProfileResidual]
  rw [hzero]
  simp

end

end HC4.Valuation
