import HC4.Valuation.KernelInflationHessianDefect
import HC4.Valuation.PolynomialFamilyCollisionSpecialFiber
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# A18.5.7: Hessian determinant of a polynomial-family special fibre

A polynomial-parameter family with pure Hessian clock

    det Hess(P) = tau^Delta

has a particularly simple special fibre when `Delta > 0`: its ordinary
source Hessian determinant vanishes.  This elementary specialization fact is
the determinant-level companion to the entrywise special-fibre calculus used
throughout the aligned-Smith closing programme.

The statement is deliberately generic.  It applies to every retained A18
presented state and does not depend on a Smith chart, recentering, or terminal
rank label.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Source Hessian commutes entrywise with passage to the parameter special
fibre. -/
theorem hessian_polynomialFamilySpecialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessian (polynomialFamilySpecialFiber P) =
      (MvPolynomial.map Polynomial.constantCoeff).mapMatrix
        (HC4.Polynomial.hessian P) := by
  apply Matrix.ext
  intro i j
  simp [HC4.Polynomial.hessian_apply,
    polynomialFamilySpecialFiber, MvPolynomial.pderiv_map]

/-- Consequently the Hessian determinant commutes with the same coefficient
specialization. -/
theorem hessianDeterminant_polynomialFamilySpecialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant (polynomialFamilySpecialFiber P) =
      MvPolynomial.map Polynomial.constantCoeff
        (HC4.Polynomial.hessianDeterminant P) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_polynomialFamilySpecialFiber]
  exact RingHom.map_det (MvPolynomial.map Polynomial.constantCoeff)
    (HC4.Polynomial.hessian P)

/-- **Positive pure family defect gives a Hessian-degenerate special fibre.** -/
theorem polynomialFamilySpecialFiber_hessianDeterminant_eq_zero_of_posDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hDelta : 0 < Delta) :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber P) = 0 := by
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef]
  simp [Nat.ne_of_gt hDelta]

/-- The same fact exposed directly from a scale-aware restart state. -/
theorem ScaleAwareAdaptiveGeometricRestartState.specialFiber_hessianDeterminant_eq_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpos : 0 < s.rawDefect) :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber s.family) = 0 := by
  exact polynomialFamilySpecialFiber_hessianDeterminant_eq_zero_of_posDefect
    s.family s.rawDefect s.hessianDefect hpos

end

end HC4.Valuation
