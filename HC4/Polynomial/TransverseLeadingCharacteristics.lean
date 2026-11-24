import HC4.Polynomial.RankThreeCubicCharacteristics
import Mathlib.Tactic

/-!
# Arbitrary transverse degree: actual leading Hessian and straight characteristics

The weight used by the cubic construction is independent of degree:
longitudinal weight zero and three transverse weights one. For any
transverse cap m >= 2 the maximal determinant grade is 4*m-6 > 0.
A constant full Hessian determinant therefore forces the true weight-m
leading Hessian to be singular.

The normalized-kernel and straight-line theorem already in
RankThreeCubicCharacteristics is degree-independent. Reuse it
without assuming singularity or introducing a replacement source.

This is a leading-layer result, not a claim of a full-source
collision-preserving reduction, nor a pole obstruction.
-/

namespace HC4.Polynomial.RankThreeCubic

noncomputable section
open MvPolynomial
open scoped BigOperators Matrix

variable {K : Type*} [Field K]

/-- The full Hessian of the actual top transverse layer is singular
for every cap m >= 2 of a constant-Hessian source. -/
theorem transverseLeading_hessian_det_eq_zero
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    (hessian (initialForm transverseCubicWeight m F)).det = 0 := by
  have he := initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
    transverseCubicWeight m F hcap
  have hc : (Fintype.card (Unit ⊕ Fin 3) : ℤ) = 4 := by decide
  have hs : (∑ i : Unit ⊕ Fin 3, transverseCubicWeight i) = 3 := by decide
  rw [hc, hs] at he
  have hw : (4 : ℤ) * m - 2 * 3 = 4 * m - 6 := by ring
  rw [hw, hdet, initialForm_eq_zero_of_isWeightedHomogeneous
    (MvPolynomial.isWeightedHomogeneous_C transverseCubicWeight δ)
    (4 * m - 6) (by omega)] at he
  exact he.symm

/-- At any regular anchor the actual leading gradient has a normalized
straight characteristic, for arbitrary transverse degree. The degree
is used only to derive leading Hessian singularity from the source. -/
theorem transverseLeading_exists_anchored_characteristic
    [CharZero K] {E : Type*} [Field E] [Algebra K E]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z : Unit ⊕ Fin 3 → E)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    ∃ V : Unit ⊕ Fin 3 → E, V (.inl ()) = 1 ∧
      ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight m F)) =
        _root_.Polynomial.C
          (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight m F))) := by
  exact exists_anchored_lineEval_gradient_eq
    (initialForm transverseCubicWeight m F)
    (transverseLeading_hessian_det_eq_zero F m hm hcap hdet)
    z hz

end
end HC4.Polynomial.RankThreeCubic
