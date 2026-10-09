import HC4.Valuation.QuadraticAxisFourBlockRankTwo
import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerDirectTest
import HC4.Valuation.AdaptiveAlignedSmithTransverseSourceShearQuadraticLayer
import Mathlib.Tactic

/-!
# The genuine represented-source transverse rank-two witness at Rees cap two

The marked-axis weight (0,1,1,1) gives every quadratic origin-Hessian entry
of the reverse-Rees family an exact coefficient, with parameter order
2-w(i)-w(j).  Therefore its origin Hessian is the quadratic-axis pencil
from QuadraticAxisFourBlockRankTwo.  Its exact Hessian determinant tau^2
forces a nonzero 2x2 minor of the *represented-source* transverse 3x3 block.

This uses the full represented determinant-one source, not a replacement
potential, and needs no terminal producer, JC2, or repair hypothesis.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Each origin Hessian entry of a cap-two marked-axis reverse-Rees family
is a single monomial in the parameter with source-Hessian coefficient. -/
theorem quadraticAxisReverseRees_originHessian_entry
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i k : Fin 4) :
    quadraticFamilyHessianMatrix
        (reverseWeightedReesFamily topKernelMarkedAxisNatWeight 2 F hbound) i k =
      Polynomial.X ^
          (2 - (topKernelMarkedAxisNatWeight i +
                topKernelMarkedAxisNatWeight k)) *
        Polynomial.C (quadraticFamilyHessianMatrix F i k) := by
  classical
  let d : Fin 4 →₀ ℕ := Finsupp.single k 1 + Finsupp.single i 1
  have hw :
      Finsupp.weight topKernelMarkedAxisNatWeight d =
        topKernelMarkedAxisNatWeight i +
          topKernelMarkedAxisNatWeight k := by
    fin_cases i <;> fin_cases k <;>
      simp [d, topKernelMarkedAxisNatWeight,
        Finsupp.weight_apply, Finsupp.sum_fintype,
        Fin.sum_univ_four, Finsupp.add_apply, Finsupp.single_apply]
  rw [quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient,
    quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient]
  change
      MvPolynomial.coeff d
          (reverseWeightedReesFamily topKernelMarkedAxisNatWeight 2 F hbound) *
          (((Finsupp.single k 1) i + 1 : ℕ) : Polynomial K) =
        Polynomial.X ^
          (2 - (topKernelMarkedAxisNatWeight i +
                topKernelMarkedAxisNatWeight k)) *
          Polynomial.C (MvPolynomial.coeff d F *
            (((Finsupp.single k 1) i + 1 : ℕ) : K))
  rw [reverseWeightedReesFamily_coeff, hw]
  by_cases hd : d ∈ F.support
  · simp only [hd, if_true]
    simp only [map_mul, map_natCast]
    ring
  · have hzero : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hzero]

/-- The full source-origin Hessian is exactly the explicit symmetric
quadratic-axis pencil, coefficient by coefficient. -/
theorem quadraticAxisReverseRees_originHessian_block
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F) :
    let H := quadraticFamilyHessianMatrix F
    let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight 2 F hbound
    GeneralFourBlock.ofSymmetricMatrix (quadraticFamilyHessianMatrix Q) =
      quadraticAxisFourBlock (Polynomial.X : Polynomial K)
        (Polynomial.C (H 0 0))
        (Polynomial.C (H 0 1))
        (Polynomial.C (H 0 2))
        (Polynomial.C (H 0 3))
        (Polynomial.C (H 1 1))
        (Polynomial.C (H 1 2))
        (Polynomial.C (H 1 3))
        (Polynomial.C (H 2 2))
        (Polynomial.C (H 2 3))
        (Polynomial.C (H 3 3)) := by
  dsimp only
  apply GeneralFourBlock.ext
  all_goals simp [GeneralFourBlock.ofSymmetricMatrix,
    quadraticAxisFourBlock, quadraticAxisReverseRees_originHessian_entry,
    topKernelMarkedAxisNatWeight]

/-- **The quadratic transverse-weight bound plus determinant one forces
an actual nonzero transverse 2x2 origin-Hessian minor of the SAME source.**

The six alternatives are all minors of the 3x3 principal transverse block;
in particular the conclusion is strictly stronger than a nonzero Hessian
entry. -/
theorem quadraticAxisReverseRees_sourceTransverseRankTwo
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let H := quadraticFamilyHessianMatrix F
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0 := by
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight 2 F hbound
  let H := quadraticFamilyHessianMatrix F
  let M := quadraticFamilyHessianMatrix Q
  have hnonneg : 2 * ∑ i : Fin 4, topKernelMarkedAxisNatWeight i ≤ 4 * 2 := by
    simp [Fin.sum_univ_four, topKernelMarkedAxisNatWeight]
  have hclock : HasPolynomialFamilyHessianDefect (K := K) Q 2 := by
    have h := reverseWeightedReesFamily_hasHessianDefect
      topKernelMarkedAxisNatWeight 2 F hbound hdet hnonneg
    simpa [Q, Fin.sum_univ_four, topKernelMarkedAxisNatWeight] using h
  have hdetM : M.det = (Polynomial.X : Polynomial K) ^ 2 := by
    dsimp [M]
    rw [quadraticFamilyHessianMatrix_det]
    rw [hclock]
    simp
  have hsymm : ∀ i k : Fin 4, M i k = M k i :=
    quadraticFamilyHessianMatrix_symmetric Q
  let B := GeneralFourBlock.ofSymmetricMatrix M
  have hB :
      B = quadraticAxisFourBlock (Polynomial.X : Polynomial K)
        (Polynomial.C (H 0 0))
        (Polynomial.C (H 0 1))
        (Polynomial.C (H 0 2))
        (Polynomial.C (H 0 3))
        (Polynomial.C (H 1 1))
        (Polynomial.C (H 1 2))
        (Polynomial.C (H 1 3))
        (Polynomial.C (H 2 2))
        (Polynomial.C (H 2 3))
        (Polynomial.C (H 3 3)) := by
    exact quadraticAxisReverseRees_originHessian_block F hbound
  have hdetB :
      (quadraticAxisFourBlock (Polynomial.X : Polynomial K)
        (Polynomial.C (H 0 0))
        (Polynomial.C (H 0 1))
        (Polynomial.C (H 0 2))
        (Polynomial.C (H 0 3))
        (Polynomial.C (H 1 1))
        (Polynomial.C (H 1 2))
        (Polynomial.C (H 1 3))
        (Polynomial.C (H 2 2))
        (Polynomial.C (H 2 3))
        (Polynomial.C (H 3 3))).determinantCore =
          (Polynomial.X : Polynomial K) ^ 2 := by
    rw [← hB]
    calc
      B.determinantCore = B.matrix.det :=
        (GeneralFourBlock.matrix_det B).symm
      _ = M.det := by
        rw [show B.matrix = M from
          GeneralFourBlock.matrix_ofSymmetricMatrix M hsymm]
      _ = (Polynomial.X : Polynomial K) ^ 2 := hdetM
  have hminor :=
    quadraticAxisFourBlock_exists_transverseMinor
      (Polynomial.X : Polynomial K)
      (Polynomial.C (H 0 0))
      (Polynomial.C (H 0 1))
      (Polynomial.C (H 0 2))
      (Polynomial.C (H 0 3))
      (Polynomial.C (H 1 1))
      (Polynomial.C (H 1 2))
      (Polynomial.C (H 1 3))
      (Polynomial.C (H 2 2))
      (Polynomial.C (H 2 3))
      (Polynomial.C (H 3 3))
      Polynomial.X_ne_zero hdetB
  simpa only [← map_mul, ← map_sub, Polynomial.C_ne_zero] using hminor

end

end HC4.Valuation
