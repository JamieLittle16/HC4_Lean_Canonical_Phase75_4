import HC4.Valuation.QuadraticTransverseCapRankThreeRiccatiTransport
import HC4.Valuation.QuadraticTransverseCapSourceRankThreeRiccatiBridge
import Mathlib.Tactic

/-!
# Actual source Riccati over K(x), with NO Riccati hypothesis

The original determinant-one source supplies its polynomial Riccati
identity in K[x]. Its generic-rank-three transverse determinant
is nonzero. This module transports the resulting matrix identity
through any honest rational-function derivation D with D(X)=1.

Thus, in the quadratic cap-two branch, the rational Riccati
equation is now a CONCLUSION of the original source, not an input.
The sole remaining rational-differential infrastructure is the
construction of the canonical X-derivation on RatFunc K.

This also establishes that once D is constructed, the actual
source transverse Hessian has an inverse in K[x] and therefore
constant nonzero determinant, with no additional geometric
hypotheses or endpoint producer.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- **No assumed Riccati coefficient:** the exact represented-source
Hessian determinant-one identity and cap two force the true
rational-matrix Riccati equation over K(x). -/
theorem quadraticTransverseCap_two_sourceRiccati_rational
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hHessDet : HC4.Polynomial.hessianDeterminant F = 1)
    (hCdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hX : D (RatFunc.X : RatFunc K) = 1) :
    let A := quadraticTransverseCapSource_rationalThreeMatrix F
    let M := A⁻¹
    quadraticTransverse_fieldMatrixDerivative D
        (quadraticTransverse_fieldMatrixDerivative D A) =
      2 * ((quadraticTransverse_fieldMatrixDerivative D A * M) *
        quadraticTransverse_fieldMatrixDerivative D A) := by
  dsimp only
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let P := C.matrix
  let A := quadraticTransverseCapSource_rationalThreeMatrix F
  let M := A⁻¹
  let f : Polynomial K →+* RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K)
  have hPdet : P.det ≠ 0 := by
    rw [GeneralThreeBlock.matrix_det]
    exact hCdet
  have hA : A.det ≠ 0 :=
    quadraticTransverseCapSource_rationalThreeMatrix_det_ne_zero
      F hCdet
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hAM : P.map f * M = 1 := by
    change A * A⁻¹ = 1
    exact Matrix.mul_nonsing_inv A hunit
  have hMA : M * P.map f = 1 := by
    change A⁻¹ * A = 1
    exact Matrix.nonsing_inv_mul A hunit
  have hcleared :
      P.det • quadraticTransverse_polynomialMatrixDerivative
          (quadraticTransverse_polynomialMatrixDerivative P) =
        2 • (quadraticTransverse_polynomialMatrixDerivative P *
          P.adjugate * quadraticTransverse_polynomialMatrixDerivative P) := by
    have hsrc :=
      quadraticTransverseCap_two_sourceRiccati_matrixCleared
        F hbound hHessDet
    simpa [C, P, GeneralThreeBlock.matrix_det] using hsrc
  exact quadraticTransverse_clearedRiccati_fieldRiccati
    f (RatFunc.algebraMap_injective K)
    D (quadraticTransverse_ratFunc_derivation_polynomialCompatibility
      D hX)
    P M hPdet hAM hMA hcleared

/-- **Source-level generic-rank-three constant determinant**, requiring
ONLY construction of the actual rational X-derivation.

The polynomial inverse is derived from the genuine Hessian's
Riccati coefficient, its existing rational inverse, and rational
field constants. No abstract Riccati or integrality assumption
remains. -/
theorem quadraticTransverseCap_two_source_constantDet_of_ratFuncDerivation
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hHessDet : HC4.Polynomial.hessianDeterminant F = 1)
    (hCdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hX : D (RatFunc.X : RatFunc K) = 1) :
    ∃ A : Matrix (Fin 3) (Fin 3) (Polynomial K),
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix * A = 1 ∧
      A * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1 ∧
        ∃ d : K, d ≠ 0 ∧
          (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore =
            Polynomial.C d := by
  exact quadraticTransverseCapSource_rationalRiccati_constantDet
    F hCdet D hX
    (quadraticTransverseCap_two_sourceRiccati_rational
      F hbound hHessDet hCdet D hX)

end

end HC4.Valuation
