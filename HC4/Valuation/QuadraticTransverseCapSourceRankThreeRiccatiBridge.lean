import HC4.Valuation.QuadraticTransverseCapSourceRationalInverse
import HC4.Valuation.QuadraticTransverseCapRatFuncDerivationX
import Mathlib.Tactic

/-!
# Source-level rank-three Riccati-to-unit-determinant bridge

The source-honest singular-quadratic endpoint already gives
det C(x) != 0. We have therefore constructed its actual rational
inverse C(x)^(-1) over K(x).

This theorem connects that very same represented source matrix to
the differential-field rank-three rigidity lemmas:

If D is a genuine K-derivation of RatFunc K with D(X)=1 and the
quadratic Hessian source identity supplies the exact matrix
Riccati equation D²C=2(DC)C⁻¹(DC), then the actual polynomial
transverse Hessian has a two-sided inverse in K[x] and hence
a NONZERO CONSTANT determinant.

The Riccati equation is an explicit, source-indexed hypothesis:
it must still be extracted from the y² coefficient of
det(Hess F)=1. No gradient collision is silently used in this step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- **Actual represented-source rank-three integrality from its
Riccati coefficient equation.**

The only unproved inputs at this interface are the rational
X-derivation and the true source Riccati equation. Everything
else, including existence of the rational inverse, is derived
from the source polynomial determinant nonvanishing. -/
theorem quadraticTransverseCapSource_rationalRiccati_constantDet
    (F : MvPolynomial (Fin 4) K)
    (hdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hX : D (RatFunc.X : RatFunc K) = 1)
    (hRiccati :
      let C := quadraticTransverseCapSource_rationalThreeMatrix F
      let M := C⁻¹
      quadraticTransverse_fieldMatrixDerivative D
          (quadraticTransverse_fieldMatrixDerivative D C) =
        2 * ((quadraticTransverse_fieldMatrixDerivative D C * M) *
          quadraticTransverse_fieldMatrixDerivative D C)) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix * P = 1 ∧
        P * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1 ∧
          ∃ d : K, d ≠ 0 ∧
            (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore =
              Polynomial.C d := by
  let Cpoly := (quadraticTransverseCapSourceAxisThreeBlock F).matrix
  let Crat := quadraticTransverseCapSource_rationalThreeMatrix F
  let M := Crat⁻¹
  have hnonzero : Crat.det ≠ 0 :=
    quadraticTransverseCapSource_rationalThreeMatrix_det_ne_zero F hdet
  have hunit : IsUnit Crat.det := isUnit_iff_ne_zero.mpr hnonzero
  have hCM :
      Cpoly.map (algebraMap (Polynomial K) (RatFunc K)) * M = 1 := by
    change Crat * Crat⁻¹ = 1
    exact Matrix.mul_nonsing_inv Crat hunit
  have hMC :
      M * Cpoly.map (algebraMap (Polynomial K) (RatFunc K)) = 1 := by
    change Crat⁻¹ * Crat = 1
    exact Matrix.nonsing_inv_mul Crat hunit
  obtain ⟨P, hCP, hPC, d, hd, hDconst⟩ :=
    quadraticTransverse_ratFuncRiccati_polynomialInverse_of_derivation_X
      D hX Cpoly M hCM hMC hRiccati
  refine ⟨P, hCP, hPC, d, hd, ?_⟩
  calc
    (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore =
        Cpoly.det := (GeneralThreeBlock.matrix_det _).symm
    _ = Polynomial.C d := hDconst

end

end HC4.Valuation
