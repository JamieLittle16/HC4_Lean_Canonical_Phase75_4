import HC4.Valuation.QuadraticTransverseCapSourceSingularClosure
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# The actual quadratic-cap represented-source transverse block over K(x)

The green singular-quadratic endpoint yields det C(x) != 0 as a
POLYNOMIAL for the reachable canonical E3 source. Hence the
source-axis transverse matrix C(x) is invertible over RatFunc K,
even though its polynomial determinant is not yet known to be a unit.

This constructs the genuine two-sided rational inverse directly
from the original source's Hessian, with no assumed inverse,
new source potential, or final-resolution producer.

The rational differential-field Riccati and affine-descent steps
may now consume this actual inverse instead of an abstract one.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The honest polynomial-to-rational-function embedding used for
the represented-source transverse Hessian. -/
noncomputable def quadraticTransverse_polynomialToRatFunc :
    Polynomial K →+* RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K)

/-- The canonical source-axis transverse Hessian, now genuinely
viewed as a 3x3 matrix over the rational-function field K(x). -/
noncomputable def quadraticTransverseCapSource_rationalThreeMatrix
    (F : MvPolynomial (Fin 4) K) :
    Matrix (Fin 3) (Fin 3) (RatFunc K) :=
  (quadraticTransverseCapSourceAxisThreeBlock F).matrix.map
    (quadraticTransverse_polynomialToRatFunc (K := K))

/-- The source polynomial transverse determinant remains nonzero
under the injective embedding K[x] -> K(x). -/
theorem quadraticTransverseCapSource_rationalThreeMatrix_det_ne_zero
    (F : MvPolynomial (Fin 4) K)
    (hdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0) :
    (quadraticTransverseCapSource_rationalThreeMatrix F).det ≠ 0 := by
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let f := quadraticTransverse_polynomialToRatFunc (K := K)
  change (C.matrix.map f).det ≠ 0
  have hmap :
      (C.matrix.map f).det = f C.determinantCore := by
    calc
      (C.matrix.map f).det = f C.matrix.det :=
        (f.map_det C.matrix).symm
      _ = f C.determinantCore := by rw [GeneralThreeBlock.matrix_det]
  rw [hmap]
  exact (RatFunc.algebraMap_ne_zero hdet)

/-- A nonzero polynomial transverse determinant constructs the
actual TWO-SIDED rational inverse of the represented source's
transverse Hessian matrix, without assuming polynomial integrality. -/
theorem quadraticTransverseCapSource_rationalThreeMatrix_inverse
    (F : MvPolynomial (Fin 4) K)
    (hdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0) :
    ∃ M : Matrix (Fin 3) (Fin 3) (RatFunc K),
      quadraticTransverseCapSource_rationalThreeMatrix F * M = 1 ∧
        M * quadraticTransverseCapSource_rationalThreeMatrix F = 1 := by
  let C := quadraticTransverseCapSource_rationalThreeMatrix F
  have hnonzero : C.det ≠ 0 :=
    quadraticTransverseCapSource_rationalThreeMatrix_det_ne_zero F hdet
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hnonzero
  exact ⟨C⁻¹, Matrix.mul_nonsing_inv hunit,
    Matrix.nonsing_inv_mul hunit⟩

end

end HC4.Valuation
