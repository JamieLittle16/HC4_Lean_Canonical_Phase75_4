import HC4.Valuation.QuadraticTransverseCapSourceRiccatiLinear
import HC4.Valuation.QuadraticTransverseCapRankThreeAffineVectorCollision
import Mathlib.Tactic

/-!
# Source-honest linear Riccati equation as a polynomial matrix-vector identity

The y-linear Hessian determinant coefficient of the original
quadratic-transverse source was already proved in three explicit
adjugate-vector components.  This file collects those three
equalities into a single equation on the *actual* vector b'(x):

  det(C) * b'' = 2 C' adj(C) b'.

No inverse or Riccati coefficient is assumed.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
variable {K : Type*} [Field K] [CharZero K]

/-- The explicit adjugate pairing in the source equation is
the ordinary (P * adj(C)) matrix-vector product. -/
theorem quadraticTransverse_threeBlock_linearAdjugatePairing
    (G : GeneralThreeBlock (Polynomial K))
    (P : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (v : Fin 3 → Polynomial K)
    (i : Fin 3) :
    (P * G.matrix.adjugate).mulVec v i =
      P i 0 * quadraticTransverseAdjugateVector0 G (v 0) (v 1) (v 2) +
      P i 1 * quadraticTransverseAdjugateVector1 G (v 0) (v 1) (v 2) +
      P i 2 * quadraticTransverseAdjugateVector2 G (v 0) (v 1) (v 2) := by
  classical
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Matrix.mul_apply,
      Fin.sum_univ_three, GeneralThreeBlock.matrix,
      Matrix.adjugate_fin_three,
      quadraticTransverseAdjugateVector0,
      quadraticTransverseAdjugateVector1,
      quadraticTransverseAdjugateVector2] <;>
    ring

/-- The exact source linear Riccati equation, now in matrix-vector
notation. The polynomial Hessian C, source coefficient vector b,
and its derivatives all refer to the same original potential F. -/
theorem quadraticTransverseCap_two_sourceRiccati_linearMatrixCleared
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let G := quadraticTransverseCapSourceAxisThreeBlock F
    let C := G.matrix
    let b := quadraticTransverseCapSourceLinearCoefficients F
    let v := quadraticTransverse_polynomialVectorDerivative b
    let P := quadraticTransverse_polynomialMatrixDerivative C
    ∀ i : Fin 3,
      C.det * (quadraticTransverse_polynomialVectorDerivative v) i =
        2 * ((P * C.adjugate).mulVec v) i := by
  dsimp only
  let G := quadraticTransverseCapSourceAxisThreeBlock F
  let C := G.matrix
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let v := quadraticTransverse_polynomialVectorDerivative b
  let P := quadraticTransverse_polynomialMatrixDerivative C
  have hsym (i j : Fin 3) :
      Polynomial.derivative (C i j) =
        Polynomial.derivative (C j i) := by
    fin_cases i <;> fin_cases j <;>
      simp [C, GeneralThreeBlock.matrix]
  intro i
  have hsrc :=
    quadraticTransverseCap_two_sourceRiccati_linearCleared
      F hbound hdet i
  dsimp only at hsrc
  have hpair :
      ((P * C.adjugate).mulVec v) i =
        Polynomial.derivative (C 0 i) *
          quadraticTransverseAdjugateVector0 G (v 0) (v 1) (v 2) +
        Polynomial.derivative (C 1 i) *
          quadraticTransverseAdjugateVector1 G (v 0) (v 1) (v 2) +
        Polynomial.derivative (C 2 i) *
          quadraticTransverseAdjugateVector2 G (v 0) (v 1) (v 2) := by
    have hp := quadraticTransverse_threeBlock_linearAdjugatePairing
      G P v i
    change
      ((P * G.matrix.adjugate).mulVec v) i =
        Polynomial.derivative (C 0 i) *
            quadraticTransverseAdjugateVector0 G (v 0) (v 1) (v 2) +
          Polynomial.derivative (C 1 i) *
            quadraticTransverseAdjugateVector1 G (v 0) (v 1) (v 2) +
          Polynomial.derivative (C 2 i) *
            quadraticTransverseAdjugateVector2 G (v 0) (v 1) (v 2)
    rw [hp]
    change
      Polynomial.derivative (C i 0) *
          quadraticTransverseAdjugateVector0 G (v 0) (v 1) (v 2) +
        Polynomial.derivative (C i 1) *
          quadraticTransverseAdjugateVector1 G (v 0) (v 1) (v 2) +
        Polynomial.derivative (C i 2) *
          quadraticTransverseAdjugateVector2 G (v 0) (v 1) (v 2) = _
    rw [hsym i 0, hsym i 1, hsym i 2]
  rw [GeneralThreeBlock.matrix_det]
  rw [hpair]
  simpa only [v, b, C,
    quadraticTransverse_polynomialVectorDerivative] using hsrc

end
end HC4.Valuation
