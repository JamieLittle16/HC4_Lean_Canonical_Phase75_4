import HC4.Valuation.QuadraticTransverseCapSourceRiccatiLinear
import HC4.Valuation.QuadraticTransverseCapRankThreeAffineInverse
import Mathlib.Tactic

/-!
# From nine actual source coefficient identities to one matrix Riccati equation

The source-level y² Schur coefficient has been proved without any
abstract Riccati hypothesis. This file collects its nine concrete
univariate identities into the canonical matrix equation

  det C • C'' = 2 • (C' * adj(C) * C').

All objects are POLYNOMIAL matrices over K[x]; the three-by-three
matrix C is the transverse Hessian of the actual four-variable
represented source. There is no inverse, rational derivation, or
rank-three hypothesis in the result.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

set_option maxHeartbeats 1000000

/-- The explicit three-by-three adjugate quadratic pairing occurring
in the source Schur coefficient equals the corresponding ordinary
matrix product. This ring identity is independent of the source. -/
theorem quadraticTransverse_threeBlock_adjugatePairing_eq_matrixProduct
    {R : Type*} [CommRing R]
    (C : GeneralThreeBlock R)
    (P : Matrix (Fin 3) (Fin 3) R)
    (i j : Fin 3) :
    (P * C.matrix.adjugate * P) i j =
      P i 0 * quadraticTransverseAdjugateVector0 C
        (P 0 j) (P 1 j) (P 2 j) +
      P i 1 * quadraticTransverseAdjugateVector1 C
        (P 0 j) (P 1 j) (P 2 j) +
      P i 2 * quadraticTransverseAdjugateVector2 C
        (P 0 j) (P 1 j) (P 2 j) := by
  classical
  simp [Matrix.mul_apply, Fin.sum_univ_three,
    GeneralThreeBlock.matrix, Matrix.adjugate_fin_three,
    quadraticTransverseAdjugateVector0,
    quadraticTransverseAdjugateVector1,
    quadraticTransverseAdjugateVector2] <;> ring

/-- The original source's *polynomial* transverse Hessian satisfies
the full rank-three Riccati equation with determinant clearing.

The determinant-one and whole-source quadratic cap are exactly the
source-derived hypotheses. The equation is NOT assumed. -/
theorem quadraticTransverseCap_two_sourceRiccati_matrixCleared
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    let A := C.matrix
    C.determinantCore •
      quadraticTransverse_polynomialMatrixDerivative
        (quadraticTransverse_polynomialMatrixDerivative A) =
      2 • (quadraticTransverse_polynomialMatrixDerivative A *
        A.adjugate * quadraticTransverse_polynomialMatrixDerivative A) := by
  dsimp only
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let A := C.matrix
  let P := quadraticTransverse_polynomialMatrixDerivative A
  let Q := quadraticTransverse_polynomialMatrixDerivative P
  apply Matrix.ext
  intro i j
  have hsrc :=
    quadraticTransverseCap_two_sourceRiccati_cleared F hbound hdet i j
  dsimp only at hsrc
  have hsym (a b : Fin 3) : A a b = A b a := by
    fin_cases a <;> fin_cases b <;>
      simp [A, C, GeneralThreeBlock.matrix]
  have hP (a b : Fin 3) : P a b = P b a := by
    simp [P, quadraticTransverse_polynomialMatrixDerivative,
      hsym a b]
  have hpair :=
    quadraticTransverse_threeBlock_adjugatePairing_eq_matrixProduct C P i j
  have hpairs :
      (P * A.adjugate * P) i j =
        P 0 i * quadraticTransverseAdjugateVector0 C
          (P 0 j) (P 1 j) (P 2 j) +
        P 1 i * quadraticTransverseAdjugateVector1 C
          (P 0 j) (P 1 j) (P 2 j) +
        P 2 i * quadraticTransverseAdjugateVector2 C
          (P 0 j) (P 1 j) (P 2 j) := by
    simpa only [hP i 0, hP i 1, hP i 2] using hpair
  simp only [Matrix.smul_apply, smul_eq_mul]
  change C.determinantCore * Q i j =
    2 * (P * A.adjugate * P) i j
  rw [hpairs]
  simpa [P, Q, A,
    quadraticTransverse_polynomialMatrixDerivative] using hsrc

end

end HC4.Valuation
