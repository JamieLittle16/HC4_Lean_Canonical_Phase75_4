import HC4.Valuation.QuadraticTransverseCapRatFuncCanonicalDerivation
import HC4.Valuation.QuadraticTransverseCapRankThreeReciprocalODE
import Mathlib.Tactic

/-!
# A source-level regular quadratic-cap rigidity theorem

Under only the original four-variable quadratic transverse cap,
det Hess F = 1, and generic nonsingularity of the actual transverse
Hessian, its polynomial inverse is not arbitrary: EVERY entry is
affine in the longitudinal variable.

This is a complete structural classification of the inverse
transverse Hessian of the original source in the regular branch.
No Riccati equation, abstract derivation or polynomial inverse is
introduced as an extra hypothesis. The full gradient inversion is
still a separate endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- **Source-level affine inverse transverse Hessian.**

If the actual source F has transverse cap two and constant
unit full Hessian determinant, and its transverse Hessian
C(x) has nonzero determinant as a polynomial, then there exist
constant ground-field matrices A,B with

    C(x) * (A + x B) = (A + x B) * C(x) = I.

The proof derives the polynomial inverse, matrix Riccati equation,
and reciprocal second-derivative rigidity from F. -/
theorem quadraticTransverseCapSource_regularAffineInverse
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0) :
    ∃ (P : Matrix (Fin 3) (Fin 3) (Polynomial K))
      (A B : Matrix (Fin 3) (Fin 3) K),
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix * P = 1 ∧
      P * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1 ∧
      (∀ i j : Fin 3,
        P i j = Polynomial.C (A i j) +
          Polynomial.C (B i j) * Polynomial.X) := by
  classical
  let T := quadraticTransverseCapSourceAxisThreeBlock F
  let C : Matrix (Fin 3) (Fin 3) (Polynomial K) := T.matrix
  let C' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    quadraticTransverse_polynomialMatrixDerivative C
  let C'' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    quadraticTransverse_polynomialMatrixDerivative C'
  obtain ⟨P, hCP, hPC, d, hdn, hD⟩ :=
    quadraticTransverseCapSource_regularPolynomialInverse
      F hcap hdet hregular
  have hdetEq : C.det = Polynomial.C d := by
    calc
      C.det = T.determinantCore := GeneralThreeBlock.matrix_det T
      _ = Polynomial.C d := hD
  have hdetNZ : C.det ≠ 0 := by
    rw [hdetEq]
    exact Polynomial.C_ne_zero.mpr hdn
  have hAdj : C.adjugate = C.det • P := by
    calc
      C.adjugate = (P * C) * C.adjugate := by rw [hPC, one_mul]
      _ = P * (C * C.adjugate) := by rw [mul_assoc]
      _ = P * (C.det • (1 : Matrix (Fin 3) (Fin 3) (Polynomial K))) := by
        rw [Matrix.mul_adjugate]
      _ = C.det • P := by rw [Matrix.mul_smul, mul_one]
  have hsource :=
    quadraticTransverseCapSource_matrixRiccati F hcap hdet
  have hsource' :
      C.det • C'' =
        (2 : Polynomial K) • ((C' * C.adjugate) * C') := by
    simpa only [C', C'', C,
      quadraticTransverse_polynomialMatrixDerivative] using hsource
  have hscaled :
      ((C' * C.adjugate) * C') =
        C.det • ((C' * P) * C') := by
    calc
      (C' * C.adjugate) * C' =
          (C' * (C.det • P)) * C' := by rw [hAdj]
      _ = C.det • ((C' * P) * C') := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hscaled] at hsource'
  have hRiccati :
      C'' = (2 : Polynomial K) • ((C' * P) * C') := by
    apply Matrix.ext
    intro i j
    change C'' i j = (2 : Polynomial K) * (((C' * P) * C') i j)
    have hi := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) (Polynomial K) => M i j)
      hsource'
    change C.det * C'' i j =
      (2 : Polynomial K) * (C.det * ((C' * P) * C') i j) at hi
    apply mul_left_cancel₀ hdetNZ
    calc
      C.det * C'' i j =
          (2 : Polynomial K) * (C.det * ((C' * P) * C') i j) := hi
      _ = C.det * (2 * ((C' * P) * C') i j) := by ring
  have hRiccatiMatrix :
      C'' = 2 * ((C' * P) * C') := by
    simpa only [two_mul, two_smul] using hRiccati
  obtain ⟨A, B, hAffine⟩ :=
    quadraticTransverse_reciprocal_polynomial_affine
      C P hCP hPC (by
        simpa [C', C'', quadraticTransverse_polynomialMatrixDerivative]
          using hRiccatiMatrix)
  exact ⟨P, A, B, hCP, hPC, hAffine⟩

end

end HC4.Valuation
