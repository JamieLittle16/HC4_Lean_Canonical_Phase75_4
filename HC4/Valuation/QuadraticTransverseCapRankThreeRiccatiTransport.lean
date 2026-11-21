import HC4.Valuation.QuadraticTransverseCapSourceRiccatiMatrix
import HC4.Valuation.QuadraticTransverseCapRankThreeFieldDerivation
import Mathlib.Tactic

/-!
# Denominator-cleared polynomial Riccati -> genuine differential-field Riccati

The determinant-one SOURCE has already supplied the polynomial
matrix equation

    (det C) C'' = 2 C' adj(C) C'.

An injective polynomial embedding f into a differential field L
whose derivation differentiates all embedded polynomials transports
this equation to

    D²(fC) = 2 (D(fC)) M (D(fC))

for the genuine two-sided inverse M of fC. The proof cancels
f(det C), which is nonzero by the *actual* green E3 generic-rank-
three theorem. No polynomial inverse is assumed.

This removes the previously explicit Riccati input from the
affine-rational inverse chain; the only remaining input is an
ordinary rational-function X-derivation.
-/

namespace HC4.Valuation

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The denominator-cleared source Riccati identity automatically
transports to the genuine rational inverse over ANY differential
coefficient field with compatible polynomial differentiation. -/
theorem quadraticTransverse_clearedRiccati_fieldRiccati
    (f : Polynomial K →+* L)
    (hf : Function.Injective f)
    (D : Derivation K L L)
    (hpoly : ∀ p : Polynomial K,
      D (f p) = f (Polynomial.derivative p))
    (C : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (M : Matrix (Fin 3) (Fin 3) L)
    (hdet : C.det ≠ 0)
    (hCM : C.map f * M = 1)
    (hMC : M * C.map f = 1)
    (hcleared :
      C.det • quadraticTransverse_polynomialMatrixDerivative
          (quadraticTransverse_polynomialMatrixDerivative C) =
        2 • (quadraticTransverse_polynomialMatrixDerivative C *
          C.adjugate * quadraticTransverse_polynomialMatrixDerivative C)) :
    quadraticTransverse_fieldMatrixDerivative D
        (quadraticTransverse_fieldMatrixDerivative D (C.map f)) =
      2 * ((quadraticTransverse_fieldMatrixDerivative D (C.map f) * M) *
        quadraticTransverse_fieldMatrixDerivative D (C.map f)) := by
  let A := C.map f
  let P := quadraticTransverse_polynomialMatrixDerivative C
  let Q := quadraticTransverse_polynomialMatrixDerivative P
  let U := quadraticTransverse_fieldMatrixDerivative D A
  have hU : U = P.map f := by
    ext i j
    simp [U, A, P, quadraticTransverse_fieldMatrixDerivative,
      quadraticTransverse_polynomialMatrixDerivative, hpoly]
  have hV :
      quadraticTransverse_fieldMatrixDerivative D U = Q.map f := by
    rw [hU]
    ext i j
    simp [Q, P, quadraticTransverse_fieldMatrixDerivative,
      quadraticTransverse_polynomialMatrixDerivative, hpoly]
  have hdetA : A.det = f C.det := by
    exact (f.map_det C).symm
  have hdetA0 : A.det ≠ 0 := by
    rw [hdetA]
    exact (map_ne_zero_iff f hf).mpr hdet
  have hAdj : A.adjugate = A.det • M := by
    calc
      A.adjugate = (M * A) * A.adjugate := by rw [hMC, one_mul]
      _ = M * (A * A.adjugate) := by rw [mul_assoc]
      _ = M * (A.det • 1) := by rw [Matrix.mul_adjugate]
      _ = A.det • M := by simp [Matrix.mul_smul]
  have hmap : A.det • (Q.map f) =
      2 • (P.map f * A.adjugate * P.map f) := by
    calc
      A.det • (Q.map f) = (C.det • Q).map f := by
        rw [hdetA]
        ext i j
        simp [Matrix.smul_apply]
      _ = (2 • (P * C.adjugate * P)).map f := by
        exact congrArg (fun Z : Matrix (Fin 3) (Fin 3) (Polynomial K) =>
          Z.map f) hcleared
      _ = 2 • (P.map f * A.adjugate * P.map f) := by
        calc
          (2 • (P * C.adjugate * P)).map f =
              2 • ((P * C.adjugate * P).map f) := by
                apply Matrix.ext
                intro i j
                simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]
          _ = 2 • (P.map f * A.adjugate * P.map f) := by
                have hadjMap : C.adjugate.map f = A.adjugate := by
                  simpa only [A] using (RingHom.map_adjugate f C)
                rw [Matrix.map_mul, Matrix.map_mul, hadjMap]
  have hcancel :
      A.det • (Q.map f) =
        A.det • (2 • (U * M * U)) := by
    rw [hU, hAdj] at *
    convert hmap using 1
    simp [Matrix.mul_smul, Matrix.smul_mul, smul_comm, smul_smul]
  have hmatrix : Q.map f = 2 • (U * M * U) := by
    ext i j
    have h := congrArg
      (fun Z : Matrix (Fin 3) (Fin 3) L => Z i j) hcancel
    simpa only [Matrix.smul_apply] using
      (mul_left_cancel₀ hdetA0 h)
  rw [← hV] at hmatrix
  simpa [U, smul_eq_mul] using hmatrix

end

end HC4.Valuation
