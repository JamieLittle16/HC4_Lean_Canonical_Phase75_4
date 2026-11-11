import HC4.Valuation.QuadraticTransverseCapSourceRiccatiRational
import HC4.Valuation.QuadraticTransverseCapRankThreeAffineDet
import Mathlib.Tactic

/-!
# Rank-three polynomial reciprocal: affine and nilpotent normal form

From the *actual* quadratic-cap source's polynomial inverse and
denominator-cleared Riccati identity, derive an affine inverse with
a cubic-nilpotent normalized slope.  No new Riccati, derivation, or
integrality hypothesis enters this source-level result.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial inversion and cleared Riccati force the inverse to
be affine.  Cancellation is justified by det(C) ≠ 0, which follows
from its given polynomial inverse. -/
theorem quadraticTransverse_polynomialInverse_affine_of_clearedRiccati
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCM : C * M = 1)
    (hMC : M * C = 1)
    (hcleared :
      C.det • quadraticTransverse_polynomialMatrixDerivative
          (quadraticTransverse_polynomialMatrixDerivative C) =
        2 • (quadraticTransverse_polynomialMatrixDerivative C *
          C.adjugate * quadraticTransverse_polynomialMatrixDerivative C)) :
    ∃ A B : Matrix (Fin 3) (Fin 3) K,
      ∀ i j : Fin 3,
        M i j = Polynomial.C (A i j) +
          Polynomial.C (B i j) * Polynomial.X := by
  let P := quadraticTransverse_polynomialMatrixDerivative C
  let Q := quadraticTransverse_polynomialMatrixDerivative P
  have hdetprod : C.det * M.det = 1 := by
    have h := congrArg Matrix.det hCM
    simpa [Matrix.det_mul] using h
  have hdet : C.det ≠ 0 := by
    intro hz
    rw [hz] at hdetprod
    simp at hdetprod
  have hAdj : C.adjugate = C.det • M := by
    calc
      C.adjugate = (M * C) * C.adjugate := by rw [hMC, one_mul]
      _ = M * (C * C.adjugate) := by rw [mul_assoc]
      _ = M * (C.det • 1) := by rw [Matrix.mul_adjugate]
      _ = C.det • M := by simp
  have hcancel : C.det • Q = C.det • (2 • (P * M * P)) := by
    rw [hAdj] at hcleared
    change C.det • Q = 2 • (P * (C.det • M) * P) at hcleared
    calc
      C.det • Q = 2 • (P * (C.det • M) * P) := hcleared
      _ = 2 • ((C.det • (P * M)) * P) := by
        rw [Matrix.mul_smul]
      _ = 2 • (C.det • (P * M * P)) := by
        rw [Matrix.smul_mul]
      _ = C.det • (2 • (P * M * P)) :=
        smul_comm (2 : ℕ) C.det (P * M * P)
  have hmatrix : Q = 2 • (P * M * P) := by
    apply Matrix.ext
    intro i j
    have h := congrArg
      (fun Z : Matrix (Fin 3) (Fin 3) (Polynomial K) => Z i j) hcancel
    exact mul_left_cancel₀ hdet
      (by simpa only [Matrix.smul_apply] using h)
  have hRiccati :
      quadraticTransverse_polynomialMatrixDerivative
          (quadraticTransverse_polynomialMatrixDerivative C) =
        2 * ((quadraticTransverse_polynomialMatrixDerivative C * M) *
          quadraticTransverse_polynomialMatrixDerivative C) := by
    simpa [P, Q, smul_eq_mul] using hmatrix
  exact quadraticTransverse_reciprocal_polynomial_affine
    C M hCM hMC hRiccati

/-- The affine polynomial inverse of a polynomially invertible 3x3
matrix has cubic-nilpotent normalized slope, constructed by evaluating
its reciprocal at X=0. -/
theorem quadraticTransverse_polynomialAffineInverse_nilpotentSlope
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCM : C * M = 1)
    (hMC : M * C = 1)
    (hAffine :
      ∃ A B : Matrix (Fin 3) (Fin 3) K,
        ∀ i j : Fin 3,
          M i j = Polynomial.C (A i j) +
            Polynomial.C (B i j) * Polynomial.X) :
    ∃ A B N : Matrix (Fin 3) (Fin 3) K,
      (∀ i j : Fin 3,
        M i j = Polynomial.C (A i j) +
          Polynomial.C (B i j) * Polynomial.X) ∧
      B = A * N ∧ N ^ 3 = 0 := by
  obtain ⟨A, B, hAB⟩ := hAffine
  let e : Polynomial K →+* K := Polynomial.evalRingHom 0
  let C₀ : Matrix (Fin 3) (Fin 3) K := C.map e
  have hM :
      M = A.map Polynomial.C +
          (Polynomial.X : Polynomial K) • B.map Polynomial.C := by
    apply Matrix.ext
    intro i j
    change M i j = Polynomial.C (A i j) +
      (Polynomial.X : Polynomial K) * Polynomial.C (B i j)
    rw [mul_comm (Polynomial.X : Polynomial K) (Polynomial.C (B i j))]
    exact hAB i j
  have hM₀ : M.map e = A := by
    rw [hM]
    apply Matrix.ext
    intro i j
    simp [e, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul]
  have hAC₀ : A * C₀ = 1 := by
    have h := congrArg
      (fun Z : Matrix (Fin 3) (Fin 3) (Polynomial K) => Z.map e) hMC
    change (M * C).map e = (1 : Matrix (Fin 3) (Fin 3) (Polynomial K)).map e at h
    rw [Matrix.map_mul, Matrix.map_one, hM₀] at h
    · exact h
    · exact map_zero e
    · exact map_one e
  let N : Matrix (Fin 3) (Fin 3) K := C₀ * B
  have hB : B = A * N := by
    dsimp [N]
    rw [← mul_assoc, hAC₀, one_mul]
  obtain ⟨d, hd, hdetM⟩ :=
    quadraticTransverse_polynomialMatrixInverse_det_constant
      M C hMC
  have hdet_eval : A.det = d := by
    have he := (e.map_det M).symm
    change (M.map e).det = e M.det at he
    rw [hM₀, hdetM] at he
    simpa [e] using he
  have hdetA : A.det ≠ 0 := by
    rw [hdet_eval]
    exact hd
  have hAffineDet :
      (A.map Polynomial.C +
        (Polynomial.X : Polynomial K) • B.map Polynomial.C).det =
          Polynomial.C A.det := by
    rw [← hM, hdetM, hdet_eval]
  have hN : N ^ 3 = 0 :=
    quadraticTransverse_affineMatrix_nilpotentSlope
      A B N hdetA hB hAffineDet
  exact ⟨A, B, N, hAB, hB, hN⟩

/-- Actual source-level affine reciprocal and nilpotent slope in
the generically rank-three quadratic-cap branch. -/
theorem quadraticTransverseCap_two_source_nilpotentAffineInverse
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hHessDet : HC4.Polynomial.hessianDeterminant F = 1)
    (hCdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0) :
    ∃ (M : Matrix (Fin 3) (Fin 3) (Polynomial K))
      (A B N : Matrix (Fin 3) (Fin 3) K),
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix * M = 1 ∧
      M * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1 ∧
      (∀ i j : Fin 3,
        M i j = Polynomial.C (A i j) +
          Polynomial.C (B i j) * Polynomial.X) ∧
      B = A * N ∧ N ^ 3 = 0 := by
  let C := (quadraticTransverseCapSourceAxisThreeBlock F).matrix
  obtain ⟨M, hCM, hMC, _d, _hd, _hdet⟩ :=
    quadraticTransverseCap_two_source_constantDet
      F hbound hHessDet hCdet
  have hcleared :
      C.det • quadraticTransverse_polynomialMatrixDerivative
          (quadraticTransverse_polynomialMatrixDerivative C) =
        2 • (quadraticTransverse_polynomialMatrixDerivative C *
          C.adjugate * quadraticTransverse_polynomialMatrixDerivative C) := by
    simpa only [C, GeneralThreeBlock.matrix_det] using
      (quadraticTransverseCap_two_sourceRiccati_matrixCleared
        F hbound hHessDet)
  have hAffine :=
    quadraticTransverse_polynomialInverse_affine_of_clearedRiccati
      C M hCM hMC hcleared
  obtain ⟨A, B, N, hAB, hB, hN⟩ :=
    quadraticTransverse_polynomialAffineInverse_nilpotentSlope
      C M hCM hMC hAffine
  exact ⟨M, A, B, N, hCM, hMC, hAB, hB, hN⟩

end
end HC4.Valuation
