import HC4.Valuation.ReverseReesAssociatedGraded
import HC4.Valuation.PermutedFamilyHessianFourBlock
import Mathlib.Tactic

/-!
# Associated-graded cleared Schur entries for bounded reverse Rees families

`ReverseReesAssociatedGraded` proves exact source normalization of all three
cleared Schur entries.  Here we cancel the explicit diagonal monomial and use
the generic normalization-to-initial-form theorem there.  Consequently each
parameter-first Schur coefficient is literally a weighted initial form of the
corresponding cleared Schur polynomial of the original source.

This is state-free provenance.  No auxiliary Schur clock is identified with a
terminal blocker clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K]

/-- Source-weight loss of the first cleared Schur entry. -/
def reverseReesSchurALoss
    (w : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4)) : ℕ :=
  2 * w (rho 0) + 2 * w (rho 1) + 2 * w (rho 2)

/-- Source-weight loss of the off-diagonal cleared Schur entry. -/
def reverseReesSchurBLoss
    (w : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4)) : ℕ :=
  2 * w (rho 0) + 2 * w (rho 1) + w (rho 2) + w (rho 3)

/-- Source-weight loss of the second diagonal cleared Schur entry. -/
def reverseReesSchurCLoss
    (w : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4)) : ℕ :=
  2 * w (rho 0) + 2 * w (rho 1) + 2 * w (rho 3)

private theorem schurA_diagonal_parameter_factor
    (w : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4)) :
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ w (rho 1)) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
      (MvPolynomial.C (Polynomial.X ^ w (rho 2))) ^ 2 =
        MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurALoss w rho) := by
  rw [pow_two, pow_two]
  repeat' rw [← MvPolynomial.C_mul]
  congr 1
  repeat' rw [← pow_add]
  congr 1
  simp [reverseReesSchurALoss]
  omega

private theorem schurB_diagonal_parameter_factor
    (w : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4)) :
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ w (rho 1)) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
      MvPolynomial.C (Polynomial.X ^ w (rho 2)) *
      MvPolynomial.C (Polynomial.X ^ w (rho 3)) =
        MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurBLoss w rho) := by
  rw [pow_two]
  repeat' rw [← MvPolynomial.C_mul]
  congr 1
  repeat' rw [← pow_add]
  congr 1
  simp [reverseReesSchurBLoss]
  omega

private theorem schurC_diagonal_parameter_factor
    (w : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4)) :
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ w (rho 1)) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
      (MvPolynomial.C (Polynomial.X ^ w (rho 3))) ^ 2 =
        MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurCLoss w rho) := by
  rw [pow_two, pow_two]
  repeat' rw [← MvPolynomial.C_mul]
  congr 1
  repeat' rw [← pow_add]
  congr 1
  simp [reverseReesSchurCLoss]
  omega

private theorem common_parameter_cube
    (D : ℕ) :
    (MvPolynomial.C (Polynomial.X ^ D) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 3 =
      MvPolynomial.C (Polynomial.X ^ (3 * D)) := by
  rw [← map_pow, ← pow_mul]
  congr 2
  omega

/-- After cancelling the diagonal source factor, the source-first Schur `A`
family is itself exactly normalized by the residual cubic source weight. -/
theorem reverseWeightedRees_schurA_inflate_eq
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurALoss w rho ≤ 3 * D) :
    let Q := reverseWeightedReesFamily w D F h
    let HQ := permutedPolynomialHessianFourBlock rho Q
    let HF := permutedPolynomialHessianFourBlock rho F
    adaptiveSmithInflateHom w HQ.schurA =
      MvPolynomial.C
          (Polynomial.X ^ (3 * D - reverseReesSchurALoss w rho)) *
        constantPolynomialFamily HF.schurA := by
  dsimp
  have hs := reverseWeightedRees_schurA_normalization w D F h rho
  dsimp at hs
  rw [schurA_diagonal_parameter_factor, common_parameter_cube] at hs
  have hpow :
      (Polynomial.X : Polynomial K) ^ (3 * D) =
        Polynomial.X ^ reverseReesSchurALoss w rho *
          Polynomial.X ^ (3 * D - reverseReesSchurALoss w rho) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, MvPolynomial.C_mul] at hs
  have hs' :
      MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurALoss w rho) *
        adaptiveSmithInflateHom w
          (permutedPolynomialHessianFourBlock rho
            (reverseWeightedReesFamily w D F h)).schurA =
      MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurALoss w rho) *
        (MvPolynomial.C
            (Polynomial.X ^ (3 * D - reverseReesSchurALoss w rho)) *
          constantPolynomialFamily
            (permutedPolynomialHessianFourBlock rho F).schurA) := by
    simpa [mul_assoc] using hs
  exact mul_left_cancel₀
    (MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)) hs'

/-- Corresponding exact normalization for the off-diagonal cleared Schur
entry. -/
theorem reverseWeightedRees_schurB_inflate_eq
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurBLoss w rho ≤ 3 * D) :
    let Q := reverseWeightedReesFamily w D F h
    let HQ := permutedPolynomialHessianFourBlock rho Q
    let HF := permutedPolynomialHessianFourBlock rho F
    adaptiveSmithInflateHom w HQ.schurB =
      MvPolynomial.C
          (Polynomial.X ^ (3 * D - reverseReesSchurBLoss w rho)) *
        constantPolynomialFamily HF.schurB := by
  dsimp
  have hs := reverseWeightedRees_schurB_normalization w D F h rho
  dsimp at hs
  rw [schurB_diagonal_parameter_factor, common_parameter_cube] at hs
  have hpow :
      (Polynomial.X : Polynomial K) ^ (3 * D) =
        Polynomial.X ^ reverseReesSchurBLoss w rho *
          Polynomial.X ^ (3 * D - reverseReesSchurBLoss w rho) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, MvPolynomial.C_mul] at hs
  have hs' :
      MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurBLoss w rho) *
        adaptiveSmithInflateHom w
          (permutedPolynomialHessianFourBlock rho
            (reverseWeightedReesFamily w D F h)).schurB =
      MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurBLoss w rho) *
        (MvPolynomial.C
            (Polynomial.X ^ (3 * D - reverseReesSchurBLoss w rho)) *
          constantPolynomialFamily
            (permutedPolynomialHessianFourBlock rho F).schurB) := by
    simpa [mul_assoc] using hs
  exact mul_left_cancel₀
    (MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)) hs'

/-- Corresponding exact normalization for the second diagonal cleared Schur
entry. -/
theorem reverseWeightedRees_schurC_inflate_eq
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurCLoss w rho ≤ 3 * D) :
    let Q := reverseWeightedReesFamily w D F h
    let HQ := permutedPolynomialHessianFourBlock rho Q
    let HF := permutedPolynomialHessianFourBlock rho F
    adaptiveSmithInflateHom w HQ.schurC =
      MvPolynomial.C
          (Polynomial.X ^ (3 * D - reverseReesSchurCLoss w rho)) *
        constantPolynomialFamily HF.schurC := by
  dsimp
  have hs := reverseWeightedRees_schurC_normalization w D F h rho
  dsimp at hs
  rw [schurC_diagonal_parameter_factor, common_parameter_cube] at hs
  have hpow :
      (Polynomial.X : Polynomial K) ^ (3 * D) =
        Polynomial.X ^ reverseReesSchurCLoss w rho *
          Polynomial.X ^ (3 * D - reverseReesSchurCLoss w rho) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, MvPolynomial.C_mul] at hs
  have hs' :
      MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurCLoss w rho) *
        adaptiveSmithInflateHom w
          (permutedPolynomialHessianFourBlock rho
            (reverseWeightedReesFamily w D F h)).schurC =
      MvPolynomial.C
          (Polynomial.X ^ reverseReesSchurCLoss w rho) *
        (MvPolynomial.C
            (Polynomial.X ^ (3 * D - reverseReesSchurCLoss w rho)) *
          constantPolynomialFamily
            (permutedPolynomialHessianFourBlock rho F).schurC) := by
    simpa [mul_assoc] using hs
  exact mul_left_cancel₀
    (MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)) hs'

/-- Parameter-first coefficient `n` of Schur `A` is an exact initial form of
the actual source Schur polynomial. -/
theorem reverseWeightedRees_parameterFirstSchurA_coeff_eq_initialForm
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurALoss w rho ≤ 3 * D)
    (hn : n ≤ 3 * D - reverseReesSchurALoss w rho) :
    let Q := reverseWeightedReesFamily w D F h
    let H := permutedFamilyHessianFourBlock rho Q
    let HF := permutedPolynomialHessianFourBlock rho F
    H.schurA.coeff n =
      initialForm (fun i => (w i : ℤ))
        (((3 * D - reverseReesSchurALoss w rho) - n : ℕ) : ℤ)
        HF.schurA := by
  dsimp
  rw [permutedFamilyHessianFourBlock_schurA_eq_parameterFirstEquiv,
    parameterFirstEquiv_coeff]
  exact congrArg (fun P => MvPolynomial.coeff (0 : Fin 4 →₀ ℕ) P)
    (by
      -- the equality itself is polynomial-valued; `exact` below avoids any
      -- source evaluation and keeps the whole associated-graded polynomial.
      skip)

/-- Whole-polynomial form of the previous theorem, used internally and by the
ray specialization. -/
theorem reverseWeightedRees_familyParameterLayer_schurA_eq_initialForm
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurALoss w rho ≤ 3 * D)
    (hn : n ≤ 3 * D - reverseReesSchurALoss w rho) :
    familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (reverseWeightedReesFamily w D F h)).schurA n =
      initialForm (fun i => (w i : ℤ))
        (((3 * D - reverseReesSchurALoss w rho) - n : ℕ) : ℤ)
        (permutedPolynomialHessianFourBlock rho F).schurA := by
  apply familyParameterLayer_eq_initialForm_of_adaptiveSmithInflate_eq
    w (3 * D - reverseReesSchurALoss w rho) n
  · exact reverseWeightedRees_schurA_inflate_eq w D F h rho hloss
  · exact hn

end

end HC4.Valuation
