import HC4.Valuation.ReverseReesSchurAssociatedGraded
import Mathlib.Tactic

/-!
# Range bounds from exact adaptive source normalisation

If source inflation sends a polynomial family exactly to one parameter monomial
times a constant source polynomial,

    inflate_w(P) = X^E * G,

then no parameter layer of P can occur above E.  This is the out-of-range
companion to `familyParameterLayer_eq_initialForm_of_adaptiveSmithInflate_eq`.

Applied to the three cleared Schur polynomials of a bounded reverse-Rees
family, it shows that their parameter-first coefficients vanish above their
exact cubic source ranges.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open HC4.Newton

variable {K : Type*} [Field K]

/-- Exact adaptive normalisation forces every parameter layer above the
normalising exponent to vanish. -/
theorem familyParameterLayer_eq_zero_of_adaptiveSmithInflate_eq_of_level_lt
    (w : Fin 4 → ℕ) (E n : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (G : MvPolynomial (Fin 4) K)
    (hEq : adaptiveSmithInflateHom w P =
      MvPolynomial.C (Polynomial.X ^ E) * constantPolynomialFamily G)
    (hEn : E < n) :
    familyParameterLayer P n = 0 := by
  ext d
  rw [familyParameterLayer_coeff, MvPolynomial.coeff_zero]
  have heq := congrArg (MvPolynomial.coeff d) hEq
  rw [coeff_adaptiveSmithInflateHom,
    MvPolynomial.coeff_C_mul, coeff_constantPolynomialFamily] at heq
  have hcoeff := congrArg
    (fun c : Polynomial K => c.coeff (Finsupp.weight w d + n)) heq
  change
    (Polynomial.X ^ Finsupp.weight w d * MvPolynomial.coeff d P).coeff
        (Finsupp.weight w d + n) =
      (Polynomial.X ^ E * Polynomial.C (MvPolynomial.coeff d G)).coeff
        (Finsupp.weight w d + n) at hcoeff
  have hleft :
      (Polynomial.X ^ Finsupp.weight w d * MvPolynomial.coeff d P).coeff
          (Finsupp.weight w d + n) =
        (MvPolynomial.coeff d P).coeff n := by
    rw [Polynomial.coeff_X_pow_mul']
    simp
  have hright :
      (Polynomial.X ^ E * Polynomial.C (MvPolynomial.coeff d G)).coeff
          (Finsupp.weight w d + n) = 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    have hle : E ≤ Finsupp.weight w d + n := by omega
    simp only [if_pos hle]
    rw [Polynomial.coeff_C]
    have hpos : 0 < Finsupp.weight w d + n - E := by omega
    simp [Nat.ne_of_gt hpos]
  rw [hleft, hright] at hcoeff
  exact hcoeff

/-- Schur A has no parameter-first coefficients above its exact source
normalisation range. -/
theorem reverseWeightedRees_parameterFirstSchurA_coeff_eq_zero_of_range_lt
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurALoss w rho ≤ 3 * D)
    (hrange : 3 * D - reverseReesSchurALoss w rho < n) :
    let Q := reverseWeightedReesFamily w D F h
    let H := permutedFamilyHessianFourBlock rho Q
    H.schurA.coeff n = 0 := by
  dsimp
  rw [permutedFamilyHessianFourBlock_schurA_eq_parameterFirstEquiv,
    parameterFirstEquiv_coeff]
  have hzero :
      familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (reverseWeightedReesFamily w D F h)).schurA n = 0 := by
    apply familyParameterLayer_eq_zero_of_adaptiveSmithInflate_eq_of_level_lt
      w (3 * D - reverseReesSchurALoss w rho) n
      (permutedPolynomialHessianFourBlock rho
        (reverseWeightedReesFamily w D F h)).schurA
      (permutedPolynomialHessianFourBlock rho F).schurA
    · exact reverseWeightedRees_schurA_inflate_eq w D F h rho hloss
    · exact hrange
  rw [hzero]
  simp

/-- Schur B range-zero theorem. -/
theorem reverseWeightedRees_parameterFirstSchurB_coeff_eq_zero_of_range_lt
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurBLoss w rho ≤ 3 * D)
    (hrange : 3 * D - reverseReesSchurBLoss w rho < n) :
    let Q := reverseWeightedReesFamily w D F h
    let H := permutedFamilyHessianFourBlock rho Q
    H.schurB.coeff n = 0 := by
  dsimp
  rw [permutedFamilyHessianFourBlock_schurB_eq_parameterFirstEquiv,
    parameterFirstEquiv_coeff]
  have hzero :
      familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (reverseWeightedReesFamily w D F h)).schurB n = 0 := by
    apply familyParameterLayer_eq_zero_of_adaptiveSmithInflate_eq_of_level_lt
      w (3 * D - reverseReesSchurBLoss w rho) n
      (permutedPolynomialHessianFourBlock rho
        (reverseWeightedReesFamily w D F h)).schurB
      (permutedPolynomialHessianFourBlock rho F).schurB
    · exact reverseWeightedRees_schurB_inflate_eq w D F h rho hloss
    · exact hrange
  rw [hzero]
  simp

/-- Schur C range-zero theorem. -/
theorem reverseWeightedRees_parameterFirstSchurC_coeff_eq_zero_of_range_lt
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurCLoss w rho ≤ 3 * D)
    (hrange : 3 * D - reverseReesSchurCLoss w rho < n) :
    let Q := reverseWeightedReesFamily w D F h
    let H := permutedFamilyHessianFourBlock rho Q
    H.schurC.coeff n = 0 := by
  dsimp
  rw [permutedFamilyHessianFourBlock_schurC_eq_parameterFirstEquiv,
    parameterFirstEquiv_coeff]
  have hzero :
      familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (reverseWeightedReesFamily w D F h)).schurC n = 0 := by
    apply familyParameterLayer_eq_zero_of_adaptiveSmithInflate_eq_of_level_lt
      w (3 * D - reverseReesSchurCLoss w rho) n
      (permutedPolynomialHessianFourBlock rho
        (reverseWeightedReesFamily w D F h)).schurC
      (permutedPolynomialHessianFourBlock rho F).schurC
    · exact reverseWeightedRees_schurC_inflate_eq w D F h rho hloss
    · exact hrange
  rw [hzero]
  simp

end

end HC4.Valuation
