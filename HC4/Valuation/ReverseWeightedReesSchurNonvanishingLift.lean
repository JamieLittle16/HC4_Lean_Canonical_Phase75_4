import HC4.Valuation.ReverseReesSchurAssociatedGraded
import Mathlib.Tactic

/-!
# Whole-family reverse-Rees lift for cleared Schur polynomials

The associated-graded Schur normalization theorems give exact diagonal
inflation identities for the three denominator-cleared 2+2 Schur entries of
a bounded reverse-Rees family.

Because adaptive diagonal inflation is injective and all parameter monomials
appearing in the normalization are nonzero, nonvanishing of a whole-family
Schur entry lifts back to nonvanishing of the corresponding Schur polynomial
of the represented source.

This is the Schur analogue of
`reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K]

/-- Whole-family Schur A nonvanishing lifts to the represented source. -/
theorem reverseWeightedReesFamily_sourceSchurA_of_familySchurA_ne_zero
    (w : Fin 4 → ℕ)
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound w D F)
    (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurALoss w rho ≤ 3 * D)
    (hne :
      (permutedFamilyHessianFourBlock rho
        (reverseWeightedReesFamily w D F hbound)).schurA ≠ 0) :
    (permutedPolynomialHessianFourBlock rho F).schurA ≠ 0 := by
  intro hsource
  have hnorm :=
    reverseWeightedRees_schurA_inflate_eq
      w D F hbound rho hloss
  dsimp at hnorm
  rw [hsource] at hnorm
  simp [constantPolynomialFamily] at hnorm
  have hinflated :
      adaptiveSmithInflateHom w
        (permutedFamilyHessianFourBlock rho
          (reverseWeightedReesFamily w D F hbound)).schurA = 0 := by
    exact hnorm
  have hzero :
      (permutedFamilyHessianFourBlock rho
        (reverseWeightedReesFamily w D F hbound)).schurA = 0 := by
    apply adaptiveSmithInflateHom_injective (K := K) w
    simpa using hinflated
  exact hne hzero

/-- Whole-family off-diagonal Schur B nonvanishing lifts to the represented
source. -/
theorem reverseWeightedReesFamily_sourceSchurB_of_familySchurB_ne_zero
    (w : Fin 4 → ℕ)
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound w D F)
    (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurBLoss w rho ≤ 3 * D)
    (hne :
      (permutedFamilyHessianFourBlock rho
        (reverseWeightedReesFamily w D F hbound)).schurB ≠ 0) :
    (permutedPolynomialHessianFourBlock rho F).schurB ≠ 0 := by
  intro hsource
  have hnorm :=
    reverseWeightedRees_schurB_inflate_eq
      w D F hbound rho hloss
  dsimp at hnorm
  rw [hsource] at hnorm
  simp [constantPolynomialFamily] at hnorm
  have hinflated :
      adaptiveSmithInflateHom w
        (permutedFamilyHessianFourBlock rho
          (reverseWeightedReesFamily w D F hbound)).schurB = 0 := by
    exact hnorm
  have hzero :
      (permutedFamilyHessianFourBlock rho
        (reverseWeightedReesFamily w D F hbound)).schurB = 0 := by
    apply adaptiveSmithInflateHom_injective (K := K) w
    simpa using hinflated
  exact hne hzero

/-- Whole-family Schur C nonvanishing lifts to the represented source. -/
theorem reverseWeightedReesFamily_sourceSchurC_of_familySchurC_ne_zero
    (w : Fin 4 → ℕ)
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound w D F)
    (rho : Equiv.Perm (Fin 4))
    (hloss : reverseReesSchurCLoss w rho ≤ 3 * D)
    (hne :
      (permutedFamilyHessianFourBlock rho
        (reverseWeightedReesFamily w D F hbound)).schurC ≠ 0) :
    (permutedPolynomialHessianFourBlock rho F).schurC ≠ 0 := by
  intro hsource
  have hnorm :=
    reverseWeightedRees_schurC_inflate_eq
      w D F hbound rho hloss
  dsimp at hnorm
  rw [hsource] at hnorm
  simp [constantPolynomialFamily] at hnorm
  have hinflated :
      adaptiveSmithInflateHom w
        (permutedFamilyHessianFourBlock rho
          (reverseWeightedReesFamily w D F hbound)).schurC = 0 := by
    exact hnorm
  have hzero :
      (permutedFamilyHessianFourBlock rho
        (reverseWeightedReesFamily w D F hbound)).schurC = 0 := by
    apply adaptiveSmithInflateHom_injective (K := K) w
    simpa using hinflated
  exact hne hzero

end

end HC4.Valuation
