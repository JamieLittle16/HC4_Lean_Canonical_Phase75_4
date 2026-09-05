import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurInflation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryDeterminantCancellation
import Mathlib.Tactic

/-!
# A19.R18: normalized binary Schur inflation layers

The binary contact Hessian carries explicit transverse-inflation powers:
`tau^4`, `tau^5`, `tau^6`, and `tau^10` on the three cleared Schur entries and
their determinant.  The covariance identities are already owned by
`ContactBinarySchurInflation`; this module removes those explicit powers at the
exact parameter-layer level using the single layer-shift lemma owned by
`ContactBinaryDeterminantCancellation`.

These are normalization lemmas only.  They introduce no new geometry, no
homogeneity assumption, and no cancellation by an active pivot.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Strip the exact `tau^4` factor from the first cleared Schur entry. -/
theorem familyParameterLayer_permutedPolynomialHessianFourBlock_schurA_unitTransverseInflateFamily_add_four
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0)
    (n : ℕ) :
    familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (unitTransverseInflateFamily (K := K) P)).schurA
        (n + 4) =
      familyParameterLayer
        (unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurA) n := by
  rw [permutedPolynomialHessianFourBlock_schurA_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  exact familyParameterLayer_C_X_pow_mul_add
    (unitTransverseInflateFamily (K := K)
      (permutedPolynomialHessianFourBlock rho P).schurA) 4 n

/-- Strip the exact `tau^5` factor from the mixed cleared Schur entry. -/
theorem familyParameterLayer_permutedPolynomialHessianFourBlock_schurB_unitTransverseInflateFamily_add_five
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0)
    (n : ℕ) :
    familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (unitTransverseInflateFamily (K := K) P)).schurB
        (n + 5) =
      familyParameterLayer
        (unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurB) n := by
  rw [permutedPolynomialHessianFourBlock_schurB_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  exact familyParameterLayer_C_X_pow_mul_add
    (unitTransverseInflateFamily (K := K)
      (permutedPolynomialHessianFourBlock rho P).schurB) 5 n

/-- Strip the exact `tau^6` factor from the second cleared Schur entry. -/
theorem familyParameterLayer_permutedPolynomialHessianFourBlock_schurC_unitTransverseInflateFamily_add_six
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0)
    (n : ℕ) :
    familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (unitTransverseInflateFamily (K := K) P)).schurC
        (n + 6) =
      familyParameterLayer
        (unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurC) n := by
  rw [permutedPolynomialHessianFourBlock_schurC_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  exact familyParameterLayer_C_X_pow_mul_add
    (unitTransverseInflateFamily (K := K)
      (permutedPolynomialHessianFourBlock rho P).schurC) 6 n

/-- Strip the exact `tau^10` factor from the cleared Schur determinant. -/
theorem familyParameterLayer_permutedPolynomialHessianFourBlock_schurDetCore_unitTransverseInflateFamily_add_ten
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0)
    (n : ℕ) :
    familyParameterLayer
        (permutedPolynomialHessianFourBlock rho
          (unitTransverseInflateFamily (K := K) P)).schurDetCore
        (n + 10) =
      familyParameterLayer
        (unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurDetCore) n := by
  rw [permutedPolynomialHessianFourBlock_schurDetCore_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  exact familyParameterLayer_C_X_pow_mul_add
    (unitTransverseInflateFamily (K := K)
      (permutedPolynomialHessianFourBlock rho P).schurDetCore) 10 n

end

end HC4.Valuation
