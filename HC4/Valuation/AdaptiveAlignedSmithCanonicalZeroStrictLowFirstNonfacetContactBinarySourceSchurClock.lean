import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryActiveSchur
import HC4.Valuation.PermutedPolynomialHessianFourBlock
import HC4.Valuation.ParameterFirstLayerBridge
import Mathlib.Tactic

/-!
# A19.R20: source-first form of the binary Hessian and Schur clocks

A19.128--A19.136 prove the exact binary Hessian clock after the canonical
parameter-first equivalence.  The remaining Euler/straightening calculation,
however, is most naturally carried out on the honest source-first polynomial
family

    MvPolynomial (Fin 4) (Polynomial K).

R20 transports those coefficient vanishings back across `parameterFirstEquiv`.
Besides the already-used cleared Schur clock, R18 needs the full determinant
one level above it.  The original strict quadratic margin is enough both for
the active-pivot shift by four and, more importantly for exact inflation
cancellation, for the full transverse-inflation shift by six.

This is purely representation plumbing: no new geometry, homogeneity
assumption, division, or determinant argument is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Source-first full Hessian determinant layers vanish strictly before the
exact binary Hessian clock. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_eq_zero_of_lt
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    {n : ℕ}
    (hn : n < (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6) :
    familyParameterLayer
        ((permutedPolynomialHessianFourBlock
          rho P.binaryHomogenizedFamily).determinantCore)
        n = 0 := by
  have h :
      ((permutedFamilyHessianFourBlock
        rho P.binaryHomogenizedFamily).determinantCore).coeff n = 0 := by
    rw [permutedFamilyHessianFourBlock_determinantCore_eq_X_pow
      rho P.binaryHomogenizedFamily P.binaryHomogenized_hessianDefect]
    simp [Polynomial.coeff_X_pow, Nat.ne_of_lt hn]
  rw [permutedFamilyHessianFourBlock_determinantCore_eq_parameterFirstEquiv]
    at h
  rw [parameterFirstEquiv_coeff] at h
  exact h

/-- The order carrying a quadratic profile coefficient after one binary active
pivot is still strictly before the full binary Hessian clock. -/
theorem QsOtherFacetContactQuadraticReesPackage.binary_profileOrder_add_four_lt_hessianClock
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (n : ℕ) :
    (2 * T.topFace.degree - P.profileWeight * n) + 4 <
      (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6 := by
  have hmargin := P.two_level_lt_defect
  have hsub :
      2 * T.topFace.degree - P.profileWeight * n ≤
        2 * T.topFace.degree := Nat.sub_le _ _
  omega

/-- The exact six powers of `tau` contributed by simultaneous transverse
inflation also fit strictly below the binary Hessian clock.  This is the
shift used when cancelling the full determinant inflation formula. -/
theorem QsOtherFacetContactQuadraticReesPackage.binary_profileOrder_add_six_lt_hessianClock
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (n : ℕ) :
    (2 * T.topFace.degree - P.profileWeight * n) + 6 <
      (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6 := by
  have hmargin := P.two_level_lt_defect
  have hsub :
      2 * T.topFace.degree - P.profileWeight * n ≤
        2 * T.topFace.degree := Nat.sub_le _ _
  omega

/-- Hence every shifted profile order needed for the one-pivot determinant
cancellation is a zero source-first full-determinant layer. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_profileOrder_add_four_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        ((permutedPolynomialHessianFourBlock
          rho P.binaryHomogenizedFamily).determinantCore)
        ((2 * T.topFace.degree - P.profileWeight * n) + 4) = 0 := by
  exact P.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_eq_zero_of_lt
    rho (P.binary_profileOrder_add_four_lt_hessianClock n)

/-- **R18 exact inflation-matched determinant clock.**  The full determinant
of the binary family vanishes at the profile order shifted by the six powers
of `tau` appearing in transverse-inflation covariance. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_profileOrder_add_six_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        ((permutedPolynomialHessianFourBlock
          rho P.binaryHomogenizedFamily).determinantCore)
        ((2 * T.topFace.degree - P.profileWeight * n) + 6) = 0 := by
  exact P.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_eq_zero_of_lt
    rho (P.binary_profileOrder_add_six_lt_hessianClock n)

/-- **R20 source-first Schur clock.**  At every parameter order which can
carry the degree-`n` binary staircase residual coefficient, the source-first
cleared Schur determinant has zero parameter layer. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_permutedSourceSchurDetCore_parameterLayer_profileOrder_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (Q : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        ((permutedPolynomialHessianFourBlock
          rho P.binaryHomogenizedFamily).schurDetCore)
        (2 * T.topFace.degree - P.profileWeight * n) = 0 := by
  have h :=
    P.binaryHomogenized_permutedSchurDetCore_coeff_profileOrder_eq_zero
      Q rho n
  rw [permutedFamilyHessianFourBlock_schurDetCore_eq_parameterFirstEquiv]
    at h
  rw [parameterFirstEquiv_coeff] at h
  exact h

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
