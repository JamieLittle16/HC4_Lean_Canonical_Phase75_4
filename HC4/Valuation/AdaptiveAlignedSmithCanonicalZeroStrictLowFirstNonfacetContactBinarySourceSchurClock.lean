import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryActiveSchur
import HC4.Valuation.PermutedPolynomialHessianFourBlock
import HC4.Valuation.ParameterFirstLayerBridge
import Mathlib.Tactic

/-!
# A19.R20: source-first form of the binary Schur clock

A19.128--A19.136 prove the exact binary Schur clock after the canonical
parameter-first equivalence.  The remaining Euler/straightening calculation,
however, is most naturally carried out on the honest source-first polynomial
family

    MvPolynomial (Fin 4) (Polynomial K).

R20 transports the already-proved coefficient vanishing back across
`parameterFirstEquiv`.  Thus every binary profile order is a zero parameter
layer of the ordinary source-first cleared Schur determinant.  This is purely
representation plumbing: no new geometry, homogeneity assumption, division,
or determinant argument is introduced.
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
