import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactBinaryParameterChainRule
import Mathlib.Tactic

/-!
# A19 Euler reduction of the singular planar binary profile determinant

This is the planar-contact analogue of the existing generic R18 Euler
reduction.  The whole-family identities proved for the singular planar binary
homogenization eliminate the auxiliary parameter-Hessian entries from
`binaryProfileHessianDetFamily` without any division or support assumption.

The resulting source-facing formula uses only the binary family, its
longitudinal Euler derivative, and its longitudinal falling Hessian.  It is the
form to be matched against the source-honest `(2,3)` Schur block.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The binary profile determinant after eliminating the parameter-parameter
entry by the falling weighted-Euler rows. -/
theorem binaryProfileHessianDetFamily_eq_euler_reduction
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    D.binaryProfileHessianDetFamily =
      MvPolynomial.C
          (Polynomial.C ((T.topFace.degree : K) - 1)) *
        familyParameterEuler D.binaryHomogenizedFamily *
          D.binaryProfileHessian11Family -
      MvPolynomial.C
          (Polynomial.C
            ((T.topFace.degree : K) - (D.binaryProfileWeight : K))) *
        HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily *
          D.binaryProfileHessian01Family := by
  have hParameter := D.binaryHomogenized_fallingParameterRow
  have hLongitudinal := D.binaryHomogenized_fallingLongitudinalRow
  unfold QsOtherFacetPrLeftVPlanarContactReesData.binaryProfileHessianDetFamily
    QsOtherFacetPrLeftVPlanarContactReesData.binaryProfileHessian00Family
    QsOtherFacetPrLeftVPlanarContactReesData.binaryProfileHessian01Family
    QsOtherFacetPrLeftVPlanarContactReesData.binaryProfileHessian11Family
  linear_combination
    hParameter *
      (HC4.Polynomial.eulerScaledHessian
        D.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)) -
    hLongitudinal *
      (familyParameterEuler
        (HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily))

/-- Source-facing normal form of the singular planar binary profile determinant.
Only the binary family itself, its longitudinal Euler row, and its
longitudinal falling Hessian remain. -/
theorem binaryProfileHessianDetFamily_eq_longitudinal_reduction
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    D.binaryProfileHessianDetFamily =
      MvPolynomial.C
          (Polynomial.C
            ((T.topFace.degree : K) * ((T.topFace.degree : K) - 1))) *
        D.binaryHomogenizedFamily * D.binaryProfileHessian11Family +
      MvPolynomial.C
          (Polynomial.C
            ((D.binaryProfileWeight : K) *
              (1 - (D.binaryProfileWeight : K)))) *
        HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily *
          D.binaryProfileHessian11Family -
      MvPolynomial.C
          (Polynomial.C
            (((T.topFace.degree : K) - (D.binaryProfileWeight : K)) ^ 2)) *
        HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily *
          HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily := by
  rw [D.binaryProfileHessianDetFamily_eq_euler_reduction]
  have hWeighted := D.binaryHomogenized_weightedEuler
  have hLongitudinal := D.binaryHomogenized_fallingLongitudinalRow
  unfold QsOtherFacetPrLeftVPlanarContactReesData.binaryProfileHessian01Family
    QsOtherFacetPrLeftVPlanarContactReesData.binaryProfileHessian11Family
  simp only [map_sub, map_mul, map_pow, map_one] at hWeighted hLongitudinal ⊢
  linear_combination
    (MvPolynomial.C (Polynomial.C (T.topFace.degree : K)) - 1) *
      hWeighted *
        (HC4.Polynomial.eulerScaledHessian
          D.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)) -
    (MvPolynomial.C (Polynomial.C (T.topFace.degree : K)) -
        MvPolynomial.C (Polynomial.C (D.binaryProfileWeight : K))) *
      hLongitudinal *
        (HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily)

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
