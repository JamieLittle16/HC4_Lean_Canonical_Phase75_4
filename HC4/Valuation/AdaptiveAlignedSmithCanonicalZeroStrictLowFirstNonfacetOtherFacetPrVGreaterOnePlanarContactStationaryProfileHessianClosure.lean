import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryRigidity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneTwoFunctionReconstruction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessianFractionRecognition
import Mathlib.Tactic

/-!
# A19 stationary profile-Hessian closing seam

The remaining geometric Schur adapter naturally produces three polynomials over
the integral coefficient ring `Polynomial K`: the parameter/parameter, mixed,
and longitudinal/longitudinal entries of the stationary binary Hessian block.
The generic fraction-field recognition theorem already knows how to convert
their exact coefficient formulas and zero determinant into the stationary
staircase residual.

This file splices that algebraic output directly into the source-honest
stationary rigidity theorem and the already-verified two-function carrier
contradiction.  Consequently the live geometric target is now exactly one
coefficientwise Hessian block with zero determinant; no further degree,
localization, or carrier classification remains after it.
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

namespace QsOtherFacetPrLeftVContactFrontierData

/-- **Stationary profile-Hessian closure.**

If the source-honest geometric adapter supplies an integral symmetric binary
block whose coefficients are exactly the stationary staircase Hessian
coefficients and whose determinant vanishes, then the left `V > 1` planar
carrier is impossible.

This is the full algebraic tail of the branch: fraction-field recognition gives
the stationary residual, stationary rigidity removes strict interior support,
and the existing exact two-function reconstruction yields the contradiction. -/
theorem impossible_of_stationary_coeffwise_hessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (H00 H01 H11 : Polynomial (Polynomial K))
    (h00 : ∀ m : ℕ,
      H00.coeff m =
        (((F.stationaryTotalDegree : Polynomial K) -
            (F.stationaryWeight : Polynomial K) * (m : Polynomial K)) *
          ((F.stationaryTotalDegree : Polynomial K) -
            (F.stationaryWeight : Polynomial K) * (m : Polynomial K) - 1)) *
          F.stationaryCarrierProfile.coeff m)
    (h01 : ∀ m : ℕ,
      H01.coeff m =
        (m : Polynomial K) *
          ((F.stationaryTotalDegree : Polynomial K) -
            (F.stationaryWeight : Polynomial K) * (m : Polynomial K)) *
          F.stationaryCarrierProfile.coeff m)
    (h11 : ∀ m : ℕ,
      H11.coeff m =
        (m : Polynomial K) * ((m : Polynomial K) - 1) *
          F.stationaryCarrierProfile.coeff m)
    (hdet : H00 * H11 - H01 * H01 = 0) : False := by
  have hres :
      binaryStaircaseProfileResidual
        F.stationaryTotalDegree F.stationaryWeight
        (Polynomial.map
          (algebraMap (Polynomial K) (FractionRing (Polynomial K)))
          F.stationaryCarrierProfile) = 0 :=
    binaryStaircaseProfileResidual_fraction_eq_zero_of_coeffwise_hessian
      F.stationaryTotalDegree F.stationaryWeight
      F.stationaryCarrierProfile H00 H01 H11
      h00 h01 h11 hdet
  have hres' :
      binaryStaircaseProfileResidual
        F.stationaryTotalDegree F.stationaryWeight
        F.stationaryCarrierProfileFraction = 0 := by
    simpa [stationaryCarrierProfileFraction] using hres
  have hno : F.NoStrictInteriorSupport :=
    F.noStrictInteriorSupport_of_stationaryResidual
      hthree houtThree hres'
  exact F.impossible_of_noStrictInterior hno

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
