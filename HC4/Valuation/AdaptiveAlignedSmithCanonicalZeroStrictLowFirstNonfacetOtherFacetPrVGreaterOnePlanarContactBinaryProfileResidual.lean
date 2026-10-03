import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactBinaryProfileHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessianFractionRecognition
import Mathlib.Tactic

/-!
# A19 planar-contact binary profile to the stationary residual

The singular planar carrier profile lives over the honest transverse
coefficient domain `MvPolynomial (Fin 3) K`.  The preceding module proves the
three exact weighted binary Hessian coefficient formulas with

    D = T.topFace.degree,    r = V + 2.

A19.R15 already owns the only localization needed by the stationary staircase
rigidity theorem.  This file therefore freezes the closing representation
adapter: once the integral two-by-two profile Hessian determinant is zero, its
fraction-field profile satisfies the exact stationary residual equation.

The remaining geometric obligation is deliberately visible in the single
hypothesis `hdet`; it must be discharged by the source-honest Schur/pivot
cancellation, not by an invalid inference from four-by-four singularity to an
arbitrary minor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- Once the honest integral binary profile determinant vanishes, the mapped
singular planar-carrier profile satisfies exactly the stationary staircase
residual consumed by the existing finite rigidity theorem. -/
theorem carrierProfile_fraction_staircaseResidual_eq_zero_of_hessianDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hdet : D.carrierProfileHessianDet = 0) :
    binaryStaircaseProfileResidual
        T.topFace.degree D.binaryProfileWeight
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin 3) K)
            (FractionRing (MvPolynomial (Fin 3) K)))
          D.carrierLongitudinalProfile) = 0 := by
  apply binaryStaircaseProfileResidual_fraction_eq_zero_of_coeffwise_hessian
    T.topFace.degree D.binaryProfileWeight
    D.carrierLongitudinalProfile
    D.carrierProfileHessian00
    D.carrierProfileHessian01
    D.carrierProfileHessian11
  · exact D.coeff_carrierProfileHessian00
  · exact D.coeff_carrierProfileHessian01
  · exact D.coeff_carrierProfileHessian11
  · simpa [carrierProfileHessianDet] using hdet

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
