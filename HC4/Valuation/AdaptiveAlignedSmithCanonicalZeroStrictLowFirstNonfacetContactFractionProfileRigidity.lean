import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFractionProfile
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# A19.119: the contact fraction profile is contradictory once its residual vanishes

A19.114 constructs the exact symbolic longitudinal profile of the represented
source, and A19.115 injects it into the fraction field of the transverse
coefficient domain without losing its constant coefficient or degree.

At that point every input of the already-green finite staircase rigidity
theorem is present except one equation:

    binaryStaircaseProfileResidual D profileWeight profile = 0.

This file freezes that final interface.  The forthcoming four-block Schur
adapter therefore has exactly one mathematical obligation: produce the
residual equation for this canonical contact profile.  No transverse
evaluation, planar JC2 hypothesis, or additional terminal geometry occurs
here.
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

/-- The A19.115 fraction-field profile is impossible as soon as the honest
contact/Schur calculation supplies the stationary residual equation. -/
theorem QsOtherFacetContactFractionProfilePackage.impossible_of_residual
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (H : QsOtherFacetContactFractionProfilePackage C P)
    (hres :
      binaryStaircaseProfileResidual
        T.topFace.degree P.profileWeight H.profile = 0) : False := by
  have hle : H.profile.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one
      (K := qsContactProfileField K)
      T.topFace.degree P.profileWeight P.profileWeight_two_le H.profile
      H.coeff_zero_ne H.support_bound hres
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
