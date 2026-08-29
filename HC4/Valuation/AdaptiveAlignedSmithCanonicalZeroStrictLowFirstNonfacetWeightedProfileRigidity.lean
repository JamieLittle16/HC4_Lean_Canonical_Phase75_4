import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetWeightedContactSingularity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# A19.100a: source-native weighted staircase contradiction interface

The surviving lower `qs` other-facet branch already carries an integral contact
slope `delta >= 2` on the actual represented special fibre.  Because the
contact weight is

    ordinaryDegree4 d + delta * d[0],

the literal weight of coordinate `0` is `delta + 1`.  This is exactly the
positive-gap convention used by the state-free binary staircase profile
rigidity theorem.

This file freezes the final algebraic contract without importing any planar
terminal provenance.  A certificate retains the actual integral source bound,
the actual singular weighted contact initial form, and a one-variable profile
of that source satisfying the stationary Euler residual.  Once such a profile
has a genuine layer of index at least two, the existing finite-profile theorem
is contradictory.

The next source adapter therefore has one precise job: construct this
certificate from the represented four-dimensional first-contact source and the
strict transverse direction lock.  No JC2 hypothesis, planar collision, new
carrier, or progress measure is introduced here.
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

/-- Source-native contract for the final weighted staircase contradiction.

`gap` is the integral *extra* weight from A19.97.  Hence the actual transverse
profile weight is `gap + 1`, matching
`binaryStaircaseProfile_natDegree_le_one_of_positiveGap` exactly. -/
structure QsOtherFacetWeightedProfileCertificate
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) : Type u where
  gap : ℕ
  gap_two_le : 2 ≤ gap
  bump_eq : C.bump = C.scale * gap
  source_weight_le :
    ∀ {d : Fin 4 →₀ ℕ},
      d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support →
      HC4.Polynomial.ordinaryDegree4 d + gap * d (0 : Fin 4) ≤
        T.topFace.degree
  weighted_contact_hessian_zero :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm
        (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 gap)
        (T.topFace.degree : ℤ)
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)) = 0
  profile : Polynomial K
  profile_coeff_zero_ne : profile.coeff 0 ≠ 0
  profile_support : profile.natDegree * (gap + 1) ≤ T.topFace.degree
  profile_residual :
    binaryStaircaseProfileResidual T.topFace.degree (gap + 1) profile = 0
  profile_degree_two_le : 2 ≤ profile.natDegree

/-- **State-free terminal contradiction once the honest weighted profile has
been extracted.**  All four-dimensional provenance is retained in the
certificate, but the contradiction itself is exactly the already-green finite
profile rigidity theorem. -/
theorem QsOtherFacetWeightedProfileCertificate.impossible
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetWeightedProfileCertificate C) : False := by
  have hle : P.profile.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one_of_positiveGap
      (K := K)
      T.topFace.degree P.gap (by omega) P.profile
      P.profile_coeff_zero_ne P.profile_support P.profile_residual
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
