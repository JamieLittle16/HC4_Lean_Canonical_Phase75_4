import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetWeightedContactSingularity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# A19.100a: source-native weighted staircase contradiction interface

The surviving lower `qs` other-facet branch already carries an integral contact
gap on the actual represented special fibre.  The existing finite staircase
rigidity theorem is state-free, but its binary profile weight is produced only
after straightening the locked transverse ray.  We therefore keep these two
integer parameters separate until that straightening has been proved.

This file freezes the final algebraic contract without importing any planar
terminal provenance.  A certificate retains the actual integral source bound,
the actual singular weighted contact initial form, and a one-variable profile
of that source satisfying the stationary Euler residual.  Once such a profile
has a genuine layer of index at least two, the existing finite-profile theorem
is contradictory.

The next source adapter therefore has one precise job: construct this
certificate from the represented four-dimensional first-contact source and the
strict transverse direction lock, including the correct binary profile weight.
No JC2 hypothesis, planar collision, new carrier, or progress measure is
introduced here.
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

`contactGap` is the integral extra source weight from A19.97.  `profileWeight`
is deliberately separate: it is the integer weight of the binary coordinate
obtained only after straightening one of the three locked cyclic transverse
rays. -/
structure QsOtherFacetWeightedProfileCertificate
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) : Type u where
  contactGap : ℕ
  contactGap_two_le : 2 ≤ contactGap
  bump_eq : C.bump = C.scale * contactGap
  source_weight_le :
    ∀ {d : Fin 4 →₀ ℕ},
      d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support →
      HC4.Polynomial.ordinaryDegree4 d + contactGap * d (0 : Fin 4) ≤
        T.topFace.degree
  weighted_contact_hessian_zero :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm
        (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 contactGap)
        (T.topFace.degree : ℤ)
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)) = 0
  profileWeight : ℕ
  profileWeight_two_le : 2 ≤ profileWeight
  profile : Polynomial K
  profile_coeff_zero_ne : profile.coeff 0 ≠ 0
  profile_support : profile.natDegree * profileWeight ≤ T.topFace.degree
  profile_residual :
    binaryStaircaseProfileResidual T.topFace.degree profileWeight profile = 0
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
    binaryStaircaseProfile_natDegree_le_one
      (K := K)
      T.topFace.degree P.profileWeight P.profileWeight_two_le P.profile
      P.profile_coeff_zero_ne P.profile_support P.profile_residual
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
