import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrLockedSourceCoefficients
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedCarrier
import Mathlib.Tactic

/-!
# A19 source-honest unit PR endpoint orientations

The normalized unit quotient branch has direction `(1,-1,-1,-1)`.  The
primitive highest slice and the locked source ray already carry independent
left/right source-honest normal forms.  This file does only the bookkeeping
needed to synchronize their internal quotient parameter with the unit quotient
and retain the four possible relative orientations.

No determinant identity, contact clock identification, or new source
classification is introduced here.
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

/-- The four source-honest relative endpoint orientations in the unit quotient
branch.  `sameLeft`/`sameRight` are the two-function orientations; the two
`mixed` constructors are the scalar extremal-coefficient orientations. -/
inductive QsOtherFacetPrUnitEndpointOrientationData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C) : Type (u + 1)
  | sameLeft
      (highest : QsOtherFacetPrHighestSliceLeftSourceData C P S R)
      (locked : QsOtherFacetPrLockedLeftSourceData C P R)
      (highest_V_eq_one : highest.V = 1)
      (locked_V_eq_one : locked.V = 1)
  | sameRight
      (highest : QsOtherFacetPrHighestSliceRightSourceData C P S R)
      (locked : QsOtherFacetPrLockedRightSourceData C P R)
      (highest_V_eq_one : highest.V = 1)
      (locked_V_eq_one : locked.V = 1)
  | mixedLeftRight
      (highest : QsOtherFacetPrHighestSliceLeftSourceData C P S R)
      (locked : QsOtherFacetPrLockedRightSourceData C P R)
      (highest_V_eq_one : highest.V = 1)
      (locked_V_eq_one : locked.V = 1)
  | mixedRightLeft
      (highest : QsOtherFacetPrHighestSliceRightSourceData C P S R)
      (locked : QsOtherFacetPrLockedLeftSourceData C P R)
      (highest_V_eq_one : highest.V = 1)
      (locked_V_eq_one : locked.V = 1)

namespace QsOtherFacetPrUnitEndpointOrientationData

private theorem highestLeft_V_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (H : QsOtherFacetPrHighestSliceLeftSourceData C P S R)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 1) :
    H.V = 1 := by
  have hpair :
      qsOtherFacetPairDegree .pr H.e0 = qsOtherFacetPairDegree .pr H.e1 := by
    simp [qsOtherFacetPairDegree, H.e0_zero, H.e0_one,
      H.e1_zero, H.e1_one]
    omega
  have hq := Q.pair_fiber
    H.e0_provenance.carrier_mem H.e1_provenance.carrier_mem hpair
  have hs := congrArg
    HC4.Polynomial.RankThreeQuotientCoordinate.secondTransverse hq
  simp [HC4.Polynomial.rankThreeQuotientCoordinate,
    H.e0_zero, H.e0_three, H.e1_zero, H.e1_three] at hs
  have hn : H.n = (H.n - 1) + 1 := by omega
  rw [hn, Nat.mul_add] at hs
  omega

private theorem highestRight_V_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (H : QsOtherFacetPrHighestSliceRightSourceData C P S R)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 1) :
    H.V = 1 := by
  have hpair :
      qsOtherFacetPairDegree .pr H.e0 = qsOtherFacetPairDegree .pr H.e1 := by
    simp [qsOtherFacetPairDegree, H.e0_zero, H.e0_one,
      H.e1_zero, H.e1_one]
    omega
  have hq := Q.pair_fiber
    H.e0_provenance.carrier_mem H.e1_provenance.carrier_mem hpair
  have hr := congrArg
    HC4.Polynomial.RankThreeQuotientCoordinate.firstTransverse hq
  simp [HC4.Polynomial.rankThreeQuotientCoordinate,
    H.e0_zero, H.e0_two, H.e1_zero, H.e1_two] at hr
  have hn : H.n = (H.n - 1) + 1 := by omega
  rw [hn, Nat.mul_add] at hr
  omega

private theorem lockedLeft_V_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (L : QsOtherFacetPrLockedLeftSourceData C P R)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 1) :
    L.V = 1 := by
  have h := Q.direction_three
  rw [L.outside_three, L.facet_three] at h
  push_cast at h
  have hVz : (L.V : ℤ) = 1 := by nlinarith
  exact_mod_cast hVz

private theorem lockedRight_V_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (L : QsOtherFacetPrLockedRightSourceData C P R)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 1) :
    L.V = 1 := by
  have h := Q.direction_two
  rw [L.outside_two, L.facet_two] at h
  push_cast at h
  have hVz : (L.V : ℤ) = 1 := by nlinarith
  exact_mod_cast hVz

end QsOtherFacetPrUnitEndpointOrientationData

/-- **Unit endpoint orientation frontier.**  In a normalized `(1,1)` quotient
carrier, the already-existing source-honest highest and locked endpoint
packages synchronize to `V=1`, leaving exactly the two same and two mixed
relative orientations. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_unitEndpointOrientation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 1)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrUnitEndpointOrientationData C P S R) := by
  rcases S.pr_highest_slice_source_data_of_nontrivial
      R hthree houtThree hnontrivial with hHL | hHR
  · rcases hHL with ⟨H⟩
    have hHV := QsOtherFacetPrUnitEndpointOrientationData.highestLeft_V_eq_one H Q
    rcases S.pr_locked_source_data_of_nontrivial
        R hthree houtThree hnontrivial with hLL | hLR
    · rcases hLL with ⟨L⟩
      have hLV := QsOtherFacetPrUnitEndpointOrientationData.lockedLeft_V_eq_one L Q
      exact ⟨.sameLeft H L hHV hLV⟩
    · rcases hLR with ⟨L⟩
      have hLV := QsOtherFacetPrUnitEndpointOrientationData.lockedRight_V_eq_one L Q
      exact ⟨.mixedLeftRight H L hHV hLV⟩
  · rcases hHR with ⟨H⟩
    have hHV := QsOtherFacetPrUnitEndpointOrientationData.highestRight_V_eq_one H Q
    rcases S.pr_locked_source_data_of_nontrivial
        R hthree houtThree hnontrivial with hLL | hLR
    · rcases hLL with ⟨L⟩
      have hLV := QsOtherFacetPrUnitEndpointOrientationData.lockedLeft_V_eq_one L Q
      exact ⟨.mixedRightLeft H L hHV hLV⟩
    · rcases hLR with ⟨L⟩
      have hLV := QsOtherFacetPrUnitEndpointOrientationData.lockedRight_V_eq_one L Q
      exact ⟨.sameRight H L hHV hLV⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation