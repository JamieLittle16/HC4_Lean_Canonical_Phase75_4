import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneContactOrders
import Mathlib.Tactic

/-!
# A19 source-honest non-unit PR contact frontier

The remaining `V>1` carrier classification should not repeatedly unpack the
terminal state.  This file packages the two pieces which have now been proved
source-honestly:

* the primitive highest pair, with its two literal nonzero source/contact
  coefficients; and
* the locked `H^ell` pair, again with literal nonzero source/contact
  coefficients.

Both are synchronized to the same normalized quotient parameter `V` and their
exact canonical contact orders are stored as derived equalities.  The only
missing information after this package is the pattern of the intermediate
quotient fibres.

There is no new mathematical assumption in these structures.  Every field is
constructed by the preceding source reconstruction, orientation and contact
order theorems.
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

/-- Complete source-honest frontier for the non-unit orientation `(1,V)`. -/
structure QsOtherFacetPrLeftVContactFrontierData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  V : ℕ
  V_gt_one : 1 < V
  quotient : QsOtherFacetPrQuotientCarrierData C P 1 V
  highest : QsOtherFacetPrHighestSliceLeftSourceData C P S R
  highest_V_eq : highest.V = V
  locked : QsOtherFacetPrLockedLeftVSourceData C P R V
  highest_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 V highest.e0 =
      T.topFace.degree - ((V + 1) * highest.n + 1)
  locked_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 V C.ray.facetExponent =
      T.topFace.degree - ((V + 1) * (locked.ell + 1) + 1)

/-- Complete source-honest frontier for the swapped non-unit orientation
`(V,1)`. -/
structure QsOtherFacetPrRightVContactFrontierData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  V : ℕ
  V_gt_one : 1 < V
  quotient : QsOtherFacetPrQuotientCarrierData C P V 1
  highest : QsOtherFacetPrHighestSliceRightSourceData C P S R
  highest_V_eq : highest.V = V
  locked : QsOtherFacetPrLockedRightVSourceData C P R V
  highest_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) V 1 highest.e0 =
      T.topFace.degree - ((V + 1) * highest.n + 1)
  locked_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) V 1 C.ray.facetExponent =
      T.topFace.degree - ((V + 1) * (locked.ell + 1) + 1)

/-- A normalized `(1,V)` carrier with `V>1` and a nontrivial highest slice
canonically produces the complete left contact frontier. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_leftV_contactFrontier
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {V : ℕ}
    (hV : 1 < V)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 V)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrLeftVContactFrontierData C P S R) := by
  rcases S.pr_highest_slice_leftV_source_data
      R hV Q hthree houtThree hnontrivial with ⟨H, hHV⟩
  rcases S.pr_locked_leftV_source_data
      R hV Q hthree houtThree hnontrivial with ⟨L⟩
  exact ⟨{
    V := V
    V_gt_one := hV
    quotient := Q
    highest := H
    highest_V_eq := hHV
    locked := L
    highest_contactOrder := H.quotientContactOrder_eq hHV
    locked_contactOrder := L.quotientContactOrder_eq
  }⟩

/-- Symmetric `(V,1)` source-honest contact frontier. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_rightV_contactFrontier
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {V : ℕ}
    (hV : 1 < V)
    (Q : QsOtherFacetPrQuotientCarrierData C P V 1)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrRightVContactFrontierData C P S R) := by
  rcases S.pr_highest_slice_rightV_source_data
      R hV Q hthree houtThree hnontrivial with ⟨H, hHV⟩
  rcases S.pr_locked_rightV_source_data
      R hV Q hthree houtThree hnontrivial with ⟨L⟩
  exact ⟨{
    V := V
    V_gt_one := hV
    quotient := Q
    highest := H
    highest_V_eq := hHV
    locked := L
    highest_contactOrder := H.quotientContactOrder_eq hHV
    locked_contactOrder := L.quotientContactOrder_eq
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
