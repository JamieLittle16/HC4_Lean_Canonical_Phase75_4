import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointNormalization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneContactOrders
import Mathlib.Tactic

/-!
# A19 source-honest unit PR contact frontier

The normalized unit quotient has direction `(1,-1,-1,-1)`.  After the unit
endpoint-orientation normalization there are only two genuine source
orientations, exchanged by the transverse coordinate swap.  This file packages
each orientation with the same literal endpoint provenance and honest contact
orders used by the non-unit frontier, but without introducing the false
hypothesis `1 < V`.

No determinant or clock identity is added here.
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

/-- Repackage a literal left locked endpoint whose internal parameter is one as
the parameter-synchronised locked data at quotient parameter one. -/
def QsOtherFacetPrLockedLeftSourceData.toLockedLeftVOne
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (L : QsOtherFacetPrLockedLeftSourceData C P R)
    (hV : L.V = 1) :
    QsOtherFacetPrLockedLeftVSourceData C P R 1 := by
  refine {
    ell := L.ell
    ell_pos := L.ell_pos
    facet_zero := L.facet_zero
    facet_one := L.facet_one
    facet_two := L.facet_two
    facet_three := ?_
    outside_zero := L.outside_zero
    outside_one := L.outside_one
    outside_two := L.outside_two
    outside_three := ?_
    facet_provenance := L.facet_provenance
    outside_provenance := L.outside_provenance
  }
  · simpa [hV] using L.facet_three
  · simpa [hV] using L.outside_three

/-- Transverse-swapped unit locked data. -/
def QsOtherFacetPrLockedRightSourceData.toLockedRightVOne
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (L : QsOtherFacetPrLockedRightSourceData C P R)
    (hV : L.V = 1) :
    QsOtherFacetPrLockedRightVSourceData C P R 1 := by
  refine {
    ell := L.ell
    ell_pos := L.ell_pos
    facet_zero := L.facet_zero
    facet_one := L.facet_one
    facet_two := ?_
    facet_three := L.facet_three
    outside_zero := L.outside_zero
    outside_one := L.outside_one
    outside_two := ?_
    outside_three := L.outside_three
    facet_provenance := L.facet_provenance
    outside_provenance := L.outside_provenance
  }
  · simpa [hV] using L.facet_two
  · simpa [hV] using L.outside_two

/-- Complete unit source/contact data in the left highest-slice orientation. -/
structure QsOtherFacetPrUnitLeftContactFrontierData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  quotient : QsOtherFacetPrQuotientCarrierData C P 1 1
  highest : QsOtherFacetPrHighestSliceLeftSourceData C P S R
  highest_V_eq_one : highest.V = 1
  locked : QsOtherFacetPrLockedLeftVSourceData C P R 1
  highest_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 1 highest.e0 =
      T.topFace.degree - (2 * highest.n + 1)
  locked_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 1 C.ray.facetExponent =
      T.topFace.degree - (2 * (locked.ell + 1) + 1)

/-- Complete unit source/contact data in the transverse-swapped orientation. -/
structure QsOtherFacetPrUnitRightContactFrontierData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  quotient : QsOtherFacetPrQuotientCarrierData C P 1 1
  highest : QsOtherFacetPrHighestSliceRightSourceData C P S R
  highest_V_eq_one : highest.V = 1
  locked : QsOtherFacetPrLockedRightVSourceData C P R 1
  highest_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 1 highest.e0 =
      T.topFace.degree - (2 * highest.n + 1)
  locked_contactOrder :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 1 C.ray.facetExponent =
      T.topFace.degree - (2 * (locked.ell + 1) + 1)

/-- **Unit source/contact frontier.**  A nontrivial unit quotient produces one
of the two genuine transverse orientations, with literal endpoint provenance
and exact honest contact orders retained. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_unitContactFrontier
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
    Nonempty (QsOtherFacetPrUnitLeftContactFrontierData C P S R) ∨
      Nonempty (QsOtherFacetPrUnitRightContactFrontierData C P S R) := by
  rcases S.pr_unitEndpointOrientation R Q hthree houtThree hnontrivial with ⟨O⟩
  rcases O.sameOrientation_normalForm with hleft | hright
  · rcases hleft with ⟨H, L, hH, hL⟩
    let L1 := L.toLockedLeftVOne hL
    left
    exact ⟨{
      quotient := Q
      highest := H
      highest_V_eq_one := hH
      locked := L1
      highest_contactOrder := by
        simpa [show (1 + 1 : ℕ) = 2 by norm_num] using H.quotientContactOrder_eq hH
      locked_contactOrder := by
        simpa [L1, show (1 + 1 : ℕ) = 2 by norm_num] using L1.quotientContactOrder_eq
    }⟩
  · rcases hright with ⟨H, L, hH, hL⟩
    let L1 := L.toLockedRightVOne hL
    right
    exact ⟨{
      quotient := Q
      highest := H
      highest_V_eq_one := hH
      locked := L1
      highest_contactOrder := by
        simpa [show (1 + 1 : ℕ) = 2 by norm_num] using H.quotientContactOrder_eq hH
      locked_contactOrder := by
        simpa [L1, show (1 + 1 : ℕ) = 2 by norm_num] using L1.quotientContactOrder_eq
    }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
