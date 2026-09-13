import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrQuotientContactBridge
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneHighestSliceOrientation
import Mathlib.Tactic

/-!
# A19 exact contact orders in the non-unit PR orientations

After synchronizing the quotient parameter `V` with both the primitive highest
slice and the locked source ray, their honest contact orders are elementary.

For either transverse orientation the primitive highest pair has normalized
quotient-coordinate sum

    (V + 1) * n + 1,

while the locked ray has quotient-coordinate sum

    (V + 1) * (ell + 1) + 1.

Thus the corresponding canonical contact-Rees orders are the deficits from
those two integers.  These are the exact finite slope quantities used by the
remaining contact-aware carrier classification.  No contact order is equated
with the zero blocker clock or with any binary filtration order.
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

private theorem left_highest_quotient_sum
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrHighestSliceLeftSourceData C P S R)
    (hDV : D.V = V) :
    (rankThreeQuotientCoordinate 1 V D.e0).pair +
        (rankThreeQuotientCoordinate 1 V D.e0).firstTransverse +
        (rankThreeQuotientCoordinate 1 V D.e0).secondTransverse =
      (V + 1) * D.n + 1 := by
  rw [← hDV]
  simp [rankThreeQuotientCoordinate, D.e0_zero, D.e0_one,
    D.e0_two, D.e0_three]
  ring

private theorem right_highest_quotient_sum
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrHighestSliceRightSourceData C P S R)
    (hDV : D.V = V) :
    (rankThreeQuotientCoordinate V 1 D.e0).pair +
        (rankThreeQuotientCoordinate V 1 D.e0).firstTransverse +
        (rankThreeQuotientCoordinate V 1 D.e0).secondTransverse =
      (V + 1) * D.n + 1 := by
  rw [← hDV]
  simp [rankThreeQuotientCoordinate, D.e0_zero, D.e0_one,
    D.e0_two, D.e0_three]
  ring

private theorem left_locked_quotient_sum
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrLockedLeftVSourceData C P R V) :
    (rankThreeQuotientCoordinate 1 V C.ray.facetExponent).pair +
        (rankThreeQuotientCoordinate 1 V C.ray.facetExponent).firstTransverse +
        (rankThreeQuotientCoordinate 1 V C.ray.facetExponent).secondTransverse =
      (V + 1) * (D.ell + 1) + 1 := by
  simp [rankThreeQuotientCoordinate, D.facet_zero, D.facet_one,
    D.facet_two, D.facet_three]
  ring

private theorem right_locked_quotient_sum
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrLockedRightVSourceData C P R V) :
    (rankThreeQuotientCoordinate V 1 C.ray.facetExponent).pair +
        (rankThreeQuotientCoordinate V 1 C.ray.facetExponent).firstTransverse +
        (rankThreeQuotientCoordinate V 1 C.ray.facetExponent).secondTransverse =
      (V + 1) * (D.ell + 1) + 1 := by
  simp [rankThreeQuotientCoordinate, D.facet_zero, D.facet_one,
    D.facet_two, D.facet_three]
  ring

/-- Exact honest contact order of the primitive highest pair in orientation
`(1,V)`. -/
theorem QsOtherFacetPrHighestSliceLeftSourceData.quotientContactOrder_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrHighestSliceLeftSourceData C P S R)
    (hDV : D.V = V) :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 V D.e0 =
      T.topFace.degree - ((V + 1) * D.n + 1) := by
  unfold qsOtherFacetPrQuotientContactOrder
  rw [left_highest_quotient_sum D hDV]

/-- Symmetric exact order for orientation `(V,1)`. -/
theorem QsOtherFacetPrHighestSliceRightSourceData.quotientContactOrder_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrHighestSliceRightSourceData C P S R)
    (hDV : D.V = V) :
    qsOtherFacetPrQuotientContactOrder (T := T) V 1 D.e0 =
      T.topFace.degree - ((V + 1) * D.n + 1) := by
  unfold qsOtherFacetPrQuotientContactOrder
  rw [right_highest_quotient_sum D hDV]

/-- Exact honest contact order of the locked `H^ell` pair in orientation
`(1,V)`. -/
theorem QsOtherFacetPrLockedLeftVSourceData.quotientContactOrder_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrLockedLeftVSourceData C P R V) :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 V C.ray.facetExponent =
      T.topFace.degree - ((V + 1) * (D.ell + 1) + 1) := by
  unfold qsOtherFacetPrQuotientContactOrder
  rw [left_locked_quotient_sum D]

/-- Symmetric exact order of the locked pair in orientation `(V,1)`. -/
theorem QsOtherFacetPrLockedRightVSourceData.quotientContactOrder_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {V : ℕ}
    (D : QsOtherFacetPrLockedRightVSourceData C P R V) :
    qsOtherFacetPrQuotientContactOrder (T := T) V 1 C.ray.facetExponent =
      T.topFace.degree - ((V + 1) * (D.ell + 1) + 1) := by
  unfold qsOtherFacetPrQuotientContactOrder
  rw [right_locked_quotient_sum D]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
