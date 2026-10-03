import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointOrientation
import Mathlib.Tactic

/-!
# A19 unit PR endpoint-orientation normalization

At quotient parameter `V = 1`, the two locked `.pr` normal forms are literally
the same source exponents: the transverse factors `(ell+1) * V` and `ell * V`
reduce to `ell+1` and `ell`.  Their coefficient provenance is already attached
to the same literal ray endpoints.

Consequently the four bookkeeping constructors of
`QsOtherFacetPrUnitEndpointOrientationData` contain only two genuine unit
orientations.  This file performs that source-honest repackaging and nothing
else; no determinant or contact equation is changed.
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

/-- A right locked source package with unit transverse parameter is the same
literal locked ray as a left package.  Provenance is reused verbatim. -/
def QsOtherFacetPrLockedRightSourceData.toLeft_of_V_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (L : QsOtherFacetPrLockedRightSourceData C P R)
    (hV : L.V = 1) :
    QsOtherFacetPrLockedLeftSourceData C P R := by
  refine {
    ell := L.ell
    V := 1
    ell_pos := L.ell_pos
    V_pos := by norm_num
    facet_zero := L.facet_zero
    facet_one := L.facet_one
    facet_two := ?_
    facet_three := ?_
    outside_zero := L.outside_zero
    outside_one := L.outside_one
    outside_two := ?_
    outside_three := ?_
    facet_provenance := L.facet_provenance
    outside_provenance := L.outside_provenance
  }
  · simpa [hV] using L.facet_two
  · simpa using L.facet_three
  · simpa [hV] using L.outside_two
  · simpa using L.outside_three

/-- The converse unit repackaging. -/
def QsOtherFacetPrLockedLeftSourceData.toRight_of_V_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (L : QsOtherFacetPrLockedLeftSourceData C P R)
    (hV : L.V = 1) :
    QsOtherFacetPrLockedRightSourceData C P R := by
  refine {
    ell := L.ell
    V := 1
    ell_pos := L.ell_pos
    V_pos := by norm_num
    facet_zero := L.facet_zero
    facet_one := L.facet_one
    facet_two := ?_
    facet_three := ?_
    outside_zero := L.outside_zero
    outside_one := L.outside_one
    outside_two := ?_
    outside_three := ?_
    facet_provenance := L.facet_provenance
    outside_provenance := L.outside_provenance
  }
  · simpa using L.facet_two
  · simpa [hV] using L.facet_three
  · simpa using L.outside_two
  · simpa [hV] using L.outside_three

/-- **Only two genuine unit endpoint orientations remain.**  The mixed labels
are normalized by converting the unit locked package, without changing either
ray endpoint or any source/contact coefficient provenance. -/
theorem QsOtherFacetPrUnitEndpointOrientationData.sameOrientation_normalForm
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (O : QsOtherFacetPrUnitEndpointOrientationData C P S R) :
    (∃ H : QsOtherFacetPrHighestSliceLeftSourceData C P S R,
      ∃ L : QsOtherFacetPrLockedLeftSourceData C P R,
        H.V = 1 ∧ L.V = 1) ∨
      (∃ H : QsOtherFacetPrHighestSliceRightSourceData C P S R,
        ∃ L : QsOtherFacetPrLockedRightSourceData C P R,
          H.V = 1 ∧ L.V = 1) := by
  cases O with
  | sameLeft H L hH hL =>
      exact Or.inl ⟨H, L, hH, hL⟩
  | sameRight H L hH hL =>
      exact Or.inr ⟨H, L, hH, hL⟩
  | mixedLeftRight H L hH hL =>
      let L' := L.toLeft_of_V_eq_one hL
      exact Or.inl ⟨H, L', hH, rfl⟩
  | mixedRightLeft H L hH hL =>
      let L' := L.toRight_of_V_eq_one hL
      exact Or.inr ⟨H, L', hH, rfl⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
