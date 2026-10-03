import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrCarrierReconstruction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrLockedNormalForm
import Mathlib.Tactic

/-!
# A19 literal source coefficients on the locked PR ray

The nontrivial primitive highest slice already forces the original locked
`.pr` ray into one of the two exact normal forms

    (0,1,ell+1,(ell+1)V) -- (1,0,ell,ell V)

or its swap in coordinates `2,3`.

This file adds no geometry.  It simply remembers that both endpoints of that
ray are actual support points of the source-honest planar carrier and therefore
carry the coefficient/source/contact provenance proved in
`...PrCarrierReconstruction`.

These are exactly the two nonzero coefficients which become `a` and `b` in the
final two-function carrier.  Keeping them attached to the literal locked
source exponents avoids recreating either coefficient during polynomial
reconstruction.
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

/-- Left locked-ray orientation, with literal source/contact coefficient
provenance at both endpoints. -/
structure QsOtherFacetPrLockedLeftSourceData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  ell : ℕ
  V : ℕ
  ell_pos : 0 < ell
  V_pos : 0 < V
  facet_zero : C.ray.facetExponent 0 = 0
  facet_one : C.ray.facetExponent 1 = 1
  facet_two : C.ray.facetExponent 2 = ell + 1
  facet_three : C.ray.facetExponent 3 = (ell + 1) * V
  outside_zero : C.ray.outsideExponent 0 = 1
  outside_one : C.ray.outsideExponent 1 = 0
  outside_two : C.ray.outsideExponent 2 = ell
  outside_three : C.ray.outsideExponent 3 = ell * V
  facet_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.facetExponent
  outside_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.outsideExponent

/-- Right/transverse-swapped locked-ray orientation, again retaining the two
actual source/contact coefficients. -/
structure QsOtherFacetPrLockedRightSourceData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  ell : ℕ
  V : ℕ
  ell_pos : 0 < ell
  V_pos : 0 < V
  facet_zero : C.ray.facetExponent 0 = 0
  facet_one : C.ray.facetExponent 1 = 1
  facet_two : C.ray.facetExponent 2 = (ell + 1) * V
  facet_three : C.ray.facetExponent 3 = ell + 1
  outside_zero : C.ray.outsideExponent 0 = 1
  outside_one : C.ray.outsideExponent 1 = 0
  outside_two : C.ray.outsideExponent 2 = ell * V
  outside_three : C.ray.outsideExponent 3 = ell
  facet_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.facetExponent
  outside_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.outsideExponent

/-- The two literal locked-ray endpoints are support points of every planar
carrier produced from that ray. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_locked_endpoints_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr) :
    C.ray.facetExponent ∈ P.carrier.support ∧
      C.ray.outsideExponent ∈ P.carrier.support := by
  constructor
  · have h := P.ray_support_subset
      (show C.ray.facetExponent ∈
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) by
          simpa using C.ray.facet_mem_face)
    simpa using h
  · have h := P.ray_support_subset
      (show C.ray.outsideExponent ∈
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) by
          simpa using C.ray.outside_mem_face)
    simpa using h

/-- **Source-honest locked-ray coefficient frontier.**  A nontrivial highest
slice gives one of the two exact locked normal forms, and in the same branch we
retain the nonzero source/contact coefficient at each literal endpoint. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_locked_source_data_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrLockedLeftSourceData C P R) ∨
      Nonempty (QsOtherFacetPrLockedRightSourceData C P R) := by
  rcases P.pr_locked_endpoints_mem with ⟨hfacetP, houtP⟩
  have hfacetProv := P.pr_coefficientProvenance R hfacetP
  have houtProv := P.pr_coefficientProvenance R houtP
  rcases S.pr_locked_ray_normal_form_of_nontrivial
      hthree houtThree hnontrivial with hleft | hright
  · rcases hleft with
      ⟨ell, V, hell, hV,
        hf0, hf1, hf2, hf3, ho0, ho1, ho2, ho3⟩
    left
    exact ⟨{
      ell := ell
      V := V
      ell_pos := hell
      V_pos := hV
      facet_zero := hf0
      facet_one := hf1
      facet_two := hf2
      facet_three := hf3
      outside_zero := ho0
      outside_one := ho1
      outside_two := ho2
      outside_three := ho3
      facet_provenance := hfacetProv
      outside_provenance := houtProv
    }⟩
  · rcases hright with
      ⟨ell, V, hell, hV,
        hf0, hf1, hf2, hf3, ho0, ho1, ho2, ho3⟩
    right
    exact ⟨{
      ell := ell
      V := V
      ell_pos := hell
      V_pos := hV
      facet_zero := hf0
      facet_one := hf1
      facet_two := hf2
      facet_three := hf3
      outside_zero := ho0
      outside_one := ho1
      outside_two := ho2
      outside_three := ho3
      facet_provenance := hfacetProv
      outside_provenance := houtProv
    }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
