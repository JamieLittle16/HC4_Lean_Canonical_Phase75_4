import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrPrimitiveEndpoint
import Mathlib.Tactic

/-!
# A19 exact locked PR ray normal form

Once the actual nontrivial highest slice has forced one transverse drop to be
one, the old cross-product relation on the original source ray determines the
other endpoint coordinates exactly.  This file records the resulting source
normal form without introducing any new carrier or clock.
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

/-- **Locked-ray normal form.**  A nontrivial highest `.pr` slice forces the
original locked source ray to be, up to swapping coordinates `2` and `3`,

`(0,1,ell+1,(ell+1)V) -- (1,0,ell,ell V)`

with `ell,V > 0`.  This is the exact paper normal form and retains literal
source exponents. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_locked_ray_normal_form_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    (∃ ell V : ℕ, 0 < ell ∧ 0 < V ∧
      C.ray.facetExponent 0 = 0 ∧
      C.ray.facetExponent 1 = 1 ∧
      C.ray.facetExponent 2 = ell + 1 ∧
      C.ray.facetExponent 3 = (ell + 1) * V ∧
      C.ray.outsideExponent 0 = 1 ∧
      C.ray.outsideExponent 1 = 0 ∧
      C.ray.outsideExponent 2 = ell ∧
      C.ray.outsideExponent 3 = ell * V) ∨
    (∃ ell V : ℕ, 0 < ell ∧ 0 < V ∧
      C.ray.facetExponent 0 = 0 ∧
      C.ray.facetExponent 1 = 1 ∧
      C.ray.facetExponent 2 = (ell + 1) * V ∧
      C.ray.facetExponent 3 = ell + 1 ∧
      C.ray.outsideExponent 0 = 1 ∧
      C.ray.outsideExponent 1 = 0 ∧
      C.ray.outsideExponent 2 = ell * V ∧
      C.ray.outsideExponent 3 = ell) := by
  rcases S.pr_endpoint_orientation_of_nontrivial
      hthree houtThree hnontrivial with ⟨D, A, horient⟩
  have hfacet := mvRankThreeOnFacet_qs hthree
  have hout := (mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree
  have hbase := C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree
  have hout0 : C.ray.outsideExponent 0 = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  rcases horient with hleft | hright
  · left
    have hfacet2 :
        C.ray.facetExponent 2 = C.ray.outsideExponent 2 + 1 := by
      simpa [hleft.2.1] using D.facet_two_eq
    have hfacet3 :
        C.ray.facetExponent 3 = C.ray.outsideExponent 3 + D.beta :=
      D.facet_three_eq
    have hcross := hbase.2
    rw [hfacet2, hfacet3] at hcross
    have hout3 :
        C.ray.outsideExponent 3 = C.ray.outsideExponent 2 * D.beta := by
      nlinarith
    have hfacet3' :
        C.ray.facetExponent 3 = (C.ray.outsideExponent 2 + 1) * D.beta := by
      rw [hfacet3, hout3]
      ring
    exact ⟨C.ray.outsideExponent 2, D.beta,
      hout.2.2.1, D.beta_pos,
      hfacet.1, hbase.1, hfacet2, hfacet3',
      hout0, hout.1, rfl, hout3⟩
  · right
    have hfacet2 :
        C.ray.facetExponent 2 = C.ray.outsideExponent 2 + D.alpha :=
      D.facet_two_eq
    have hfacet3 :
        C.ray.facetExponent 3 = C.ray.outsideExponent 3 + 1 := by
      simpa [hright.2.1] using D.facet_three_eq
    have hcross := hbase.2
    rw [hfacet2, hfacet3] at hcross
    have hout2 :
        C.ray.outsideExponent 2 = C.ray.outsideExponent 3 * D.alpha := by
      nlinarith
    have hfacet2' :
        C.ray.facetExponent 2 = (C.ray.outsideExponent 3 + 1) * D.alpha := by
      rw [hfacet2, hout2]
      ring
    exact ⟨C.ray.outsideExponent 3, D.alpha,
      hout.2.2.2, D.alpha_pos,
      hfacet.1, hbase.1, hfacet2', hfacet3,
      hout0, hout.1, hout2, rfl⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
