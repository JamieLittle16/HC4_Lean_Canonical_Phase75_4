import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarBoundaryStart
import HC4.Newton.FiniteSupportCrossFacetRayAffineRR
import HC4.RationalRigidity.LineSupportedHessianRigidity
import Mathlib.Tactic

/-!
# A19 source-honest affine-RR realisation of a highest planar slice

A nontrivial highest pair slice now has a genuine boundary start in coordinate
`0`, and its entire support is already known to be parallel to the locked
source ray.  Rather than introduce another coefficient reconstruction, package
the slice itself as the existing balance-free `CrossFacetRayData` with contact
coordinate `0`.

This is deliberately lossless.  The `face` of the constructed ray is literally
the highest slice, its facet endpoint is an actual supported slice monomial,
and the mature A19.69 `zeroAffineLineData` reconstruction therefore retains the
actual slice coefficients.  The resulting affine slopes are exactly the
integer locked-ray coordinate differences cast into the coefficient field.
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

/-- Exact affine-RR package attached to a nontrivial source-honest highest
pair slice. -/
structure QsOtherFacetPlanarAffineRRPackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet)
    (P : QsOtherFacetPlanarCarrierPackage C next)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P) where
  ray : HC4.Newton.CrossFacetRayData S.slice (0 : Fin 4)
  face_eq : ray.face = S.slice
  facet_transverse_pos :
    ∀ i : Fin 4, i ≠ 0 → 0 < ray.facetExponent i
  slope_eq_locked :
    ∀ i : Fin 4,
      ray.zeroSlope i =
        (((C.ray.outsideExponent i : ℤ) -
          (C.ray.facetExponent i : ℤ) : ℤ) : K)

/-- Two supported highest-slice exponents satisfy the proportionality equation
required by `CrossFacetRayData`, once the first has coordinate `0 = 0`. -/
private theorem highestSlice_cross_proportional
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    {e f d : Fin 4 →₀ ℕ}
    (he : e ∈ S.slice.support)
    (hf : f ∈ S.slice.support)
    (hd : d ∈ S.slice.support)
    (he0 : e 0 = 0)
    (k : Fin 4) :
    (f 0 : ℤ) * ((d k : ℤ) - (e k : ℤ)) =
      (d 0 : ℤ) * ((f k : ℤ) - (e k : ℤ)) := by
  have hdpar := S.support_difference_parallel_ray
    hthree hne houtThree hd he k
  have hfpar := S.support_difference_parallel_ray
    hthree hne houtThree hf he k
  rw [he0] at hdpar hfpar
  simp only [Nat.cast_zero, sub_zero] at hdpar hfpar
  calc
    (f 0 : ℤ) * ((d k : ℤ) - (e k : ℤ)) =
        (f 0 : ℤ) *
          ((d 0 : ℤ) *
            ((C.ray.outsideExponent k : ℤ) -
              (C.ray.facetExponent k : ℤ))) := by rw [hdpar]
    _ = (d 0 : ℤ) *
        ((f 0 : ℤ) *
          ((C.ray.outsideExponent k : ℤ) -
            (C.ray.facetExponent k : ℤ))) := by ring
    _ = (d 0 : ℤ) * ((f k : ℤ) - (e k : ℤ)) := by rw [hfpar]

/-- **Lossless affine-RR package.**  Every nontrivial highest pair slice is an
instance of the already-certified balance-free cross-facet ray interface, with
its affine slopes equal to the original locked source-ray direction. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.affineRRPackage_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPlanarAffineRRPackage C next P S) := by
  rcases S.exists_boundary_start_of_nontrivial
      hthree hne houtThree hnontrivial with
    ⟨e, he, he0, heTrans⟩
  rcases hnontrivial with ⟨a, ha, b, hb, hab⟩
  have hother : ∃ f ∈ S.slice.support, f ≠ e := by
    by_cases hae : a = e
    · refine ⟨b, hb, ?_⟩
      intro hbe
      exact hab (hae.trans hbe.symm)
    · exact ⟨a, ha, hae⟩
  rcases hother with ⟨f, hf, hfe⟩
  have hf0ne : f 0 ≠ 0 := by
    intro hf0
    apply hfe
    exact S.eq_of_zeroCoordinate_eq hthree hne houtThree hf he (by simpa [he0] using hf0)
  have hf0pos : 0 < f 0 := Nat.pos_of_ne_zero hf0ne

  let R : HC4.Newton.CrossFacetRayData S.slice (0 : Fin 4) := {
    face := S.slice
    facetExponent := e
    outsideExponent := f
    facet_mem_source := he
    outside_mem_source := hf
    facet_mem_face := he
    outside_mem_face := hf
    facet_coordinate_zero := he0
    outside_coordinate_pos := hf0pos
    support_subset := by
      intro d hd
      exact hd
    hessian_zero_of_source := by
      intro hzero
      exact hzero
    first_auxiliary_support_bound := by
      intro d hd
      exact le_of_eq (highestSlice_cross_proportional
        S hthree hne houtThree he hf hd he0 (crossFacetRayAux0 (0 : Fin 4)))
    affine_proportional := by
      intro d hd k
      exact highestSlice_cross_proportional
        S hthree hne houtThree he hf hd he0 k
  }

  have hslope :
      ∀ i : Fin 4,
        R.zeroSlope i =
          (((C.ray.outsideExponent i : ℤ) -
            (C.ray.facetExponent i : ℤ) : ℤ) : K) := by
    intro i
    have hfpar := S.support_difference_parallel_ray
      hthree hne houtThree hf he i
    rw [he0] at hfpar
    simp only [Nat.cast_zero, sub_zero] at hfpar
    have hf0K : ((f 0 : ℕ) : K) ≠ 0 := by
      exact_mod_cast hf0ne
    unfold HC4.Newton.CrossFacetRayData.zeroSlope
    change
      ((((f i : ℤ) - (e i : ℤ) : ℤ) : K) / ((f 0 : ℕ) : K)) = _
    have hfparK := congrArg (fun z : ℤ => (z : K)) hfpar
    push_cast at hfparK
    field_simp [hf0K]
    simpa using hfparK

  exact ⟨{
    ray := R
    face_eq := rfl
    facet_transverse_pos := by
      intro i hi
      exact heTrans i hi
    slope_eq_locked := hslope
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
