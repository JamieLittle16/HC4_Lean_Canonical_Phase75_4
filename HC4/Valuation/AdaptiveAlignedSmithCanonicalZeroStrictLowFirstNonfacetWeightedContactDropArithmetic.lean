import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralSourceContact
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetEndpointArithmetic
import Mathlib.Tactic

/-!
# A19.100b: integral contact gap is the locked transverse degree drop

The source-native integral contact from A19.97 supplies an integer `r >= 2`
with

    ordinaryDegree4 d + r * d[0] = topDegree

on the actual extracted ray face.  In the three possible other-facet
rank-three cases the endpoint arithmetic is already rigid:

* `.pr`: the start has coordinate `1 = 1`, the outside endpoint has
  coordinate `1 = 0`;
* `.sp`: the same statement holds in coordinate `2`;
* `.rq`: the same statement holds in coordinate `3`.

Both endpoints lie on the integral contact level and the outside longitudinal
coordinate is exactly one.  Cancelling these fixed coordinates shows that the
integral contact gap is exactly the total drop in the two surviving transverse
coordinates.  This is the first integer identity required by the final
source-to-binary staircase straightening.

No gcd choice, primitive-ray assertion, planar terminal, or progress measure is
introduced.
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

/-- In the `.pr` branch the integral contact gap is exactly the total strict
fall in the locked `(2,3)` pair. -/
theorem qs_ray_pr_integral_contactGap_add_outside_eq_facet
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ r : ℕ,
      2 ≤ r ∧
      C.bump = C.scale * r ∧
      r + C.ray.outsideExponent 2 + C.ray.outsideExponent 3 =
        C.ray.facetExponent 2 + C.ray.facetExponent 3 := by
  rcases C.qs_ray_otherFacet_integral_source_contact
      hthree (next := .pr) (by decide) houtThree with
    ⟨r, hr, hbump, _hsource, hface⟩
  have hfacet := hface C.ray.facet_mem_face
  have hout := hface C.ray.outside_mem_face
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hpr := (HC4.Newton.mvRankThreeOnFacet_iff .pr
    C.ray.outsideExponent).1 houtThree
  rcases hpr with ⟨hout1, _hout0, _hout2, _hout3⟩
  have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  change HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent +
      r * C.ray.facetExponent (0 : Fin 4) = T.topFace.degree at hfacet
  change HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent +
      r * C.ray.outsideExponent (0 : Fin 4) = T.topFace.degree at hout
  simp only [HC4.Polynomial.ordinaryDegree4] at hfacet hout
  simp only [hbase.1, hfacet1] at hfacet
  simp only [hout0, hout1] at hout
  refine ⟨r, hr, hbump, ?_⟩
  omega

/-- Cyclic `.sp` form: the integral gap is the total drop in `(1,3)`. -/
theorem qs_ray_sp_integral_contactGap_add_outside_eq_facet
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    ∃ r : ℕ,
      2 ≤ r ∧
      C.bump = C.scale * r ∧
      r + C.ray.outsideExponent 1 + C.ray.outsideExponent 3 =
        C.ray.facetExponent 1 + C.ray.facetExponent 3 := by
  rcases C.qs_ray_otherFacet_integral_source_contact
      hthree (next := .sp) (by decide) houtThree with
    ⟨r, hr, hbump, _hsource, hface⟩
  have hfacet := hface C.ray.facet_mem_face
  have hout := hface C.ray.outside_mem_face
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hsp := (HC4.Newton.mvRankThreeOnFacet_iff .sp
    C.ray.outsideExponent).1 houtThree
  rcases hsp with ⟨hout2, _hout0, _hout1, _hout3⟩
  have hfacet2 : C.ray.facetExponent (2 : Fin 4) = 1 :=
    (C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  change HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent +
      r * C.ray.facetExponent (0 : Fin 4) = T.topFace.degree at hfacet
  change HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent +
      r * C.ray.outsideExponent (0 : Fin 4) = T.topFace.degree at hout
  simp only [HC4.Polynomial.ordinaryDegree4] at hfacet hout
  simp only [hbase.1, hfacet2] at hfacet
  simp only [hout0, hout2] at hout
  refine ⟨r, hr, hbump, ?_⟩
  omega

/-- Cyclic `.rq` form: the integral gap is the total drop in `(1,2)`. -/
theorem qs_ray_rq_integral_contactGap_add_outside_eq_facet
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    ∃ r : ℕ,
      2 ≤ r ∧
      C.bump = C.scale * r ∧
      r + C.ray.outsideExponent 1 + C.ray.outsideExponent 2 =
        C.ray.facetExponent 1 + C.ray.facetExponent 2 := by
  rcases C.qs_ray_otherFacet_integral_source_contact
      hthree (next := .rq) (by decide) houtThree with
    ⟨r, hr, hbump, _hsource, hface⟩
  have hfacet := hface C.ray.facet_mem_face
  have hout := hface C.ray.outside_mem_face
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hrq := (HC4.Newton.mvRankThreeOnFacet_iff .rq
    C.ray.outsideExponent).1 houtThree
  rcases hrq with ⟨hout3, _hout0, _hout1, _hout2⟩
  have hfacet3 : C.ray.facetExponent (3 : Fin 4) = 1 :=
    (C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  change HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent +
      r * C.ray.facetExponent (0 : Fin 4) = T.topFace.degree at hfacet
  change HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent +
      r * C.ray.outsideExponent (0 : Fin 4) = T.topFace.degree at hout
  simp only [HC4.Polynomial.ordinaryDegree4] at hfacet hout
  simp only [hbase.1, hfacet3] at hfacet
  simp only [hout0, hout3] at hout
  refine ⟨r, hr, hbump, ?_⟩
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
