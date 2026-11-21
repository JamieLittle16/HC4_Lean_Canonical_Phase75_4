import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsReducedLowerFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRankThreeDegreeGap
import Mathlib.Tactic

/-!
# A19.94: strict transverse direction lock at the other-facet endpoint

A19.81 gives the balance-free cross-product relation at a unit lower `qs`
endpoint which lands rank three on a different coordinate facet.  A19.84 says
that this endpoint has strictly smaller ordinary degree than its starting
`qs` endpoint.  Positivity on the two coordinates which survive at the new
rank-three facet then upgrades proportionality plus total-degree decrease to
coordinatewise strict decrease.

Thus in each cyclic case the two positive transverse pairs lie on the same
rational ray and the outside pair is strictly smaller in both coordinates.
This is the exact finite-support direction lock needed by the existing binary
staircase/profile rigidity layer.  No balance relation or global progress
measure is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem positive_cross_strict_component_drop
    {B C V W : ℕ}
    (hV : 0 < V) (hW : 0 < W)
    (hcross : B * W = C * V)
    (hsum : V + W < B + C) :
    V < B ∧ W < C := by
  have hVB : V < B := by
    by_contra hnot
    have hBV : B ≤ V := Nat.le_of_not_gt hnot
    by_cases hWC : W < C
    · have hleft : B * W ≤ V * W := Nat.mul_le_mul_right W hBV
      have hright : V * W < C * V := by
        rw [Nat.mul_comm V W]
        exact Nat.mul_lt_mul_of_pos_right hWC hV
      omega
    · have hCW : C ≤ W := Nat.le_of_not_gt hWC
      omega
  have hWC : W < C := by
    by_contra hnot
    have hCW : C ≤ W := Nat.le_of_not_gt hnot
    by_cases hVB' : V < B
    · have hleft : C * V ≤ W * V := Nat.mul_le_mul_right V hCW
      have hright : W * V < B * W := by
        rw [Nat.mul_comm W V]
        exact Nat.mul_lt_mul_of_pos_right hVB' hW
      omega
    · have hBV : B ≤ V := Nat.le_of_not_gt hVB'
      omega
  exact ⟨hVB, hWC⟩

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- At a `.pr` outside endpoint, the positive `(2,3)` pair remains on the
same rational ray as the starting pair and drops strictly in both entries. -/
theorem qs_ray_pr_outside_strict_directionLock
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    C.ray.facetExponent 2 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 2 ∧
      C.ray.outsideExponent 2 < C.ray.facetExponent 2 ∧
      C.ray.outsideExponent 3 < C.ray.facetExponent 3 := by
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hout := (HC4.Newton.mvRankThreeOnFacet_iff .pr
    C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨hout1, _hout0, hout2, hout3⟩
  have harith := C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree
  have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 := harith.1
  have hcross := harith.2
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent <
        HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent := by
    rw [C.qs_ray_facet_degree_eq_topFace]
    exact C.qs_ray_outside_degree_lt_topFace
  have hout0eq : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := hbase.1
  have hsum :
      C.ray.outsideExponent 2 + C.ray.outsideExponent 3 <
        C.ray.facetExponent 2 + C.ray.facetExponent 3 := by
    simp only [HC4.Polynomial.ordinaryDegree4] at hdeg
    omega
  have hdrop := positive_cross_strict_component_drop
    hout2 hout3 hcross hsum
  exact ⟨hcross, hdrop.1, hdrop.2⟩

/-- Cyclic `.sp` form of the strict direction lock. -/
theorem qs_ray_sp_outside_strict_directionLock
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    C.ray.facetExponent 1 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 1 ∧
      C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
      C.ray.outsideExponent 3 < C.ray.facetExponent 3 := by
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hout := (HC4.Newton.mvRankThreeOnFacet_iff .sp
    C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨hout2, _hout0, hout1, hout3⟩
  have harith := C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree
  have hfacet2 : C.ray.facetExponent (2 : Fin 4) = 1 := harith.1
  have hcross := harith.2
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent <
        HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent := by
    rw [C.qs_ray_facet_degree_eq_topFace]
    exact C.qs_ray_outside_degree_lt_topFace
  have hout0eq : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := hbase.1
  have hsum :
      C.ray.outsideExponent 1 + C.ray.outsideExponent 3 <
        C.ray.facetExponent 1 + C.ray.facetExponent 3 := by
    simp only [HC4.Polynomial.ordinaryDegree4] at hdeg
    omega
  have hdrop := positive_cross_strict_component_drop
    hout1 hout3 hcross hsum
  exact ⟨hcross, hdrop.1, hdrop.2⟩

/-- Cyclic `.rq` form of the strict direction lock. -/
theorem qs_ray_rq_outside_strict_directionLock
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    C.ray.facetExponent 1 * C.ray.outsideExponent 2 =
        C.ray.facetExponent 2 * C.ray.outsideExponent 1 ∧
      C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
      C.ray.outsideExponent 2 < C.ray.facetExponent 2 := by
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hout := (HC4.Newton.mvRankThreeOnFacet_iff .rq
    C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨hout3, _hout0, hout1, hout2⟩
  have harith := C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree
  have hfacet3 : C.ray.facetExponent (3 : Fin 4) = 1 := harith.1
  have hcross := harith.2
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent <
        HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent := by
    rw [C.qs_ray_facet_degree_eq_topFace]
    exact C.qs_ray_outside_degree_lt_topFace
  have hout0eq : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := hbase.1
  have hsum :
      C.ray.outsideExponent 1 + C.ray.outsideExponent 2 <
        C.ray.facetExponent 1 + C.ray.facetExponent 2 := by
    simp only [HC4.Polynomial.ordinaryDegree4] at hdeg
    omega
  have hdrop := positive_cross_strict_component_drop
    hout1 hout2 hcross hsum
  exact ⟨hcross, hdrop.1, hdrop.2⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
