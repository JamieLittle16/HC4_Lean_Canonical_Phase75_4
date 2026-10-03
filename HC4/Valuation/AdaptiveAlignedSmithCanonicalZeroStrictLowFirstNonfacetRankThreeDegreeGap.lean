import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetEndpointArithmetic
import Mathlib.Tactic

/-!
# A19.88: a different rank-three lower endpoint loses at least two degrees

A19.84 gives a strict ordinary-degree drop from the starting `.qs` endpoint to
the actual unit outside endpoint.  A19.81 gives substantially more arithmetic
when that outside endpoint is itself rank three on a different coordinate
facet: the corresponding starting transverse exponent is exactly one and the
other two coordinates satisfy a positive cross-product identity.

For positive natural pairs `(B,C)` and `(V,W)`, proportionality
`B*W = C*V` forbids their sums from differing by exactly one.  Therefore a
strict drop between the two rank-three endpoint degrees is automatically at
least two.  This is a local finite-support consequence of the already-proved
RR pencil identities; no balance relation and no new termination measure are
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Positive proportional natural pairs cannot have sums separated by exactly
one. -/
private theorem positive_cross_sum_gap_two
    {B C V W : ℕ}
    (hV : 0 < V) (hW : 0 < W)
    (hcross : B * W = C * V)
    (hsum : V + W < B + C) :
    V + W + 2 ≤ B + C := by
  by_contra hnot
  have heq : B + C = V + W + 1 := by omega
  by_cases hBV : B ≤ V
  · have hWC : W < C := by omega
    have hleft : B * W ≤ V * W := Nat.mul_le_mul_right W hBV
    have hright : V * W < C * V := by
      rw [Nat.mul_comm V W]
      exact Nat.mul_lt_mul_of_pos_right hWC hV
    omega
  · have hVB : V < B := by omega
    have hCW : C ≤ W := by omega
    have hleft : C * V ≤ W * V := Nat.mul_le_mul_right V hCW
    have hright : W * V < B * W := by
      rw [Nat.mul_comm W V]
      exact Nat.mul_lt_mul_of_pos_right hVB hW
    omega

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **A19.88 strengthened lower boundary gap.**  If the unit outside endpoint
of the genuine lower `.qs` ray is rank three on a different coordinate facet,
its ordinary degree is at least two below the original maximal top degree. -/
theorem qs_ray_rankThree_otherFacet_degree_add_two_le_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (next : ToricFacet)
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent + 2 ≤
      T.topFace.degree := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hdegLt :
      HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent <
        HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent := by
    rw [C.qs_ray_facet_degree_eq_topFace]
    exact C.qs_ray_outside_degree_lt_topFace
  have hfacetTop := C.qs_ray_facet_degree_eq_topFace
  cases next with
  | qs => exact (hne rfl).elim
  | pr =>
      have hout := (HC4.Newton.mvRankThreeOnFacet_iff .pr
        C.ray.outsideExponent).1 houtThree
      rcases hout with ⟨hout1, _hout0pos, hout2, hout3⟩
      have harith := C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree
      have hfacet1 := harith.1
      have hcross := harith.2
      have hsum :
          C.ray.outsideExponent 2 + C.ray.outsideExponent 3 <
            C.ray.facetExponent 2 + C.ray.facetExponent 3 := by
        simp only [HC4.Polynomial.ordinaryDegree4] at hdegLt
        omega
      have hgap := positive_cross_sum_gap_two hout2 hout3 hcross hsum
      rw [← hfacetTop]
      simp only [HC4.Polynomial.ordinaryDegree4]
      omega
  | sp =>
      have hout := (HC4.Newton.mvRankThreeOnFacet_iff .sp
        C.ray.outsideExponent).1 houtThree
      rcases hout with ⟨hout2, _hout0pos, hout1, hout3⟩
      have harith := C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree
      have hfacet2 := harith.1
      have hcross := harith.2
      have hsum :
          C.ray.outsideExponent 1 + C.ray.outsideExponent 3 <
            C.ray.facetExponent 1 + C.ray.facetExponent 3 := by
        simp only [HC4.Polynomial.ordinaryDegree4] at hdegLt
        omega
      have hgap := positive_cross_sum_gap_two hout1 hout3 hcross hsum
      rw [← hfacetTop]
      simp only [HC4.Polynomial.ordinaryDegree4]
      omega
  | rq =>
      have hout := (HC4.Newton.mvRankThreeOnFacet_iff .rq
        C.ray.outsideExponent).1 houtThree
      rcases hout with ⟨hout3, _hout0pos, hout1, hout2⟩
      have harith := C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree
      have hfacet3 := harith.1
      have hcross := harith.2
      have hsum :
          C.ray.outsideExponent 1 + C.ray.outsideExponent 2 <
            C.ray.facetExponent 1 + C.ray.facetExponent 2 := by
        simp only [HC4.Polynomial.ordinaryDegree4] at hdegLt
        omega
      have hgap := positive_cross_sum_gap_two hout1 hout2 hcross hsum
      rw [← hfacetTop]
      simp only [HC4.Polynomial.ordinaryDegree4]
      omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
