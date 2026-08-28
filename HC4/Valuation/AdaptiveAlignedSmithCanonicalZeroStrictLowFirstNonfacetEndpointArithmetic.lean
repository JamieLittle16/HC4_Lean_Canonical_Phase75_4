import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetDegreeOnePencil
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsBoundaryClosure
import HC4.Polynomial.RankThreeWeightedFirstZeroPencil
import HC4.Polynomial.RankThreeWeightedBoundaryPencils
import Mathlib.Tactic

/-!
# A19.81: balance-free arithmetic of the lower degree-one boundary endpoint

A19.79 turns the genuine lower `.qs` first-contact ray into an honest
coefficient-weighted degree-one endpoint pencil.  A19.76 says its retained
outside endpoint is either codimension two or rank three on a coordinate facet
different from `.qs`.

In the rank-three case the endpoint has exactly one transverse zero.  The
three cyclic weighted-pencil identities then force the corresponding positive
base exponent to be `1` and give an exact cross-product relation between the
other two transverse coordinates.  This file records those three possibilities
without adding a torus balance relation and without yet asserting that the
resulting arithmetic package is contradictory.
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

private theorem qs_ray_degreeOne_endpointCoefficients_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1 C.ray.face
    phi.coeff 0 ≠ 0 ∧ phi.coeff 1 ≠ 0 := by
  let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
    (C.ray.facetExponent 1)
    (C.ray.facetExponent 2)
    (C.ray.facetExponent 3)
    1
    (C.ray.outsideExponent 1)
    (C.ray.outsideExponent 2)
    (C.ray.outsideExponent 3)
    1 C.ray.face
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray.facet_coordinate_zero
  have hstartExp :
      HC4.Polynomial.rankThreeLineExponentFinsupp
        (C.ray.facetExponent 1)
        (C.ray.facetExponent 2)
        (C.ray.facetExponent 3)
        1
        (C.ray.outsideExponent 1)
        (C.ray.outsideExponent 2)
        (C.ray.outsideExponent 3)
        1 0 = C.ray.facetExponent := by
    ext k
    fin_cases k <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply, hfacet0]
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hendExp :
      HC4.Polynomial.rankThreeLineExponentFinsupp
        (C.ray.facetExponent 1)
        (C.ray.facetExponent 2)
        (C.ray.facetExponent 3)
        1
        (C.ray.outsideExponent 1)
        (C.ray.outsideExponent 2)
        (C.ray.outsideExponent 3)
        1 1 = C.ray.outsideExponent := by
    ext k
    fin_cases k <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply, hout0]
  constructor
  · dsimp [phi]
    rw [HC4.Polynomial.coeff_zero_rankThreeLineCoefficientPolynomial,
      hstartExp]
    exact MvPolynomial.mem_support_iff.mp C.ray.facet_mem_face
  · dsimp [phi]
    rw [HC4.Polynomial.coeff_M_rankThreeLineCoefficientPolynomial,
      hendExp]
    exact MvPolynomial.mem_support_iff.mp C.ray.outside_mem_face

/-- If the lower outside endpoint is rank three on `.pr` (coordinate `1`
zero), singularity forces the first base exponent to be `1` and the remaining
endpoint coordinates satisfy the cyclic cross-product relation. -/
theorem qs_ray_pr_outside_base_eq_one_and_cross
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    C.ray.facetExponent 1 = 1 ∧
      C.ray.facetExponent 2 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 2 := by
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hA : 0 < C.ray.facetExponent 1 := hbase.2.1
  have hout := (HC4.Newton.mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1
    houtThree
  rcases hout with ⟨hU0, _hout0, hV, hW⟩
  let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
    (C.ray.facetExponent 1)
    (C.ray.facetExponent 2)
    (C.ray.facetExponent 3)
    1
    (C.ray.outsideExponent 1)
    (C.ray.outsideExponent 2)
    (C.ray.outsideExponent 3)
    1 C.ray.face
  have hcoeff := C.qs_ray_degreeOne_endpointCoefficients_ne_zero hthree
  have hc0 : phi.coeff 0 ≠ 0 := by simpa [phi] using hcoeff.1
  have hc1 : phi.coeff 1 ≠ 0 := by simpa [phi] using hcoeff.2
  have hpencil :
      (HC4.Polynomial.weightedRankThreeEndpointPencil
        ((C.ray.facetExponent 1 : ℕ) : K)
        ((C.ray.facetExponent 2 : ℕ) : K)
        ((C.ray.facetExponent 3 : ℕ) : K)
        (1 : K)
        ((C.ray.outsideExponent 1 : ℕ) : K)
        ((C.ray.outsideExponent 2 : ℕ) : K)
        ((C.ray.outsideExponent 3 : ℕ) : K)
        (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using C.qs_ray_degreeOne_endpointPencil_det_zero hthree
  exact HC4.Polynomial.firstZero_weightedPencil_base_eq_one_and_cross
    hA hV hW hc0 hc1 (by simpa [hU0] using hpencil)

/-- If the lower outside endpoint is rank three on `.sp` (coordinate `2`
zero), singularity forces the second base exponent to be `1`. -/
theorem qs_ray_sp_outside_base_eq_one_and_cross
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    C.ray.facetExponent 2 = 1 ∧
      C.ray.facetExponent 1 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 1 := by
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hB : 0 < C.ray.facetExponent 2 := hbase.2.2.1
  have hout := (HC4.Newton.mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1
    houtThree
  rcases hout with ⟨hV0, _hout0, hU, hW⟩
  let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
    (C.ray.facetExponent 1)
    (C.ray.facetExponent 2)
    (C.ray.facetExponent 3)
    1
    (C.ray.outsideExponent 1)
    (C.ray.outsideExponent 2)
    (C.ray.outsideExponent 3)
    1 C.ray.face
  have hcoeff := C.qs_ray_degreeOne_endpointCoefficients_ne_zero hthree
  have hc0 : phi.coeff 0 ≠ 0 := by simpa [phi] using hcoeff.1
  have hc1 : phi.coeff 1 ≠ 0 := by simpa [phi] using hcoeff.2
  have hpencil :
      (HC4.Polynomial.weightedRankThreeEndpointPencil
        ((C.ray.facetExponent 1 : ℕ) : K)
        ((C.ray.facetExponent 2 : ℕ) : K)
        ((C.ray.facetExponent 3 : ℕ) : K)
        (1 : K)
        ((C.ray.outsideExponent 1 : ℕ) : K)
        ((C.ray.outsideExponent 2 : ℕ) : K)
        ((C.ray.outsideExponent 3 : ℕ) : K)
        (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using C.qs_ray_degreeOne_endpointPencil_det_zero hthree
  exact HC4.Polynomial.thirdZero_weightedPencil_base_eq_one_and_cross
    hB hU hW hc0 hc1 (by simpa [hV0] using hpencil)

/-- If the lower outside endpoint is rank three on `.rq` (coordinate `3`
zero), singularity forces the third base exponent to be `1`. -/
theorem qs_ray_rq_outside_base_eq_one_and_cross
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    C.ray.facetExponent 3 = 1 ∧
      C.ray.facetExponent 1 * C.ray.outsideExponent 2 =
        C.ray.facetExponent 2 * C.ray.outsideExponent 1 := by
  have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hC : 0 < C.ray.facetExponent 3 := hbase.2.2.2
  have hout := (HC4.Newton.mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1
    houtThree
  rcases hout with ⟨hW0, _hout0, hU, hV⟩
  let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
    (C.ray.facetExponent 1)
    (C.ray.facetExponent 2)
    (C.ray.facetExponent 3)
    1
    (C.ray.outsideExponent 1)
    (C.ray.outsideExponent 2)
    (C.ray.outsideExponent 3)
    1 C.ray.face
  have hcoeff := C.qs_ray_degreeOne_endpointCoefficients_ne_zero hthree
  have hc0 : phi.coeff 0 ≠ 0 := by simpa [phi] using hcoeff.1
  have hc1 : phi.coeff 1 ≠ 0 := by simpa [phi] using hcoeff.2
  have hpencil :
      (HC4.Polynomial.weightedRankThreeEndpointPencil
        ((C.ray.facetExponent 1 : ℕ) : K)
        ((C.ray.facetExponent 2 : ℕ) : K)
        ((C.ray.facetExponent 3 : ℕ) : K)
        (1 : K)
        ((C.ray.outsideExponent 1 : ℕ) : K)
        ((C.ray.outsideExponent 2 : ℕ) : K)
        ((C.ray.outsideExponent 3 : ℕ) : K)
        (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using C.qs_ray_degreeOne_endpointPencil_det_zero hthree
  exact HC4.Polynomial.fourthZero_weightedPencil_base_eq_one_and_cross
    hC hU hV hc0 hc1 (by simpa [hW0] using hpencil)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
