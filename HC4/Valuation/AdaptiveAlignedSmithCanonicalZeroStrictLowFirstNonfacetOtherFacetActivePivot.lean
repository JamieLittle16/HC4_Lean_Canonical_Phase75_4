import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetDegreeOnePencil
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# A19.118: nonzero active Schur pivots on the three other facets

The surviving lower `.qs` ray is an honest degree-one endpoint pencil.  Its
coefficient at line index `1` is literally the coefficient of the retained
outside endpoint and is therefore nonzero.

When that outside endpoint is rank three on a different coordinate facet, two
transverse coordinates remain strictly positive.  A19.R8 says the principal
Hessian minor on precisely those two coordinates has a nonzero quadratic
coefficient in the endpoint pencil.  Thus it is a genuine polynomial pivot:

* `.pr` uses coordinates `(2,3)`;
* `.sp` uses coordinates `(1,3)`;
* `.rq` uses coordinates `(1,2)`.

The final three lemmas retain the stronger information needed by the binary
Schur clock: after the canonical rank-three-line specialisation, the ordinary
ray Hessian pivot has a nonzero coefficient in longitudinal degree two.
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

/-- Coefficient polynomial of the actual unit lower ray. -/
noncomputable def qsRayDegreeOneCoefficientPolynomial
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) : Polynomial K :=
  HC4.Polynomial.rankThreeLineCoefficientPolynomial
    (C.ray.facetExponent 1)
    (C.ray.facetExponent 2)
    (C.ray.facetExponent 3)
    1
    (C.ray.outsideExponent 1)
    (C.ray.outsideExponent 2)
    (C.ray.outsideExponent 3)
    1 C.ray.face

/-- The degree-one ray's upper endpoint coefficient is literally nonzero. -/
theorem qsRayDegreeOneCoefficientPolynomial_coeff_one_ne
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    (C.qsRayDegreeOneCoefficientPolynomial).coeff 1 ≠ 0 := by
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hexp :
      HC4.Polynomial.rankThreeLineExponentFinsupp
        (C.ray.facetExponent 1)
        (C.ray.facetExponent 2)
        (C.ray.facetExponent 3)
        1
        (C.ray.outsideExponent 1)
        (C.ray.outsideExponent 2)
        (C.ray.outsideExponent 3)
        1 1 = C.ray.outsideExponent := by
    ext i
    fin_cases i <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply, hout0]
  rw [qsRayDegreeOneCoefficientPolynomial,
    HC4.Polynomial.coeff_M_rankThreeLineCoefficientPolynomial]
  rw [hexp]
  exact MvPolynomial.mem_support_iff.mp C.ray.outside_mem_face

/-- `.pr`: the `(2,3)` principal endpoint-pencil minor is nonzero. -/
theorem qs_ray_pr_endpointActiveMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.weightedRankThreeEndpointActiveMinor
      (C.ray.facetExponent 1 : K)
      (C.ray.facetExponent 2 : K)
      (C.ray.facetExponent 3 : K)
      (1 : K)
      (C.ray.outsideExponent 1 : K)
      (C.ray.outsideExponent 2 : K)
      (C.ray.outsideExponent 3 : K)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
      (2 : Fin 4) 3 ≠ 0 := by
  have hout :=
    (HC4.Newton.mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨_hout1, _hout0, hout2, hout3⟩
  exact HC4.Polynomial.weightedRankThreeEndpointActiveMinor_two_three_ne_zero
    (K := K)
    (C.ray.facetExponent 1 : K)
    (C.ray.facetExponent 2 : K)
    (C.ray.facetExponent 3 : K)
    (1 : K)
    (C.ray.outsideExponent 1 : K)
    (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
    (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
    hout2 hout3 (C.qsRayDegreeOneCoefficientPolynomial_coeff_one_ne hthree)

/-- `.sp`: the `(1,3)` principal endpoint-pencil minor is nonzero. -/
theorem qs_ray_sp_endpointActiveMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    HC4.Polynomial.weightedRankThreeEndpointActiveMinor
      (C.ray.facetExponent 1 : K)
      (C.ray.facetExponent 2 : K)
      (C.ray.facetExponent 3 : K)
      (1 : K)
      (C.ray.outsideExponent 1 : K)
      (C.ray.outsideExponent 2 : K)
      (C.ray.outsideExponent 3 : K)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
      (1 : Fin 4) 3 ≠ 0 := by
  have hout :=
    (HC4.Newton.mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨_hout2, _hout0, hout1, hout3⟩
  exact HC4.Polynomial.weightedRankThreeEndpointActiveMinor_one_three_ne_zero
    (K := K)
    (C.ray.facetExponent 1 : K)
    (C.ray.facetExponent 2 : K)
    (C.ray.facetExponent 3 : K)
    (1 : K)
    (C.ray.outsideExponent 2 : K)
    (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
    (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
    hout1 hout3 (C.qsRayDegreeOneCoefficientPolynomial_coeff_one_ne hthree)

/-- `.rq`: the `(1,2)` principal endpoint-pencil minor is nonzero. -/
theorem qs_ray_rq_endpointActiveMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    HC4.Polynomial.weightedRankThreeEndpointActiveMinor
      (C.ray.facetExponent 1 : K)
      (C.ray.facetExponent 2 : K)
      (C.ray.facetExponent 3 : K)
      (1 : K)
      (C.ray.outsideExponent 1 : K)
      (C.ray.outsideExponent 2 : K)
      (C.ray.outsideExponent 3 : K)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
      (1 : Fin 4) 2 ≠ 0 := by
  have hout :=
    (HC4.Newton.mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨_hout3, _hout0, hout1, hout2⟩
  exact HC4.Polynomial.weightedRankThreeEndpointActiveMinor_one_two_ne_zero
    (K := K)
    (C.ray.facetExponent 1 : K)
    (C.ray.facetExponent 2 : K)
    (C.ray.facetExponent 3 : K)
    (1 : K)
    (C.ray.outsideExponent 3 : K)
    (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
    (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
    hout1 hout2 (C.qsRayDegreeOneCoefficientPolynomial_coeff_one_ne hthree)

/-- `.pr`: after ordinary transverse-Hessian specialization, the quadratic
longitudinal coefficient of the actual ray pivot is nonzero. -/
theorem qs_ray_pr_hessianPrincipalMinor_specialisation_coeff_two_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (HC4.Polynomial.rankThreeLineSpecialisation
      (HC4.Polynomial.hessianPrincipalMinor C.ray.face
        (2 : Fin 4) 3)).coeff 2 ≠ 0 := by
  rw [HC4.Polynomial.rankThree_degreeOne_specialisation_hessianPrincipalMinor_of_transverse
    (C.qs_ray_degreeOne_supportedLine hthree) (2 : Fin 4) 3 (by decide) (by decide)]
  have hout :=
    (HC4.Newton.mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨_hout1, _hout0, hout2, hout3⟩
  simpa [qsRayDegreeOneCoefficientPolynomial] using
    HC4.Polynomial.coeff_two_weightedRankThreeEndpointActiveMinor_two_three_ne_zero
      (K := K)
      (C.ray.facetExponent 1 : K)
      (C.ray.facetExponent 2 : K)
      (C.ray.facetExponent 3 : K)
      (1 : K)
      (C.ray.outsideExponent 1 : K)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
      hout2 hout3 (C.qsRayDegreeOneCoefficientPolynomial_coeff_one_ne hthree)

/-- `.sp`: after ordinary transverse-Hessian specialization, the quadratic
longitudinal coefficient of the actual ray pivot is nonzero. -/
theorem qs_ray_sp_hessianPrincipalMinor_specialisation_coeff_two_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    (HC4.Polynomial.rankThreeLineSpecialisation
      (HC4.Polynomial.hessianPrincipalMinor C.ray.face
        (1 : Fin 4) 3)).coeff 2 ≠ 0 := by
  rw [HC4.Polynomial.rankThree_degreeOne_specialisation_hessianPrincipalMinor_of_transverse
    (C.qs_ray_degreeOne_supportedLine hthree) (1 : Fin 4) 3 (by decide) (by decide)]
  have hout :=
    (HC4.Newton.mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨_hout2, _hout0, hout1, hout3⟩
  simpa [qsRayDegreeOneCoefficientPolynomial] using
    HC4.Polynomial.coeff_two_weightedRankThreeEndpointActiveMinor_one_three_ne_zero
      (K := K)
      (C.ray.facetExponent 1 : K)
      (C.ray.facetExponent 2 : K)
      (C.ray.facetExponent 3 : K)
      (1 : K)
      (C.ray.outsideExponent 2 : K)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
      hout1 hout3 (C.qsRayDegreeOneCoefficientPolynomial_coeff_one_ne hthree)

/-- `.rq`: after ordinary transverse-Hessian specialization, the quadratic
longitudinal coefficient of the actual ray pivot is nonzero. -/
theorem qs_ray_rq_hessianPrincipalMinor_specialisation_coeff_two_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    (HC4.Polynomial.rankThreeLineSpecialisation
      (HC4.Polynomial.hessianPrincipalMinor C.ray.face
        (1 : Fin 4) 2)).coeff 2 ≠ 0 := by
  rw [HC4.Polynomial.rankThree_degreeOne_specialisation_hessianPrincipalMinor_of_transverse
    (C.qs_ray_degreeOne_supportedLine hthree) (1 : Fin 4) 2 (by decide) (by decide)]
  have hout :=
    (HC4.Newton.mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree
  rcases hout with ⟨_hout3, _hout0, hout1, hout2⟩
  simpa [qsRayDegreeOneCoefficientPolynomial] using
    HC4.Polynomial.coeff_two_weightedRankThreeEndpointActiveMinor_one_two_ne_zero
      (K := K)
      (C.ray.facetExponent 1 : K)
      (C.ray.facetExponent 2 : K)
      (C.ray.facetExponent 3 : K)
      (1 : K)
      (C.ray.outsideExponent 3 : K)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 0)
      (C.qsRayDegreeOneCoefficientPolynomial.coeff 1)
      hout1 hout2 (C.qsRayDegreeOneCoefficientPolynomial_coeff_one_ne hthree)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
