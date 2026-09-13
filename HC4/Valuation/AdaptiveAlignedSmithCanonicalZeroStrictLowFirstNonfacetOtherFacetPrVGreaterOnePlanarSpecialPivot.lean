import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarSpecialFiber
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# A19 active pivot on the locked planar-contact special fibre

The zero layer of the singular planar-contact Rees is the literal locked
facet/outside pair.  Hence it is an honest rank-three segment of length one.
The generic endpoint active-minor theorem applies directly: in the `.pr`
orientation the outside endpoint has strictly positive coordinates `2` and
`3`, and its literal carrier coefficient is nonzero.

Thus the `(2,3)` Hessian principal minor of the special fibre is nonzero.  This
is the denominator-free active pivot needed for first-layer Schur
linearisation.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The locked special fibre is supported on its literal length-one
rank-three endpoint segment. -/
theorem specialFiber_supportedRankThreeLine
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.IsSupportedOnRankThreeLine
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1
      (polynomialFamilySpecialFiber D.family) := by
  intro d hd
  have hzero := polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
    (K := K) (qsIntegralContactWeight (F.V + 1)) T.topFace.degree
    P.carrier D.bound
  change polynomialFamilySpecialFiber D.family = familyParameterLayer D.family 0 at hzero
  have hd0 : d ∈ (familyParameterLayer D.family 0).support := by
    rw [← hzero]
    exact hd
  have hsupp := D.zeroLayer_support_eq_locked hthree houtThree
  rw [hsupp] at hd0
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd0
  rcases hd0 with hfacet | hout
  · refine ⟨0, by decide, ?_⟩
    rw [hfacet]
    ext i
    fin_cases i <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply,
        F.locked.facet_zero]
  · refine ⟨1, by decide, ?_⟩
    rw [hout]
    ext i
    fin_cases i <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply,
        F.locked.outside_zero]

/-- The coefficient at the outside endpoint of the extracted degree-one line
polynomial is the literal nonzero carrier coefficient. -/
theorem specialFiber_lineCoefficient_one_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (HC4.Polynomial.rankThreeLineCoefficientPolynomial
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1
      (polynomialFamilySpecialFiber D.family)).coeff 1 ≠ 0 := by
  rw [HC4.Polynomial.coeff_M_rankThreeLineCoefficientPolynomial]
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
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply,
        F.locked.outside_zero]
  rw [hexp]
  have hzero := polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
    (K := K) (qsIntegralContactWeight (F.V + 1)) T.topFace.degree
    P.carrier D.bound
  change polynomialFamilySpecialFiber D.family = familyParameterLayer D.family 0 at hzero
  rw [hzero]
  rw [(D.zeroLayer_locked_coefficients hthree houtThree).2]
  exact F.locked.outside_provenance.carrier_coeff_ne

/-- **Active locked pivot.**  The `(2,3)` principal Hessian minor of the
planar-contact special fibre is nonzero. -/
theorem specialFiber_hessianPrincipalMinor_two_three_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber D.family) (2 : Fin 4) 3 ≠ 0 := by
  let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
    (C.ray.facetExponent 1)
    (C.ray.facetExponent 2)
    (C.ray.facetExponent 3)
    1
    (C.ray.outsideExponent 1)
    (C.ray.outsideExponent 2)
    (C.ray.outsideExponent 3)
    1
    (polynomialFamilySpecialFiber D.family)
  have hout2 : 0 < C.ray.outsideExponent 2 := by
    rw [F.locked.outside_two]
    exact F.locked.ell_pos
  have hout3 : 0 < C.ray.outsideExponent 3 := by
    rw [F.locked.outside_three]
    exact Nat.mul_pos F.locked.ell_pos (by omega : 0 < F.V)
  apply HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_endpointActiveMinor_ne_zero
    (K := K)
    (D.specialFiber_supportedRankThreeLine hthree houtThree)
    (2 : Fin 4) 3
  dsimp only [phi]
  exact HC4.Polynomial.weightedRankThreeEndpointActiveMinor_two_three_ne_zero
    (K := K)
    (C.ray.facetExponent 1 : K)
    (C.ray.facetExponent 2 : K)
    (C.ray.facetExponent 3 : K)
    (1 : K)
    (C.ray.outsideExponent 1 : K)
    (HC4.Polynomial.rankThreeLineCoefficientPolynomial
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1
      (polynomialFamilySpecialFiber D.family)).coeff 0
    (HC4.Polynomial.rankThreeLineCoefficientPolynomial
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1
      (polynomialFamilySpecialFiber D.family)).coeff 1
    hout2 hout3
    (D.specialFiber_lineCoefficient_one_ne_zero hthree houtThree)

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
