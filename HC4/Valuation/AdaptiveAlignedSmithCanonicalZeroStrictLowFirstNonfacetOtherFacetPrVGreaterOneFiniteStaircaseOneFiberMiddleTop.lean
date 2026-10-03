import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberDegree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorAffineRealisation
import Mathlib.Tactic

/-!
# A19 middle one-fibre top source monomial

On the sole surviving one-fibre diagonal `j+1=k`, the common honest profile
has ordinary degree `k-1` or `k`.  Its leading coefficient is nonzero, and the
contact-side affine realisation therefore produces an actual source-carrier
monomial with longitudinal coordinate equal to that degree.

The affine staircase equations identify the two possible top source exponents:

* degree `k-1`: `(k-1, 1, 1, V*k)`;
* degree `k`:   `(k,   0, 0, V*(k-1))`.

No determinant argument occurs here.
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

/-- On the middle diagonal, the honest source profile has one of the two
adjacent degrees. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_middle_degree_dichotomy
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 1 = Alo.k) :
    Alo.coefficientProfile.natDegree = Alo.k - 1 ∨
      Alo.coefficientProfile.natDegree = Alo.k := by
  exact (F.oneFiber_commonProfile_degree_pairs
    Alo Ahi hthree houtThree hext).1

private theorem top_profile_coefficient_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {m : ℕ} (hdeg : Alo.coefficientProfile.natDegree = m) :
    Alo.coefficientProfile.coeff m ≠ 0 := by
  have hlead : Alo.coefficientProfile.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr Alo.coefficientProfile_ne_zero
  simpa [Polynomial.leadingCoeff, hdeg] using hlead

/-- A nonzero profile coefficient is realised by an actual carrier monomial
with the same longitudinal coordinate. -/
theorem QsOtherFacetPrLeftVFirstInteriorAffineLayerData.exists_carrierExponent_of_profile_coeff_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {m : ℕ} (hm : Alo.coefficientProfile.coeff m ≠ 0) :
    ∃ e ∈ P.carrier.support,
      e 0 = m ∧
      e 0 + e 1 = Alo.k ∧
      e 0 + e 2 = Alo.j + 1 ∧
      F.V * e 0 + e 3 = F.V * (Alo.k + Alo.j) := by
  have hmSupp : m ∈ Alo.coefficientProfile.support :=
    Polynomial.mem_support_iff.mpr hm
  rcases Alo.exists_layerExponent_of_coefficientProfile_mem hmSupp with
    ⟨e, heLayer, he0⟩
  have hcoords := Alo.coordinates e heLayer
  have hcoeffLayer :
      MvPolynomial.coeff e
        (familyParameterLayer Dlo.family
          (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp heLayer
  have hcoeffCarrier := Alo.coefficient_eq_carrier e heLayer
  have heCarrier : e ∈ P.carrier.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [← hcoeffCarrier]
    exact hcoeffLayer
  exact ⟨e, heCarrier, he0, hcoords.1, hcoords.2.1, hcoords.2.2⟩

/-- Middle lower-degree branch: an actual source monomial has exponent
coordinates `(k-1,1,1,V*k)`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.exists_middleLower_top_carrierExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (hdiag : Alo.j + 1 = Alo.k)
    (hdeg : Alo.coefficientProfile.natDegree = Alo.k - 1) :
    ∃ e ∈ P.carrier.support,
      e 0 = Alo.k - 1 ∧ e 1 = 1 ∧ e 2 = 1 ∧
      e 3 = F.V * Alo.k := by
  have hm := top_profile_coefficient_ne_zero Alo hdeg
  rcases Alo.exists_carrierExponent_of_profile_coeff_ne_zero hm with
    ⟨e, he, he0, hePair, heFirst, heThird⟩
  refine ⟨e, he, he0, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hsum : F.V * (Alo.k - 1) + e 3 =
        F.V * (Alo.k + (Alo.k - 1)) := by
      rw [← he0]
      have hj : Alo.j = Alo.k - 1 := by omega
      simpa [hj] using heThird
    omega

/-- Middle upper-degree branch: an actual source monomial is the central
singleton exponent `(k,0,0,V*(k-1))`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.exists_middleUpper_central_carrierExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (hdiag : Alo.j + 1 = Alo.k)
    (hdeg : Alo.coefficientProfile.natDegree = Alo.k) :
    ∃ e ∈ P.carrier.support,
      e 0 = Alo.k ∧ e 1 = 0 ∧ e 2 = 0 ∧
      e 3 = F.V * (Alo.k - 1) := by
  have hm := top_profile_coefficient_ne_zero Alo hdeg
  rcases Alo.exists_carrierExponent_of_profile_coeff_ne_zero hm with
    ⟨e, he, he0, hePair, heFirst, heThird⟩
  refine ⟨e, he, he0, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hj : Alo.j = Alo.k - 1 := by omega
    rw [he0, hj] at heThird
    omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
