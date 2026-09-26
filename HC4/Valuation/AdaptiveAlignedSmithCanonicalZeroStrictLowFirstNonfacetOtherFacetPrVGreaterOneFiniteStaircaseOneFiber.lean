import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseDualExtrema
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorAffineRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInteriorMomentRealisation
import Mathlib.Tactic

/-!
# A19 coincident extremal fibres are literally the same source layer

If the contact-side least surviving interior pair degree and the pair-Rees
highest surviving interior pair degree coincide, the two auxiliary Rees
families have selected the same source-carrier quotient fibre.

This file proves that statement literally at the parameter-layer level.  Since
both selected layers retain the original carrier coefficients, their
multivariate layer polynomials agree, their staircase heights agree, and the
two extracted one-variable coefficient profiles agree.

This is the exact source-honest coupling needed before applying both endpoint
first-variation equations to a single interior profile.
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

namespace QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- The selected contact-side layer is exactly the carrier fibre of pair degree
`A.k`. -/
theorem firstPositiveLayer_support_eq_pairFiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support =
      P.carrier.support.filter fun e =>
        (rankThreeQuotientCoordinate 1 F.V e).pair = A.k := by
  classical
  let q := firstPositiveActualParameterOrder D.family D.hasPositiveLayer
  let L := familyParameterLayer D.family q
  have hLne : L ≠ 0 := by
    dsimp [L, q]
    exact firstPositiveActualParameterLayer_ne_zero D.family D.hasPositiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨a, ha⟩
  have ha' : a ∈ (familyParameterLayer D.family q).support := by
    simpa [L] using ha
  rcases D.parameterLayer_support_source_and_order (by simpa [q] using ha') with
    ⟨haP, haOrder⟩
  have haPairNat : a 0 + a 1 = A.k :=
    (A.coordinates a (by simpa [q] using ha')).1
  ext e
  constructor
  · intro he
    have he' : e ∈ (familyParameterLayer D.family q).support := by
      simpa [q] using he
    rcases D.parameterLayer_support_source_and_order (by simpa [q] using he') with
      ⟨heP, _heOrder⟩
    have hePairNat : e 0 + e 1 = A.k := (A.coordinates e (by simpa [q] using he')).1
    exact Finset.mem_filter.mpr ⟨heP, by
      simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hePairNat⟩
  · intro he
    rcases Finset.mem_filter.mp he with ⟨heP, hePair⟩
    have hqeq := F.support_quotient_eq_of_pair_eq haP heP
      (by
        have haPair :
            (rankThreeQuotientCoordinate 1 F.V a).pair = A.k := by
          simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using haPairNat
        exact haPair.trans hePair.symm)
    have hcontact :
        qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V e =
          qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V a := by
      unfold qsOtherFacetPrQuotientContactOrder
      rw [hqeq]
    have heOrder :
        T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e = q := by
      calc
        T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e =
          qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V e :=
            D.reverseOrder_eq_quotientContactOrder hthree houtThree e
        _ = qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V a := hcontact
        _ = T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight (F.V + 1)) a :=
              (D.reverseOrder_eq_quotientContactOrder hthree houtThree a).symm
        _ = q := by simpa [q] using haOrder
    have hm := D.parameterLayer_mem_of_carrier_mem heP
    rw [heOrder] at hm
    simpa [q] using hm

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

namespace QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- The selected pair-Rees layer is exactly the carrier fibre of pair degree
`A.k`. -/
theorem firstPositiveLayer_support_eq_pairFiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support =
      P.carrier.support.filter fun e =>
        (rankThreeQuotientCoordinate 1 F.V e).pair = A.k := by
  classical
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have hLne : familyParameterLayer D.family q ≠ 0 := by
    dsimp [q]
    exact firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨a, ha⟩
  have haFilter :
      a ∈ P.carrier.support ∧ F.highest.n - (a 0 + a 1) = q := by
    have hs := D.parameterLayer_support q
    rw [hs] at ha
    exact Finset.mem_filter.mp ha
  have haPairNat : a 0 + a 1 = A.k :=
    (A.coordinates a (by simpa [q] using ha)).1
  have hq : F.highest.n - A.k = q := by
    rw [← haPairNat]
    exact haFilter.2
  have hAkN : A.k ≤ F.highest.n := by omega

  rw [D.parameterLayer_support q]
  ext e
  simp only [Finset.mem_filter]
  constructor
  · intro he
    refine ⟨he.1, ?_⟩
    have heN : e 0 + e 1 ≤ F.highest.n := by
      rcases F.support_staircase_classification hthree houtThree he.1 with
        ⟨_j, _hj, hk, _hjle, _hzero, _hlocked⟩
      simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hk
    have hePair : e 0 + e 1 = A.k := by
      omega
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hePair
  · intro he
    refine ⟨he.1, ?_⟩
    have hePairNat : e 0 + e 1 = A.k := by
      simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using he.2
    rw [hePairNat, hq]

end QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- Coincident extremal pair degrees force the two selected parameter layers
to be literally equal as multivariate polynomials. -/
theorem QsOtherFacetPrLeftVContactFrontierData.selectedInteriorLayers_eq_of_k_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
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
    (hext : Alo.k = Ahi.k) :
    familyParameterLayer Dlo.family
        (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer) =
      familyParameterLayer Dhi.family
        (firstPositiveActualParameterOrder Dhi.family Dhi.positiveLayer) := by
  let Llo := familyParameterLayer Dlo.family
    (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer)
  let Lhi := familyParameterLayer Dhi.family
    (firstPositiveActualParameterOrder Dhi.family Dhi.positiveLayer)
  have hsupp : Llo.support = Lhi.support := by
    dsimp [Llo, Lhi]
    rw [Alo.firstPositiveLayer_support_eq_pairFiber hthree houtThree,
      Ahi.firstPositiveLayer_support_eq_pairFiber hthree houtThree,
      hext]
  apply MvPolynomial.ext
  intro e
  by_cases he : e ∈ Llo.support
  · have hehi : e ∈ Lhi.support := by
      rw [← hsupp]
      exact he
    have hlo := Alo.coefficient_eq_carrier (by simpa [Llo] using he)
    have hhi := Ahi.coefficient_eq_carrier (by simpa [Lhi] using hehi)
    simpa [Llo, Lhi] using hlo.trans hhi.symm
  · have hehi : e ∉ Lhi.support := by
      intro h
      apply he
      rw [hsupp]
      exact h
    have hlo : MvPolynomial.coeff e Llo = 0 :=
      MvPolynomial.notMem_support_iff.mp he
    have hhi : MvPolynomial.coeff e Lhi = 0 :=
      MvPolynomial.notMem_support_iff.mp hehi
    simpa [Llo, Lhi] using hlo.trans hhi.symm

/-- Coincident extremal pair degrees also force the two staircase heights to
agree. -/
theorem QsOtherFacetPrLeftVContactFrontierData.selectedInterior_j_eq_of_k_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
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
    (hext : Alo.k = Ahi.k) :
    Alo.j = Ahi.j := by
  have hL := F.selectedInteriorLayers_eq_of_k_eq
    Alo Ahi hthree houtThree hext
  let Llo := familyParameterLayer Dlo.family
    (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer)
  let Lhi := familyParameterLayer Dhi.family
    (firstPositiveActualParameterOrder Dhi.family Dhi.positiveLayer)
  have hLne : Llo ≠ 0 := by
    dsimp [Llo]
    exact firstPositiveActualParameterLayer_ne_zero Dlo.family Dlo.hasPositiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨e, he⟩
  have hehi : e ∈ Lhi.support := by
    have hsupp := congrArg MvPolynomial.support hL
    rw [← hsupp]
    exact he
  have hlo := (Alo.coordinates e (by simpa [Llo] using he)).2.1
  have hhi := (Ahi.coordinates e (by simpa [Lhi] using hehi)).2.1
  omega

/-- Most importantly, coincident extremal fibres give the same honest
one-variable source coefficient profile. -/
theorem QsOtherFacetPrLeftVContactFrontierData.selectedInteriorProfiles_eq_of_k_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
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
    (hext : Alo.k = Ahi.k) :
    Alo.coefficientProfile = Ahi.coefficientProfile := by
  have hL := F.selectedInteriorLayers_eq_of_k_eq
    Alo Ahi hthree houtThree hext
  change
    (∑ e ∈ (familyParameterLayer Dlo.family
      (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer)).support,
      Polynomial.monomial (e 0)
        (MvPolynomial.coeff e (familyParameterLayer Dlo.family
          (firstPositiveActualParameterOrder Dlo.family Dlo.hasPositiveLayer)))) =
    (∑ e ∈ (familyParameterLayer Dhi.family
      (firstPositiveActualParameterOrder Dhi.family Dhi.positiveLayer)).support,
      Polynomial.monomial (e 0)
        (MvPolynomial.coeff e (familyParameterLayer Dhi.family
          (firstPositiveActualParameterOrder Dhi.family Dhi.positiveLayer))))
  rw [hL]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
