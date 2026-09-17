import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarContactFirstInterior
import Mathlib.Tactic

/-!
# A19 locked special fibre of the unit planar-contact Rees

The source-honest unit contact Rees is filtered by the integral contact weight
`qsIntegralContactWeight 2`.  Its zero layer is exactly the locked pair-degree
one source fibre.  This is the unit analogue of the already verified non-unit
special-fibre package; coefficients remain literal carrier coefficients.
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

namespace QsOtherFacetPrUnitLeftPlanarContactReesData

/-- The locked facet endpoint has reverse order zero in the unit contact family. -/
theorem locked_facet_reverseOrder_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    T.topFace.degree -
        Finsupp.weight (qsIntegralContactWeight 2) C.ray.facetExponent = 0 := by
  rw [D.reverseOrder_eq_quotientContactOrder]
  rw [F.locked_contactOrder, F.topFace_degree_eq hthree houtThree]
  simp

/-- The locked outside endpoint has the same zero reverse order. -/
theorem locked_outside_reverseOrder_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    T.topFace.degree -
        Finsupp.weight (qsIntegralContactWeight 2) C.ray.outsideExponent = 0 := by
  have hpair :
      qsOtherFacetPairDegree .pr C.ray.outsideExponent =
        qsOtherFacetPairDegree .pr C.ray.facetExponent := by
    simp [qsOtherFacetPairDegree,
      F.locked.outside_zero, F.locked.outside_one,
      F.locked.facet_zero, F.locked.facet_one]
  have hq := F.quotient.quotientContactOrder_eq_of_pairDegree_eq
    F.locked.outside_provenance.carrier_mem
    F.locked.facet_provenance.carrier_mem hpair
  rw [← D.reverseOrder_eq_quotientContactOrder,
    ← D.reverseOrder_eq_quotientContactOrder] at hq
  rw [D.locked_facet_reverseOrder_eq_zero hthree houtThree] at hq
  exact hq

/-- The zero unit contact layer consists exactly of the two locked source endpoints. -/
theorem zeroLayer_support_eq_locked
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (familyParameterLayer D.family 0).support =
      {C.ray.facetExponent, C.ray.outsideExponent} := by
  classical
  have hfacetOrder := D.locked_facet_reverseOrder_eq_zero hthree houtThree
  have houtOrder := D.locked_outside_reverseOrder_eq_zero hthree houtThree
  have hpairFacet :
      qsOtherFacetPairDegree .pr C.ray.facetExponent = (1 : ℤ) := by
    simp [qsOtherFacetPairDegree,
      F.locked.facet_zero, F.locked.facet_one]
  have hpairOutside :
      qsOtherFacetPairDegree .pr C.ray.outsideExponent = (1 : ℤ) := by
    simp [qsOtherFacetPairDegree,
      F.locked.outside_zero, F.locked.outside_one]
  have hqFacetOutside :
      HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent =
        HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.outsideExponent :=
    F.quotient.pair_fiber
      F.locked.facet_provenance.carrier_mem
      F.locked.outside_provenance.carrier_mem
      (hpairFacet.trans hpairOutside.symm)
  ext e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    rcases D.parameterLayer_support_source_and_order he with ⟨heP, heOrder⟩
    have hpairEq := D.pair_eq_of_reverseOrder_eq hthree houtThree
      heP F.locked.facet_provenance.carrier_mem
      (heOrder.trans hfacetOrder.symm)
    have hpairNat : e 0 + e 1 = 1 := by
      simpa [F.locked.facet_zero, F.locked.facet_one,
        QsOtherFacetPrUnitLeftPlanarContactReesData.rankThreeQuotientCoordinate] using hpairEq
    have hpairE : qsOtherFacetPairDegree .pr e = (1 : ℤ) := by
      have hcast := congrArg (fun m : ℕ => (m : ℤ)) hpairNat
      simpa [qsOtherFacetPairDegree] using hcast
    have hqEF :
        HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e =
          HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent :=
      F.quotient.pair_fiber heP F.locked.facet_provenance.carrier_mem
        (hpairE.trans hpairFacet.symm)
    have he0 : e 0 = 0 ∨ e 0 = 1 := by omega
    rcases he0 with he0 | he0
    · left
      exact HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
        1 1 e C.ray.facetExponent hqEF (by
          rw [he0, F.locked.facet_zero])
    · right
      exact HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
        1 1 e C.ray.outsideExponent (hqEF.trans hqFacetOutside) (by
          rw [he0, F.locked.outside_zero])
  · intro he
    rcases he with rfl | rfl
    · apply MvPolynomial.mem_support_iff.mpr
      change MvPolynomial.coeff C.ray.facetExponent
          (familyParameterLayer
            (reverseWeightedReesFamily
              (qsIntegralContactWeight 2) T.topFace.degree
              P.carrier D.bound) 0) ≠ 0
      rw [reverseWeightedReesFamily_parameterLayer_coeff]
      simp [F.locked.facet_provenance.carrier_mem, hfacetOrder,
        F.locked.facet_provenance.carrier_coeff_ne]
    · apply MvPolynomial.mem_support_iff.mpr
      change MvPolynomial.coeff C.ray.outsideExponent
          (familyParameterLayer
            (reverseWeightedReesFamily
              (qsIntegralContactWeight 2) T.topFace.degree
              P.carrier D.bound) 0) ≠ 0
      rw [reverseWeightedReesFamily_parameterLayer_coeff]
      simp [F.locked.outside_provenance.carrier_mem, houtOrder,
        F.locked.outside_provenance.carrier_coeff_ne]

/-- Coefficients on the zero layer are literal carrier coefficients. -/
theorem zeroLayer_locked_coefficients
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    MvPolynomial.coeff C.ray.facetExponent
        (familyParameterLayer D.family 0) =
        MvPolynomial.coeff C.ray.facetExponent P.carrier ∧
      MvPolynomial.coeff C.ray.outsideExponent
        (familyParameterLayer D.family 0) =
        MvPolynomial.coeff C.ray.outsideExponent P.carrier := by
  have hfacetOrder := D.locked_facet_reverseOrder_eq_zero hthree houtThree
  have houtOrder := D.locked_outside_reverseOrder_eq_zero hthree houtThree
  constructor
  · change MvPolynomial.coeff C.ray.facetExponent
        (familyParameterLayer
          (reverseWeightedReesFamily
            (qsIntegralContactWeight 2) T.topFace.degree
            P.carrier D.bound) 0) = _
    rw [reverseWeightedReesFamily_parameterLayer_coeff]
    simp [F.locked.facet_provenance.carrier_mem, hfacetOrder]
  · change MvPolynomial.coeff C.ray.outsideExponent
        (familyParameterLayer
          (reverseWeightedReesFamily
            (qsIntegralContactWeight 2) T.topFace.degree
            P.carrier D.bound) 0) = _
    rw [reverseWeightedReesFamily_parameterLayer_coeff]
    simp [F.locked.outside_provenance.carrier_mem, houtOrder]

/-- The singular unit planar contact family starts at the literal locked pair. -/
theorem specialFiber_eq_locked_pair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    polynomialFamilySpecialFiber D.family =
      MvPolynomial.monomial C.ray.facetExponent
        (MvPolynomial.coeff C.ray.facetExponent P.carrier) +
      MvPolynomial.monomial C.ray.outsideExponent
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier) := by
  classical
  have hzero := polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
    (K := K) (qsIntegralContactWeight 2) T.topFace.degree P.carrier D.bound
  change polynomialFamilySpecialFiber D.family = familyParameterLayer D.family 0 at hzero
  rw [hzero]
  let L := familyParameterLayer D.family 0
  have hsupp : L.support =
      {C.ray.facetExponent, C.ray.outsideExponent} := by
    dsimp [L]
    exact D.zeroLayer_support_eq_locked hthree houtThree
  have hcoeff := D.zeroLayer_locked_coefficients hthree houtThree
  have hne : C.ray.facetExponent ≠ C.ray.outsideExponent := by
    intro h
    have h0 : C.ray.facetExponent 0 = C.ray.outsideExponent 0 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    rw [F.locked.facet_zero, F.locked.outside_zero] at h0
    omega
  have hsum := MvPolynomial.as_sum L
  rw [hsupp] at hsum
  dsimp [L] at hsum ⊢
  calc
    familyParameterLayer D.family 0 =
        ∑ v ∈ {C.ray.facetExponent, C.ray.outsideExponent},
          MvPolynomial.monomial v
            (MvPolynomial.coeff v (familyParameterLayer D.family 0)) := hsum
    _ = MvPolynomial.monomial C.ray.facetExponent
          (MvPolynomial.coeff C.ray.facetExponent P.carrier) +
        MvPolynomial.monomial C.ray.outsideExponent
          (MvPolynomial.coeff C.ray.outsideExponent P.carrier) := by
      simp [Finset.sum_insert, hne, Ne.symm hne, hcoeff.1, hcoeff.2]

end QsOtherFacetPrUnitLeftPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
