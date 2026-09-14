import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactRees
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import HC4.Polynomial.RankThreeQuotientFibers
import Mathlib.Tactic

/-!
# A19 first positive planar-contact staircase layer

For the singular reverse Rees of the planar carrier, exact parameter order is
the honest quotient-contact deficit.  The staircase interpolation identity
then shows that parameter order determines pair degree injectively.  Hence the
least positive actual parameter layer is supported on one fixed pair-degree
quotient fibre.

If any strict-interior carrier point exists, its positive contact order is
strictly smaller than the highest primitive order.  Minimality therefore puts
the first positive layer strictly before the highest pair degree.
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

/-- The natural reverse-Rees order on `P.carrier` is exactly the previously
proved honest quotient-contact order. -/
theorem reverseOrder_eq_quotientContactOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (e : Fin 4 →₀ ℕ) :
    T.topFace.degree -
        Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e =
      qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V e := by
  have hgap := F.quotient.contactGap_eq_sum R hthree houtThree
  have h := F.quotient.sourceContactDeficit_eq_quotientContactOrder
    R hthree houtThree e
  rw [hgap] at h
  rw [qsIntegralContactWeight_finsupp]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Any monomial of an exact planar-contact parameter layer is an actual
carrier monomial with reverse order equal to that layer index. -/
theorem parameterLayer_support_source_and_order
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    {q : ℕ} {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family q).support) :
    e ∈ P.carrier.support ∧
      T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e = q := by
  have hc := MvPolynomial.mem_support_iff.mp he
  have hformula := reverseWeightedReesFamily_parameterLayer_coeff
    (K := K) (qsIntegralContactWeight (F.V + 1))
    T.topFace.degree q P.carrier D.bound e
  change MvPolynomial.coeff e (familyParameterLayer D.family q) = _ at hformula
  by_cases hcond :
      e ∈ P.carrier.support ∧
        T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e = q
  · exact hcond
  · simp only [if_neg hcond] at hformula
    exact (hc hformula).elim

/-- Equal exact parameter order on two actual staircase monomials forces equal
pair degree. -/
theorem pair_eq_of_reverseOrder_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (horder :
      T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e =
        T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight (F.V + 1)) f) :
    (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair =
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V f).pair := by
  have heq := F.contactOrder_interpolation hthree houtThree he
  have hfq := F.contactOrder_interpolation hthree houtThree hf
  rw [← D.reverseOrder_eq_quotientContactOrder hthree houtThree e] at heq
  rw [← D.reverseOrder_eq_quotientContactOrder hthree houtThree f] at hfq
  rw [horder] at heq
  have hBpos :
      0 < (F.V + 1) * (F.locked.ell + 1 - F.highest.n) := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    exact Nat.mul_pos (by omega) (by omega)
  have hmul :
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair - 1) =
        (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V f).pair - 1) := by
    rw [← heq, ← hfq]
  have hsub :
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair - 1 =
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V f).pair - 1 :=
    Nat.mul_left_cancel hBpos hmul
  have hepos := F.support_pair_pos hthree houtThree he
  have hfpos := F.support_pair_pos hthree houtThree hf
  omega

/-- The least positive planar-contact layer is supported in one fixed
pair-degree quotient fibre. -/
theorem firstPositiveLayer_pair_fiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support)
    (hf : f ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair =
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V f).pair := by
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, heq⟩
  rcases D.parameterLayer_support_source_and_order hf with ⟨hfP, hfq⟩
  exact D.pair_eq_of_reverseOrder_eq hthree houtThree heP hfP
    (heq.trans hfq.symm)

/-- Every monomial on the first positive layer has pair degree strictly bigger
than one. -/
theorem firstPositiveLayer_pair_gt_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    1 < (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair := by
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, heq⟩
  have hinterp := F.contactOrder_interpolation hthree houtThree heP
  rw [← D.reverseOrder_eq_quotientContactOrder hthree houtThree e, heq] at hinterp
  have hqpos := firstPositiveActualParameterOrder_pos D.family D.hasPositiveLayer
  have hn2 := F.highest.n_two_le
  have hnpos : 0 < F.highest.n - 1 := by omega
  have hkpos := F.support_pair_pos hthree houtThree heP
  by_contra hnot
  have hk1 : (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair = 1 := by
    omega
  rw [hk1] at hinterp
  have hinterp0 :
      (F.highest.n - 1) *
          firstPositiveActualParameterOrder D.family D.hasPositiveLayer = 0 := by
    simpa only [Nat.sub_self, Nat.mul_zero] using hinterp
  exact (Nat.ne_of_gt (Nat.mul_pos hnpos hqpos)) hinterp0

/-- A strict-interior carrier point has parameter order strictly below the
highest primitive pair. -/
theorem reverseOrder_lt_highest_of_pair_lt_highest
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    (hklt : (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair <
      F.highest.n) :
    T.topFace.degree -
        Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e <
      D.highestOrder := by
  have hinterp := F.contactOrder_interpolation hthree houtThree he
  rw [← D.reverseOrder_eq_quotientContactOrder hthree houtThree e] at hinterp
  have hBpos :
      0 < (F.V + 1) * (F.locked.ell + 1 - F.highest.n) := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    exact Nat.mul_pos (by omega) (by omega)
  have hkpos := F.support_pair_pos hthree houtThree he
  have hn2 := F.highest.n_two_le
  have hn1pos : 0 < F.highest.n - 1 := by omega
  unfold highestOrder
  have htarget :
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair - 1 <
        F.highest.n - 1 := by
    omega
  have hBmulLt := Nat.mul_lt_mul_of_pos_left htarget hBpos
  have hscaledLt :
      (F.highest.n - 1) *
          (T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e) <
        (F.highest.n - 1) *
          ((F.V + 1) * (F.locked.ell + 1 - F.highest.n)) := by
    calc
      (F.highest.n - 1) *
          (T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e) =
        (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair - 1) := hinterp
      _ < (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          (F.highest.n - 1) := hBmulLt
      _ = (F.highest.n - 1) *
          ((F.V + 1) * (F.locked.ell + 1 - F.highest.n)) := by
        simp [Nat.mul_comm]
  by_contra hnot
  have hge :
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) ≤
        T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e := by
    omega
  have hscaledGe := Nat.mul_le_mul_left (F.highest.n - 1) hge
  exact (not_lt_of_ge hscaledGe) hscaledLt

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
