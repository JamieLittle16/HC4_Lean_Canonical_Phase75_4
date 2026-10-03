import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarContactRees
import HC4.Polynomial.RankThreeQuotientFibers
import Mathlib.Tactic

/-!
# A19 first positive locked-side unit contact layer

The unit planar contact Rees is the locked-end selector.  Its exact parameter
order is the honest unit quotient-contact deficit, hence strictly increases
with pair degree along the staircase.  Therefore, whenever strict-interior
support exists, the least positive actual layer is the least surviving
strict-interior pair fibre.  Coefficients remain literal carrier coefficients.
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

/-- The unit reverse-Rees order is literally the unit quotient-contact order. -/
theorem reverseOrder_eq_quotientContactOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (e : Fin 4 →₀ ℕ) :
    T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e =
      qsOtherFacetPrQuotientContactOrder (T := T) 1 1 e := by
  rw [qsIntegralContactWeight_finsupp]
  unfold qsOtherFacetPrQuotientContactOrder
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    one_mul, HC4.Polynomial.ordinaryDegree4]
  congr 1
  omega

/-- Supported monomials of an exact layer are actual carrier monomials at that
literal reverse order. -/
theorem parameterLayer_support_source_and_order
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    {q : ℕ} {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family q).support) :
    e ∈ P.carrier.support ∧
      T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e = q := by
  have hc := MvPolynomial.mem_support_iff.mp he
  have hformula := reverseWeightedReesFamily_parameterLayer_coeff
    (K := K) (qsIntegralContactWeight 2)
    T.topFace.degree q P.carrier D.bound e
  change MvPolynomial.coeff e (familyParameterLayer D.family q) = _ at hformula
  by_cases hcond : e ∈ P.carrier.support ∧
      T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e = q
  · exact hcond
  · simp only [if_neg hcond] at hformula
    exact (hc hformula).elim

/-- Literal coefficient preservation on an exact unit contact layer. -/
theorem parameterLayer_coeff_eq_carrier_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    {q : ℕ} {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family q).support) :
    MvPolynomial.coeff e (familyParameterLayer D.family q) =
      MvPolynomial.coeff e P.carrier := by
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, heq⟩
  have hformula := reverseWeightedReesFamily_parameterLayer_coeff
    (K := K) (qsIntegralContactWeight 2)
    T.topFace.degree q P.carrier D.bound e
  change MvPolynomial.coeff e (familyParameterLayer D.family q) = _ at hformula
  rw [hformula]
  simp [heP, heq]

/-- Equal reverse order forces equal pair degree by exact unit interpolation. -/
theorem pair_eq_of_reverseOrder_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (horder :
      T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e =
      T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) f) :
    (rankThreeQuotientCoordinate 1 1 e).pair =
      (rankThreeQuotientCoordinate 1 1 f).pair := by
  have heq := F.contactOrder_interpolation hthree houtThree he
  have hfq := F.contactOrder_interpolation hthree houtThree hf
  rw [← D.reverseOrder_eq_quotientContactOrder e] at heq
  rw [← D.reverseOrder_eq_quotientContactOrder f] at hfq
  rw [horder] at heq
  have hBpos : 0 < 2 * (F.locked.ell + 1 - F.highest.n) := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    exact Nat.mul_pos (by omega) (by omega)
  have hmul :
      2 * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 1 e).pair - 1) =
        2 * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 1 f).pair - 1) := by
    rw [← heq, ← hfq]
  simp only [rankThreeQuotientCoordinate] at hmul ⊢
  have hsub := Nat.mul_left_cancel hBpos hmul
  have hepos := F.support_pair_pos hthree houtThree he
  have hfpos := F.support_pair_pos hthree houtThree hf
  omega

/-- The first positive layer lies in one normalized quotient fibre. -/
theorem firstPositiveLayer_quotient_fiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support)
    (hf : f ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    rankThreeQuotientCoordinate 1 1 e = rankThreeQuotientCoordinate 1 1 f := by
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, heq⟩
  rcases D.parameterLayer_support_source_and_order hf with ⟨hfP, hfq⟩
  have hp := D.pair_eq_of_reverseOrder_eq hthree houtThree heP hfP
    (heq.trans hfq.symm)
  apply F.quotient.pair_fiber heP hfP
  simp only [qsOtherFacetPairDegree]
  exact_mod_cast hp

/-- Every carrier monomial occurs in the unit contact family at its literal
reverse order. -/
theorem parameterLayer_mem_of_carrier_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    e ∈ (familyParameterLayer D.family
      (T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e)).support := by
  let q := T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e
  apply MvPolynomial.mem_support_iff.mpr
  have hformula := reverseWeightedReesFamily_parameterLayer_coeff
    (K := K) (qsIntegralContactWeight 2)
    T.topFace.degree q P.carrier D.bound e
  change MvPolynomial.coeff e (familyParameterLayer D.family q) = _ at hformula
  rw [hformula]
  simp [q, he, MvPolynomial.mem_support_iff.mp he]

/-- Failure of endpoint-only support produces a literal strict-interior unit
carrier monomial. -/
theorem exists_strictInterior_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ e ∈ P.carrier.support,
      1 < (rankThreeQuotientCoordinate 1 1 e).pair ∧
      (rankThreeQuotientCoordinate 1 1 e).pair < F.highest.n := by
  classical
  by_contra hnone
  apply hnot
  intro e he
  have hkpos := F.support_pair_pos hthree houtThree he
  rcases F.support_staircase_classification hthree houtThree he with
    ⟨_j, _hj, hkn, _hjell, _hj0, _hjell⟩
  by_cases hk1 : (rankThreeQuotientCoordinate 1 1 e).pair = 1
  · exact Or.inl hk1
  by_cases hkn' : (rankThreeQuotientCoordinate 1 1 e).pair = F.highest.n
  · exact Or.inr hkn'
  exfalso
  apply hnone
  exact ⟨e, he, lt_of_le_of_ne hkpos (Ne.symm hk1), lt_of_le_of_ne hkn hkn'⟩

/-- Strict-interior pair degree means positive locked-side contact order. -/
theorem reverseOrder_pos_of_strictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    (hk : 1 < (rankThreeQuotientCoordinate 1 1 e).pair) :
    0 < T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e := by
  have hinterp := F.contactOrder_interpolation hthree houtThree he
  rw [← D.reverseOrder_eq_quotientContactOrder e] at hinterp
  have hsep := F.highest_n_lt_locked_height hthree houtThree
  have hB : 0 < 2 * (F.locked.ell + 1 - F.highest.n) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hsep)
  have hk1 : 0 < (rankThreeQuotientCoordinate 1 1 e).pair - 1 :=
    Nat.sub_pos_of_lt hk
  by_contra hnot
  have hq0 : T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hq0] at hinterp
  have hrhs : 0 < 2 * (F.locked.ell + 1 - F.highest.n) *
      ((rankThreeQuotientCoordinate 1 1 e).pair - 1) := Nat.mul_pos hB hk1
  have hrhs0 : 2 * (F.locked.ell + 1 - F.highest.n) *
      ((rankThreeQuotientCoordinate 1 1 e).pair - 1) = 0 := by
    simpa using hinterp.symm
  exact (Nat.ne_of_gt hrhs) hrhs0

/-- A strict-interior point occurs before the primitive highest endpoint in
locked-side contact order. -/
theorem reverseOrder_lt_highest_of_pair_lt_highest
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    (hklt : (rankThreeQuotientCoordinate 1 1 e).pair < F.highest.n) :
    T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e < D.highestOrder := by
  have hinterp := F.contactOrder_interpolation hthree houtThree he
  rw [← D.reverseOrder_eq_quotientContactOrder e] at hinterp
  have hBpos : 0 < 2 * (F.locked.ell + 1 - F.highest.n) := by
    exact Nat.mul_pos (by omega)
      (Nat.sub_pos_of_lt (F.highest_n_lt_locked_height hthree houtThree))
  have hkpos := F.support_pair_pos hthree houtThree he
  have hn1pos : 0 < F.highest.n - 1 :=
    Nat.sub_pos_of_lt F.highest.n_two_le
  unfold highestOrder
  have htarget : (rankThreeQuotientCoordinate 1 1 e).pair - 1 <
      F.highest.n - 1 := by omega
  have hBmulLt := Nat.mul_lt_mul_of_pos_left htarget hBpos
  have hscaledLt :
      (F.highest.n - 1) *
          (T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e) <
      (F.highest.n - 1) * (2 * (F.locked.ell + 1 - F.highest.n)) := by
    calc
      _ = 2 * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 1 e).pair - 1) := hinterp
      _ < 2 * (F.locked.ell + 1 - F.highest.n) * (F.highest.n - 1) := hBmulLt
      _ = _ := by ring
  by_contra hnot
  have hge : 2 * (F.locked.ell + 1 - F.highest.n) ≤
      T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e := by omega
  exact (not_lt_of_ge (Nat.mul_le_mul_left (F.highest.n - 1) hge)) hscaledLt

/-- The least positive contact layer is itself strict interior whenever such
support exists. -/
theorem firstPositiveLayer_pair_strictInterior_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    1 < (rankThreeQuotientCoordinate 1 1 e).pair ∧
      (rankThreeQuotientCoordinate 1 1 e).pair < F.highest.n := by
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, heOrder⟩
  have hkgt : 1 < (rankThreeQuotientCoordinate 1 1 e).pair := by
    have hinterp := F.contactOrder_interpolation hthree houtThree heP
    rw [← D.reverseOrder_eq_quotientContactOrder e, heOrder] at hinterp
    have hqpos := firstPositiveActualParameterOrder_pos D.family D.hasPositiveLayer
    have hkpos := F.support_pair_pos hthree houtThree heP
    by_contra hnotgt
    have hnotgt' :
        ¬ 1 < (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair := by
      simpa only [rankThreeQuotientCoordinate] using hnotgt
    have hk1 : (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = 1 := by
      omega
    rw [hk1] at hinterp
    simpa using
      (Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt F.highest.n_two_le) hqpos))
        (by simpa using hinterp)
  have hkn := (F.support_staircase_classification hthree houtThree heP).choose_spec.2.1
  refine ⟨hkgt, ?_⟩
  by_contra hnotlt
  have hnotlt' :
      ¬ (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair < F.highest.n := by
    simpa only [rankThreeQuotientCoordinate] using hnotlt
  have hkeq :
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = F.highest.n := by
    omega
  have hinterp := F.contactOrder_interpolation hthree houtThree heP
  rw [← D.reverseOrder_eq_quotientContactOrder e, heOrder, hkeq] at hinterp
  have hsame :
      (F.highest.n - 1) * firstPositiveActualParameterOrder D.family D.hasPositiveLayer =
      (F.highest.n - 1) * D.highestOrder := by
    unfold highestOrder
    calc
      _ = 2 * (F.locked.ell + 1 - F.highest.n) * (F.highest.n - 1) := hinterp
      _ = _ := by ring
  have hEq := Nat.mul_left_cancel (Nat.sub_pos_of_lt F.highest.n_two_le) hsame
  rcases D.exists_strictInterior_of_not_noStrictInterior hthree houtThree hnot with
    ⟨a, ha, _hagt, halt⟩
  let qa := T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) a
  have haLayer := D.parameterLayer_mem_of_carrier_mem ha
  have haCoeff : (MvPolynomial.coeff a D.family).coeff qa ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp (by simpa [qa] using haLayer)
    rw [familyParameterLayer_coeff] at h
    exact h
  have haFamily : a ∈ D.family.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at haCoeff
    simp at haCoeff
  have hqamem : qa ∈ familyParameterLayerOrders D.family :=
    (mem_familyParameterLayerOrders_iff D.family qa).2 ⟨a, haFamily, haCoeff⟩
  have hqapos : 0 < qa := by
    dsimp [qa]
    exact D.reverseOrder_pos_of_strictInterior hthree houtThree ha _hagt
  have hfirstle := firstPositiveActualParameterOrder_le
    D.family D.hasPositiveLayer hqamem hqapos
  have hqalt : qa < D.highestOrder := by
    dsimp [qa]
    exact D.reverseOrder_lt_highest_of_pair_lt_highest hthree houtThree ha halt
  rw [← hEq] at hqalt
  exact (not_lt_of_ge hfirstle) hqalt

/-- The first positive contact layer has shared strict-interior staircase
coordinates and literal carrier coefficients. -/
theorem exists_firstPositiveLayer_strictInterior_fiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ k j : ℕ, 1 < k ∧ k < F.highest.n ∧ 0 < j ∧ j < F.locked.ell ∧
      ∀ e ∈ (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
        (rankThreeQuotientCoordinate 1 1 e).pair = k ∧
        (rankThreeQuotientCoordinate 1 1 e).firstTransverse = j + 1 ∧
        MvPolynomial.coeff e (familyParameterLayer D.family
          (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)) =
          MvPolynomial.coeff e P.carrier := by
  have hreal := firstPositiveActualParameterOrder_realised D.family D.hasPositiveLayer
  rcases hreal with ⟨e, _heFamily, hcoeff⟩
  have he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [familyParameterLayer_coeff]
    exact hcoeff
  have hinterior := D.firstPositiveLayer_pair_strictInterior_of_not_noStrictInterior
    hthree houtThree hnot he
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, _⟩
  rcases F.support_staircase_classification hthree houtThree heP with
    ⟨j, hj, _hkn, hjell, hj0, hjellEq⟩
  let k := (rankThreeQuotientCoordinate 1 1 e).pair
  have hjpos : 0 < j := by
    by_contra h
    have hkEq := hj0.mp (Nat.eq_zero_of_not_pos h)
    have : k = F.highest.n := by simpa [k] using hkEq
    omega
  have hjlt : j < F.locked.ell := by
    by_contra h
    have hjeq : j = F.locked.ell := by omega
    have hkEq := hjellEq.mp hjeq
    have : k = 1 := by simpa [k] using hkEq
    omega
  refine ⟨k, j, by simpa [k] using hinterior.1,
    by simpa [k] using hinterior.2, hjpos, hjlt, ?_⟩
  intro f hf
  have hq := D.firstPositiveLayer_quotient_fiber hthree houtThree hf he
  refine ⟨?_, ?_, D.parameterLayer_coeff_eq_carrier_of_mem hf⟩
  · rw [hq]
  · rw [hq, hj]

end QsOtherFacetPrUnitLeftPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation