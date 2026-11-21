import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarSpecialPivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneNoInteriorSupport
import Mathlib.Tactic

/-!
# A19 strict interior appears at the first positive planar-contact layer

The singular planar-contact reverse Rees has a canonical least positive actual
parameter layer.  If the whole carrier contains any strict-interior staircase
support, this file proves that the selected first layer is itself strict
interior:

    1 < pairDegree(first layer) < highest.n.

This removes one ambiguity before the first-variation calculation.  In
particular the first layer cannot secretly be the already-known highest
primitive pair.

No coprimality of the wall segment is assumed.  The proof uses only the exact
contact-order interpolation already retained by the source-honest frontier.
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

/-- Every actual carrier monomial occurs in the planar-contact family at its
literal reverse order. -/
theorem parameterLayer_mem_of_carrier_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    e ∈ (familyParameterLayer D.family
      (T.topFace.degree -
        Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e)).support := by
  let q := T.topFace.degree -
    Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e
  apply MvPolynomial.mem_support_iff.mpr
  have hformula := reverseWeightedReesFamily_parameterLayer_coeff
    (K := K) (qsIntegralContactWeight (F.V + 1))
    T.topFace.degree q P.carrier D.bound e
  change MvPolynomial.coeff e (familyParameterLayer D.family q) = _ at hformula
  rw [hformula]
  simp [q, he, MvPolynomial.mem_support_iff.mp he]

/-- Failure of `NoStrictInteriorSupport` produces a literal strict-interior
carrier monomial. -/
theorem exists_strictInterior_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ e ∈ P.carrier.support,
      1 < (rankThreeQuotientCoordinate 1 F.V e).pair ∧
      (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n := by
  classical
  by_contra hnone
  apply hnot
  intro e he
  have hkpos := F.support_pair_pos hthree houtThree he
  rcases F.support_staircase_classification hthree houtThree he with
    ⟨_j, _hj, hkn, _hjell, _hj0, _hjell⟩
  by_cases hk1 : (rankThreeQuotientCoordinate 1 F.V e).pair = 1
  · exact Or.inl hk1
  by_cases hkn' : (rankThreeQuotientCoordinate 1 F.V e).pair = F.highest.n
  · exact Or.inr hkn'
  exfalso
  apply hnone
  have hkgt : 1 < (rankThreeQuotientCoordinate 1 F.V e).pair :=
    lt_of_le_of_ne hkpos (Ne.symm hk1)
  have hklt : (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n :=
    lt_of_le_of_ne hkn hkn'
  exact ⟨e, he, hkgt, hklt⟩

/-- A strict-interior monomial has strictly positive planar-contact reverse
order. -/
theorem reverseOrder_pos_of_strictInterior
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
    (hk : 1 < (rankThreeQuotientCoordinate 1 F.V e).pair) :
    0 < T.topFace.degree -
      Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e := by
  have hinterp := F.contactOrder_interpolation hthree houtThree he
  rw [← D.reverseOrder_eq_quotientContactOrder hthree houtThree e] at hinterp
  have hsep := F.highest_n_lt_locked_height hthree houtThree
  have hgap : 0 < F.locked.ell + 1 - F.highest.n :=
    Nat.sub_pos_of_lt hsep
  have hB :
      0 < (F.V + 1) * (F.locked.ell + 1 - F.highest.n) :=
    Nat.mul_pos (Nat.succ_pos F.V) hgap
  have hk1 :
      0 < (rankThreeQuotientCoordinate 1 F.V e).pair - 1 :=
    Nat.sub_pos_of_lt hk
  by_contra hnot
  have hq0 :
      T.topFace.degree -
        Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hq0] at hinterp
  have hrhs :
      0 < (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((rankThreeQuotientCoordinate 1 F.V e).pair - 1) :=
    Nat.mul_pos hB hk1
  have hrhs0 :
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 F.V e).pair - 1) = 0 := by
    simpa using hinterp.symm
  exact (Nat.ne_of_gt hrhs) hrhs0

/-- If strict-interior support exists, the least positive actual layer occurs
strictly before the highest primitive pair. -/
theorem firstPositiveOrder_lt_highest_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    firstPositiveActualParameterOrder D.family D.hasPositiveLayer <
      D.highestOrder := by
  rcases D.exists_strictInterior_of_not_noStrictInterior
      hthree houtThree hnot with ⟨e, he, hkgt, hklt⟩
  let q := T.topFace.degree -
    Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e
  have heLayer : e ∈ (familyParameterLayer D.family q).support := by
    simpa [q] using D.parameterLayer_mem_of_carrier_mem he
  have hcoeff :
      (MvPolynomial.coeff e D.family).coeff q ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp heLayer
    rw [familyParameterLayer_coeff] at h
    exact h
  have heFamily : e ∈ D.family.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hqmem : q ∈ familyParameterLayerOrders D.family :=
    (mem_familyParameterLayerOrders_iff D.family q).2
      ⟨e, heFamily, hcoeff⟩
  have hqpos : 0 < q := by
    dsimp [q]
    exact D.reverseOrder_pos_of_strictInterior hthree houtThree he hkgt
  have hfirstle :
      firstPositiveActualParameterOrder D.family D.hasPositiveLayer ≤ q :=
    firstPositiveActualParameterOrder_le D.family D.hasPositiveLayer hqmem hqpos
  have hqhigh : q < D.highestOrder := by
    dsimp [q]
    exact D.reverseOrder_lt_highest_of_pair_lt_highest
      hthree houtThree he hklt
  exact lt_of_le_of_lt hfirstle hqhigh

/-- **First-layer strict interior.**  Under failure of the endpoint-only
classification, every monomial of the selected least positive layer has pair
degree strictly between the locked and highest values. -/
theorem firstPositiveLayer_pair_strictInterior_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    1 < (rankThreeQuotientCoordinate 1 F.V e).pair ∧
      (rankThreeQuotientCoordinate 1 F.V e).pair < F.highest.n := by
  have hkgt := D.firstPositiveLayer_pair_gt_one hthree houtThree he
  have hfirstlt := D.firstPositiveOrder_lt_highest_of_not_noStrictInterior
    hthree houtThree hnot
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, heOrder⟩
  have hkn :=
    (F.support_staircase_classification hthree houtThree heP).choose_spec.2.1
  refine ⟨hkgt, ?_⟩
  by_contra hnotlt
  have hnle :
      F.highest.n ≤ (rankThreeQuotientCoordinate 1 F.V e).pair :=
    Nat.le_of_not_gt hnotlt
  have hkeq :
      (rankThreeQuotientCoordinate 1 F.V e).pair = F.highest.n :=
    Nat.le_antisymm hkn hnle
  have hinterp := F.contactOrder_interpolation hthree houtThree heP
  rw [← D.reverseOrder_eq_quotientContactOrder hthree houtThree e,
    heOrder, hkeq] at hinterp
  have hn1pos : 0 < F.highest.n - 1 := by
    exact Nat.sub_pos_of_lt (show 1 < F.highest.n by
      exact F.highest.n_two_le)
  have hEq :
      firstPositiveActualParameterOrder D.family D.hasPositiveLayer =
        D.highestOrder := by
    unfold highestOrder
    have hsame :
        (F.highest.n - 1) *
            firstPositiveActualParameterOrder D.family D.hasPositiveLayer =
          (F.highest.n - 1) *
            ((F.V + 1) * (F.locked.ell + 1 - F.highest.n)) := by
      calc
        (F.highest.n - 1) *
            firstPositiveActualParameterOrder D.family D.hasPositiveLayer =
          (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
            (F.highest.n - 1) := hinterp
        _ = (F.highest.n - 1) *
            ((F.V + 1) * (F.locked.ell + 1 - F.highest.n)) := by ring
    exact Nat.mul_left_cancel hn1pos hsame
  rw [hEq] at hfirstlt
  exact (Nat.lt_irrefl _ hfirstlt)

/-- The first positive layer therefore has one canonical strict-interior
staircase height shared by every one of its monomials. -/
theorem exists_firstPositiveLayer_strictInterior_coordinates
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ e k j,
      e ∈ (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support ∧
      k = (rankThreeQuotientCoordinate 1 F.V e).pair ∧
      1 < k ∧ k < F.highest.n ∧
      (rankThreeQuotientCoordinate 1 F.V e).firstTransverse = j + 1 ∧
      0 < j ∧ j < F.locked.ell := by
  have hne := firstPositiveActualParameterLayer_ne_zero
    D.family D.hasPositiveLayer
  have hreal := firstPositiveActualParameterOrder_realised
    D.family D.hasPositiveLayer
  rcases hreal with ⟨e, heFamily, hcoeff⟩
  have he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [familyParameterLayer_coeff]
    exact hcoeff
  have hinterior :=
    D.firstPositiveLayer_pair_strictInterior_of_not_noStrictInterior
      hthree houtThree hnot he
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, _heOrder⟩
  rcases F.support_staircase_classification hthree houtThree heP with
    ⟨j, hj, _hkn, hjell, hj0, hjellEq⟩
  let k := (rankThreeQuotientCoordinate 1 F.V e).pair
  have hjpos : 0 < j := by
    apply Nat.pos_of_ne_zero
    intro hjz
    have hkN := hj0.mp hjz
    exact (Nat.ne_of_lt hinterior.2) hkN
  have hjlt : j < F.locked.ell := by
    apply lt_of_le_of_ne hjell
    intro hjeq
    have hk1 := hjellEq.mp hjeq
    exact (Nat.ne_of_gt hinterior.1) hk1
  exact ⟨e, k, j, he, rfl, hinterior.1, hinterior.2, hj, hjpos, hjlt⟩

/-- Every supported exact layer coefficient is the literal carrier coefficient.
This keeps coefficient provenance when constructing the first-variation profile. -/
theorem parameterLayer_coeff_eq_carrier_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    {q : ℕ} {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family q).support) :
    MvPolynomial.coeff e (familyParameterLayer D.family q) =
      MvPolynomial.coeff e P.carrier := by
  have hsource := D.parameterLayer_support_source_and_order he
  have hformula := reverseWeightedReesFamily_parameterLayer_coeff
    (K := K) (qsIntegralContactWeight (F.V + 1))
    T.topFace.degree q P.carrier D.bound e
  change MvPolynomial.coeff e (familyParameterLayer D.family q) = _ at hformula
  simpa [hsource.1, hsource.2] using hformula

/-- The first positive layer has a single full quotient coordinate, not just
one pair degree. The carrier's two retained affine equations supply this fact. -/
theorem firstPositiveLayer_quotient_fiber
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
    rankThreeQuotientCoordinate 1 F.V e =
      rankThreeQuotientCoordinate 1 F.V f := by
  have hp := D.firstPositiveLayer_pair_fiber hthree houtThree he hf
  apply F.quotient.pair_fiber
    (D.parameterLayer_support_source_and_order he).1
    (D.parameterLayer_support_source_and_order hf).1
  change e 0 + e 1 = f 0 + f 1 at hp
  change (e 0 : ℤ) + (e 1 : ℤ) = (f 0 : ℤ) + (f 1 : ℤ)
  exact_mod_cast hp

/-- Shared first-interior coordinates, with exact coefficients retained for
all supported monomials. These are derived from the live frontier. -/
theorem exists_firstPositiveLayer_strictInterior_fiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ k j : ℕ, 1 < k ∧ k < F.highest.n ∧
      0 < j ∧ j < F.locked.ell ∧
      ∀ e ∈ (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
        (rankThreeQuotientCoordinate 1 F.V e).pair = k ∧
        (rankThreeQuotientCoordinate 1 F.V e).firstTransverse = j + 1 ∧
        MvPolynomial.coeff e (familyParameterLayer D.family
          (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)) =
          MvPolynomial.coeff e P.carrier := by
  obtain ⟨e, k, j, he, hk, hkgt, hklt, hj, hjpos, hjlt⟩ :=
    D.exists_firstPositiveLayer_strictInterior_coordinates hthree houtThree hnot
  refine ⟨k, j, hkgt, hklt, hjpos, hjlt, ?_⟩
  intro f hf
  have hq := D.firstPositiveLayer_quotient_fiber hthree houtThree hf he
  refine ⟨?_, ?_, D.parameterLayer_coeff_eq_carrier_of_mem hf⟩
  · rw [hq, ← hk]
  · rw [hq, hj]

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
