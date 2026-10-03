import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitContactFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneQuotientInterpolation
import Mathlib.Tactic

/-!
# A19 unit PR whole-carrier quotient interpolation

The non-unit quotient interpolation proof uses only the literal locked ray,
the final source weight, the endpoint-native neutral skew, and the positive
Hessian clock.  None of those steps uses `1 < V`.  This file records the same
source-honest argument at the genuine unit direction `(1,-1,-1,-1)` without
weakening the non-unit frontier type.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem unit_weight_explicit_fin4
    (a : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight a e =
      a 0 * (e 0 : ℤ) + a 1 * (e 1 : ℤ) +
      a 2 * (e 2 : ℤ) + a 3 * (e 3 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    ring
  · intro i
    simp

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

private theorem unit_pr_final_skew_transverseDet_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    P.finalWeight 2 * qsOtherFacetSkewWeight C .pr 3 -
      P.finalWeight 3 * qsOtherFacetSkewWeight C .pr 2 ≠ 0 := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hout1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  have hfacetMem : C.ray.facetExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.facet_mem_face)
    simpa using h
  have houtMem : C.ray.outsideExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.outside_mem_face)
    simpa using h
  have hfacetLevel := P.support_final_level hfacetMem
  have houtLevel := P.support_final_level houtMem
  simp only [unit_weight_explicit_fin4] at hfacetLevel houtLevel
  simp [hfacet0, hfacet1, hout0, hout1] at hfacetLevel houtLevel
  have hclock := P.hessianClock_pos
  rw [Fin.sum_univ_four] at hclock
  intro hdet
  simp [qsOtherFacetSkewWeight] at hdet
  nlinarith

/-- Unit left orientation: every carrier support point lies on the affine
quotient line joining the locked endpoint to the primitive highest endpoint. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.quotient_affine_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
    let qL := HC4.Polynomial.rankThreeQuotientCoordinate
      1 1 C.ray.facetExponent
    let qH := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 F.highest.e0
    ((qH.pair : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) ∧
      ((qH.pair : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  let qL := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent
  let qH := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 F.highest.e0
  let skew := qsOtherFacetSkewWeight C .pr
  have hfacetMem := F.locked.facet_provenance.carrier_mem
  have houtMem := F.locked.outside_provenance.carrier_mem
  have h0 : C.ray.outsideExponent 0 = C.ray.facetExponent 0 + 1 := by
    rw [F.locked.outside_zero, F.locked.facet_zero]
  have h1 : C.ray.facetExponent 1 = C.ray.outsideExponent 1 + 1 := by
    rw [F.locked.facet_one, F.locked.outside_one]
  have h2 : C.ray.facetExponent 2 = C.ray.outsideExponent 2 + 1 := by
    rw [F.locked.facet_two, F.locked.outside_two]
  have h3 : C.ray.facetExponent 3 = C.ray.outsideExponent 3 + 1 := by
    rw [F.locked.facet_three, F.locked.outside_three]
    ring
  have hfinalEq :
      Finsupp.weight P.finalWeight C.ray.facetExponent =
        Finsupp.weight P.finalWeight C.ray.outsideExponent := by
    rw [P.support_final_level hfacetMem, P.support_final_level houtMem]
  have hfinalNeutral :
      HC4.Polynomial.RankThreeDirectionNeutralWeight 1 1 P.finalWeight :=
    HC4.Polynomial.rankThreeDirectionNeutralWeight_of_primitive_pair
      1 1 P.finalWeight C.ray.facetExponent C.ray.outsideExponent
      h0 h1 h2 h3 hfinalEq
  have hskewEq :
      Finsupp.weight skew C.ray.facetExponent =
        Finsupp.weight skew C.ray.outsideExponent := by
    dsimp [skew]
    rw [C.qsOtherFacetSkewWeight_facet_eq_level
        hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree,
      C.qsOtherFacetSkewWeight_outside_eq_level
        hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree]
  have hskewNeutral :
      HC4.Polynomial.RankThreeDirectionNeutralWeight 1 1 skew :=
    HC4.Polynomial.rankThreeDirectionNeutralWeight_of_primitive_pair
      1 1 skew C.ray.facetExponent C.ray.outsideExponent
      h0 h1 h2 h3 hskewEq
  have hpairL : qL.pair = 1 := by
    simp [qL, HC4.Polynomial.rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one]
  have hwq :
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight q =
        HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight q =
          Finsupp.weight P.finalWeight e := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 1 P.finalWeight hfinalNeutral e
      _ = P.finalLevel := P.support_final_level he
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL :=
        HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
          1 1 P.finalWeight hfinalNeutral C.ray.facetExponent
  have hwH :
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qH =
        HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qH =
          Finsupp.weight P.finalWeight F.highest.e0 := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 1 P.finalWeight hfinalNeutral F.highest.e0
      _ = P.finalLevel :=
        P.support_final_level F.highest.e0_provenance.carrier_mem
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL :=
        HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
          1 1 P.finalWeight hfinalNeutral C.ray.facetExponent
  have hskewL :
      HC4.Polynomial.rankThreeQuotientWeight skew qL =
        qsOtherFacetSkewLevel C .pr := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight skew qL =
          Finsupp.weight skew C.ray.facetExponent := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 1 skew hskewNeutral C.ray.facetExponent
      _ = qsOtherFacetSkewLevel C .pr := by
        dsimp [skew]
        exact C.qsOtherFacetSkewWeight_facet_eq_level
          hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
  have hskewE :
      Finsupp.weight skew e =
        HC4.Polynomial.rankThreeQuotientWeight skew q :=
    HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
      1 1 skew hskewNeutral e
  have hskewH :
      Finsupp.weight skew F.highest.e0 =
        HC4.Polynomial.rankThreeQuotientWeight skew qH :=
    HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
      1 1 skew hskewNeutral F.highest.e0
  have hpairE : qsOtherFacetPairDegree .pr e = (q.pair : ℤ) := by
    simp [q, qsOtherFacetPairDegree,
      HC4.Polynomial.rankThreeQuotientCoordinate]
  have hpairH :
      qsOtherFacetPairDegree .pr F.highest.e0 = (qH.pair : ℤ) := by
    simp [qH, qsOtherFacetPairDegree,
      HC4.Polynomial.rankThreeQuotientCoordinate]
  have hv := P.support_wall_ratio he F.highest.e0_provenance.carrier_mem
  rw [hpairE, hpairH, hskewE, hskewH, ← hskewL] at hv
  have hdet := unit_pr_final_skew_transverseDet_ne_zero C P hthree houtThree
  exact rankThreeQuotientCoordinate_affine_interpolation
    P.finalWeight skew qL qH q hpairL hdet hwq hwH hv

/-- Unit right orientation: the same quotient-line argument, with the highest
endpoint transversely swapped. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.quotient_affine_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
    let qL := HC4.Polynomial.rankThreeQuotientCoordinate
      1 1 C.ray.facetExponent
    let qH := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 F.highest.e0
    ((qH.pair : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) ∧
      ((qH.pair : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  let qL := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 C.ray.facetExponent
  let qH := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 F.highest.e0
  let skew := qsOtherFacetSkewWeight C .pr
  have hfacetMem := F.locked.facet_provenance.carrier_mem
  have houtMem := F.locked.outside_provenance.carrier_mem
  have h0 : C.ray.outsideExponent 0 = C.ray.facetExponent 0 + 1 := by
    rw [F.locked.outside_zero, F.locked.facet_zero]
  have h1 : C.ray.facetExponent 1 = C.ray.outsideExponent 1 + 1 := by
    rw [F.locked.facet_one, F.locked.outside_one]
  have h2 : C.ray.facetExponent 2 = C.ray.outsideExponent 2 + 1 := by
    rw [F.locked.facet_two, F.locked.outside_two]
    ring
  have h3 : C.ray.facetExponent 3 = C.ray.outsideExponent 3 + 1 := by
    rw [F.locked.facet_three, F.locked.outside_three]
  have hfinalEq :
      Finsupp.weight P.finalWeight C.ray.facetExponent =
        Finsupp.weight P.finalWeight C.ray.outsideExponent := by
    rw [P.support_final_level hfacetMem, P.support_final_level houtMem]
  have hfinalNeutral :
      HC4.Polynomial.RankThreeDirectionNeutralWeight 1 1 P.finalWeight :=
    HC4.Polynomial.rankThreeDirectionNeutralWeight_of_primitive_pair
      1 1 P.finalWeight C.ray.facetExponent C.ray.outsideExponent
      h0 h1 h2 h3 hfinalEq
  have hskewEq :
      Finsupp.weight skew C.ray.facetExponent =
        Finsupp.weight skew C.ray.outsideExponent := by
    dsimp [skew]
    rw [C.qsOtherFacetSkewWeight_facet_eq_level
        hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree,
      C.qsOtherFacetSkewWeight_outside_eq_level
        hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree]
  have hskewNeutral :
      HC4.Polynomial.RankThreeDirectionNeutralWeight 1 1 skew :=
    HC4.Polynomial.rankThreeDirectionNeutralWeight_of_primitive_pair
      1 1 skew C.ray.facetExponent C.ray.outsideExponent
      h0 h1 h2 h3 hskewEq
  have hpairL : qL.pair = 1 := by
    simp [qL, HC4.Polynomial.rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one]
  have hwq :
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight q =
        HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight q =
          Finsupp.weight P.finalWeight e := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 1 P.finalWeight hfinalNeutral e
      _ = P.finalLevel := P.support_final_level he
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL :=
        HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
          1 1 P.finalWeight hfinalNeutral C.ray.facetExponent
  have hwH :
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qH =
        HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qH =
          Finsupp.weight P.finalWeight F.highest.e0 := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 1 P.finalWeight hfinalNeutral F.highest.e0
      _ = P.finalLevel :=
        P.support_final_level F.highest.e0_provenance.carrier_mem
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL :=
        HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
          1 1 P.finalWeight hfinalNeutral C.ray.facetExponent
  have hskewL :
      HC4.Polynomial.rankThreeQuotientWeight skew qL =
        qsOtherFacetSkewLevel C .pr := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight skew qL =
          Finsupp.weight skew C.ray.facetExponent := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 1 skew hskewNeutral C.ray.facetExponent
      _ = qsOtherFacetSkewLevel C .pr := by
        dsimp [skew]
        exact C.qsOtherFacetSkewWeight_facet_eq_level
          hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
  have hskewE :
      Finsupp.weight skew e =
        HC4.Polynomial.rankThreeQuotientWeight skew q :=
    HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
      1 1 skew hskewNeutral e
  have hskewH :
      Finsupp.weight skew F.highest.e0 =
        HC4.Polynomial.rankThreeQuotientWeight skew qH :=
    HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
      1 1 skew hskewNeutral F.highest.e0
  have hpairE : qsOtherFacetPairDegree .pr e = (q.pair : ℤ) := by
    simp [q, qsOtherFacetPairDegree,
      HC4.Polynomial.rankThreeQuotientCoordinate]
  have hpairH :
      qsOtherFacetPairDegree .pr F.highest.e0 = (qH.pair : ℤ) := by
    simp [qH, qsOtherFacetPairDegree,
      HC4.Polynomial.rankThreeQuotientCoordinate]
  have hv := P.support_wall_ratio he F.highest.e0_provenance.carrier_mem
  rw [hpairE, hpairH, hskewE, hskewH, ← hskewL] at hv
  have hdet := unit_pr_final_skew_transverseDet_ne_zero C P hthree houtThree
  exact rankThreeQuotientCoordinate_affine_interpolation
    P.finalWeight skew qL qH q hpairL hdet hwq hwH hv

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
