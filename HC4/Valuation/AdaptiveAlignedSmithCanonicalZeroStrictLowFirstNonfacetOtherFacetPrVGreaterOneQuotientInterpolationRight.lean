import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneQuotientInterpolation
import Mathlib.Tactic

/-!
# A19 swapped non-unit PR quotient interpolation

This is the `(V,1)` companion of the whole-carrier interpolation theorem.  It
uses the same final source exposure and endpoint-native skew; only the two
transverse quotient drops are exchanged.
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

/-- **Whole-carrier quotient interpolation, right orientation.** -/
theorem QsOtherFacetPrRightVContactFrontierData.quotient_affine_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := rankThreeQuotientCoordinate F.V 1 e
    let qL := rankThreeQuotientCoordinate F.V 1 C.ray.facetExponent
    let qH := rankThreeQuotientCoordinate F.V 1 F.highest.e0
    ((qH.pair : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) ∧
      ((qH.pair : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) := by
  let q := rankThreeQuotientCoordinate F.V 1 e
  let qL := rankThreeQuotientCoordinate F.V 1 C.ray.facetExponent
  let qH := rankThreeQuotientCoordinate F.V 1 F.highest.e0
  let skew := qsOtherFacetSkewWeight C .pr
  have hfacetMem := F.locked.facet_provenance.carrier_mem
  have houtMem := F.locked.outside_provenance.carrier_mem
  have h0 : C.ray.outsideExponent 0 = C.ray.facetExponent 0 + 1 := by
    rw [F.locked.outside_zero, F.locked.facet_zero]
  have h1 : C.ray.facetExponent 1 = C.ray.outsideExponent 1 + 1 := by
    rw [F.locked.facet_one, F.locked.outside_one]
  have h2 : C.ray.facetExponent 2 = C.ray.outsideExponent 2 + F.V := by
    rw [F.locked.facet_two, F.locked.outside_two]
    ring
  have h3 : C.ray.facetExponent 3 = C.ray.outsideExponent 3 + 1 := by
    rw [F.locked.facet_three, F.locked.outside_three]
  have hfinalEq :
      Finsupp.weight P.finalWeight C.ray.facetExponent =
        Finsupp.weight P.finalWeight C.ray.outsideExponent := by
    rw [P.support_final_level hfacetMem, P.support_final_level houtMem]
  have hfinalNeutral :
      RankThreeDirectionNeutralWeight F.V 1 P.finalWeight :=
    rankThreeDirectionNeutralWeight_of_primitive_pair
      F.V 1 P.finalWeight C.ray.facetExponent C.ray.outsideExponent
      h0 h1 h2 h3 hfinalEq
  have hskewEq :
      Finsupp.weight skew C.ray.facetExponent =
        Finsupp.weight skew C.ray.outsideExponent := by
    dsimp [skew]
    rw [C.qsOtherFacetSkewWeight_facet_eq_level
        hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree,
      C.qsOtherFacetSkewWeight_outside_eq_level
        hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree]
  have hskewNeutral : RankThreeDirectionNeutralWeight F.V 1 skew :=
    rankThreeDirectionNeutralWeight_of_primitive_pair
      F.V 1 skew C.ray.facetExponent C.ray.outsideExponent
      h0 h1 h2 h3 hskewEq
  have hpairL : qL.pair = 1 := by
    simp [qL, rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one]
  have hwq :
      rankThreeQuotientWeight P.finalWeight q =
        rankThreeQuotientWeight P.finalWeight qL := by
    calc
      rankThreeQuotientWeight P.finalWeight q =
          Finsupp.weight P.finalWeight e := by
            symm
            exact finsupp_weight_eq_rankThreeQuotientWeight
              F.V 1 P.finalWeight hfinalNeutral e
      _ = P.finalLevel := P.support_final_level he
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = rankThreeQuotientWeight P.finalWeight qL :=
        finsupp_weight_eq_rankThreeQuotientWeight
          F.V 1 P.finalWeight hfinalNeutral C.ray.facetExponent
  have hwH :
      rankThreeQuotientWeight P.finalWeight qH =
        rankThreeQuotientWeight P.finalWeight qL := by
    calc
      rankThreeQuotientWeight P.finalWeight qH =
          Finsupp.weight P.finalWeight F.highest.e0 := by
            symm
            exact finsupp_weight_eq_rankThreeQuotientWeight
              F.V 1 P.finalWeight hfinalNeutral F.highest.e0
      _ = P.finalLevel :=
        P.support_final_level F.highest.e0_provenance.carrier_mem
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = rankThreeQuotientWeight P.finalWeight qL :=
        finsupp_weight_eq_rankThreeQuotientWeight
          F.V 1 P.finalWeight hfinalNeutral C.ray.facetExponent
  have hskewL :
      rankThreeQuotientWeight skew qL = qsOtherFacetSkewLevel C .pr := by
    calc
      rankThreeQuotientWeight skew qL =
          Finsupp.weight skew C.ray.facetExponent := by
            symm
            exact finsupp_weight_eq_rankThreeQuotientWeight
              F.V 1 skew hskewNeutral C.ray.facetExponent
      _ = qsOtherFacetSkewLevel C .pr := by
        dsimp [skew]
        exact C.qsOtherFacetSkewWeight_facet_eq_level
          hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
  have hskewE :
      Finsupp.weight skew e = rankThreeQuotientWeight skew q :=
    finsupp_weight_eq_rankThreeQuotientWeight F.V 1 skew hskewNeutral e
  have hskewH :
      Finsupp.weight skew F.highest.e0 = rankThreeQuotientWeight skew qH :=
    finsupp_weight_eq_rankThreeQuotientWeight
      F.V 1 skew hskewNeutral F.highest.e0
  have hpairE : qsOtherFacetPairDegree .pr e = (q.pair : ℤ) := by
    simp [q, qsOtherFacetPairDegree, rankThreeQuotientCoordinate]
  have hpairH :
      qsOtherFacetPairDegree .pr F.highest.e0 = (qH.pair : ℤ) := by
    simp [qH, qsOtherFacetPairDegree, rankThreeQuotientCoordinate]
  have hv := P.support_wall_ratio he F.highest.e0_provenance.carrier_mem
  rw [hpairE, hpairH, hskewE, hskewH, ← hskewL] at hv
  have hdet := pr_final_skew_transverseDet_ne_zero C P hthree houtThree
  exact rankThreeQuotientCoordinate_affine_interpolation
    P.finalWeight skew qL qH q hpairL hdet hwq hwH hv

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
