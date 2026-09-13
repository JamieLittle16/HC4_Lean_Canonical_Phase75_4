import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneContactInterpolation
import HC4.Polynomial.RankThreeQuotientWeightFactorization
import Mathlib.Tactic

/-!
# A19 whole-carrier interpolation on the non-unit PR quotient line

The previous non-unit files know the locked quotient point and the primitive
highest quotient point.  What is still needed for literal carrier
reconstruction is control of an arbitrary support monomial.

There is a useful way to obtain that control without choosing coordinates for
the first planar wall.  Two source-honest linear forms are already available:

* the final positive source-exposure weight, which is constant on the whole
  planar carrier; and
* the endpoint-native neutral skew, whose ratio to pair degree is constant on
  the retained maximal-ratio wall.

Both annihilate the locked primitive direction.  Their transverse determinant
is nonzero: this is exactly the same positive-Hessian-clock calculation used
by the fixed-pair line-support theorem.  Hence, after passing to quotient
coordinates, those two equations determine the two transverse coordinates
from the pair coordinate.

The result below is an affine interpolation identity between the locked point,
the primitive highest point, and every actual carrier point.  It is the
coordinate-free precursor of the final staircase support classification.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem weight_explicit_fin4
    (a : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight a e =
      a 0 * (e 0 : ℤ) + a 1 * (e 1 : ℤ) +
      a 2 * (e 2 : ℤ) + a 3 * (e 3 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    ring
  · intro i
    simp

private theorem two_by_two_kernel_zero
    {a b c d x y : ℤ}
    (hdet : a * d - b * c ≠ 0)
    (h₁ : a * x + b * y = 0)
    (h₂ : c * x + d * y = 0) :
    x = 0 ∧ y = 0 := by
  have hx : (a * d - b * c) * x = 0 := by
    linear_combination d * h₁ - b * h₂
  have hy : (a * d - b * c) * y = 0 := by
    linear_combination a * h₂ - c * h₁
  exact ⟨(mul_eq_zero.mp hx).resolve_left hdet,
    (mul_eq_zero.mp hy).resolve_left hdet⟩

/-- State-free affine interpolation in quotient space.  One weight is constant
on the line; the second has constant ratio to the pair-coordinate displacement
from the locked point. -/
theorem rankThreeQuotientCoordinate_affine_interpolation
    (w v : Fin 4 → ℤ)
    (qL qH q : HC4.Polynomial.RankThreeQuotientCoordinate)
    (hpairL : qL.pair = 1)
    (hdet : w 2 * v 3 - w 3 * v 2 ≠ 0)
    (hwq : HC4.Polynomial.rankThreeQuotientWeight w q =
      HC4.Polynomial.rankThreeQuotientWeight w qL)
    (hwH : HC4.Polynomial.rankThreeQuotientWeight w qH =
      HC4.Polynomial.rankThreeQuotientWeight w qL)
    (hv :
      ((qH.pair : ℤ) - 1) *
          (HC4.Polynomial.rankThreeQuotientWeight v q -
            HC4.Polynomial.rankThreeQuotientWeight v qL) =
        ((q.pair : ℤ) - 1) *
          (HC4.Polynomial.rankThreeQuotientWeight v qH -
            HC4.Polynomial.rankThreeQuotientWeight v qL)) :
    ((qH.pair : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) ∧
      ((qH.pair : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) := by
  let x : ℤ :=
    ((qH.pair : ℤ) - 1) *
        ((q.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) -
      ((q.pair : ℤ) - 1) *
        ((qH.firstTransverse : ℤ) - (qL.firstTransverse : ℤ))
  let y : ℤ :=
    ((qH.pair : ℤ) - 1) *
        ((q.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) -
      ((q.pair : ℤ) - 1) *
        ((qH.secondTransverse : ℤ) - (qL.secondTransverse : ℤ))
  have hwlin : w 2 * x + w 3 * y = 0 := by
    dsimp [x, y]
    unfold HC4.Polynomial.rankThreeQuotientWeight at hwq hwH
    rw [hpairL] at hwq hwH
    norm_num at hwq hwH
    linear_combination
      ((qH.pair : ℤ) - 1) * hwq - ((q.pair : ℤ) - 1) * hwH
  have hvlin : v 2 * x + v 3 * y = 0 := by
    dsimp [x, y]
    unfold HC4.Polynomial.rankThreeQuotientWeight at hv
    rw [hpairL] at hv
    norm_num at hv
    ring_nf at hv ⊢
    exact hv
  rcases two_by_two_kernel_zero hdet hwlin hvlin with ⟨hx, hy⟩
  dsimp [x] at hx
  dsimp [y] at hy
  constructor <;> linarith

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The final source weight and the neutral skew remain independent on the two
transverse quotient coordinates. -/
private theorem pr_final_skew_transverseDet_ne_zero
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
  simp only [weight_explicit_fin4] at hfacetLevel houtLevel
  simp [hfacet0, hfacet1, hout0, hout1] at hfacetLevel houtLevel
  have hclock := P.hessianClock_pos
  rw [Fin.sum_univ_four] at hclock
  intro hdet
  simp [qsOtherFacetSkewWeight] at hdet
  nlinarith

/-- **Whole-carrier quotient interpolation, left orientation.**  Every actual
support monomial lies on the affine quotient line through the locked point and
the primitive highest point. -/
theorem QsOtherFacetPrLeftVContactFrontierData.quotient_affine_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e
    let qL := HC4.Polynomial.rankThreeQuotientCoordinate
      1 F.V C.ray.facetExponent
    let qH := HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V F.highest.e0
    ((qH.pair : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.firstTransverse : ℤ) - (qL.firstTransverse : ℤ)) ∧
      ((qH.pair : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) =
        ((q.pair : ℤ) - 1) *
          ((qH.secondTransverse : ℤ) - (qL.secondTransverse : ℤ)) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e
  let qL := HC4.Polynomial.rankThreeQuotientCoordinate
    1 F.V C.ray.facetExponent
  let qH := HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V F.highest.e0
  let skew := qsOtherFacetSkewWeight C .pr
  have hfacetMem := F.locked.facet_provenance.carrier_mem
  have houtMem := F.locked.outside_provenance.carrier_mem
  have h0 : C.ray.outsideExponent 0 = C.ray.facetExponent 0 + 1 := by
    rw [F.locked.outside_zero, F.locked.facet_zero]
  have h1 : C.ray.facetExponent 1 = C.ray.outsideExponent 1 + 1 := by
    rw [F.locked.facet_one, F.locked.outside_one]
  have h2 : C.ray.facetExponent 2 = C.ray.outsideExponent 2 + 1 := by
    rw [F.locked.facet_two, F.locked.outside_two]
  have h3 : C.ray.facetExponent 3 = C.ray.outsideExponent 3 + F.V := by
    rw [F.locked.facet_three, F.locked.outside_three]
    ring
  have hfinalEq :
      Finsupp.weight P.finalWeight C.ray.facetExponent =
        Finsupp.weight P.finalWeight C.ray.outsideExponent := by
    rw [P.support_final_level hfacetMem, P.support_final_level houtMem]
  have hfinalNeutral :
      HC4.Polynomial.RankThreeDirectionNeutralWeight
        1 F.V P.finalWeight :=
    HC4.Polynomial.rankThreeDirectionNeutralWeight_of_primitive_pair
      1 F.V P.finalWeight C.ray.facetExponent C.ray.outsideExponent
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
      HC4.Polynomial.RankThreeDirectionNeutralWeight 1 F.V skew :=
    HC4.Polynomial.rankThreeDirectionNeutralWeight_of_primitive_pair
      1 F.V skew C.ray.facetExponent C.ray.outsideExponent
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
              1 F.V P.finalWeight hfinalNeutral e
      _ = P.finalLevel := P.support_final_level he
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL :=
        HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
          1 F.V P.finalWeight hfinalNeutral C.ray.facetExponent
  have hwH :
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qH =
        HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qH =
          Finsupp.weight P.finalWeight F.highest.e0 := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 F.V P.finalWeight hfinalNeutral F.highest.e0
      _ = P.finalLevel :=
        P.support_final_level F.highest.e0_provenance.carrier_mem
      _ = Finsupp.weight P.finalWeight C.ray.facetExponent :=
        (P.support_final_level hfacetMem).symm
      _ = HC4.Polynomial.rankThreeQuotientWeight P.finalWeight qL :=
        HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
          1 F.V P.finalWeight hfinalNeutral C.ray.facetExponent
  have hskewL :
      HC4.Polynomial.rankThreeQuotientWeight skew qL =
        qsOtherFacetSkewLevel C .pr := by
    calc
      HC4.Polynomial.rankThreeQuotientWeight skew qL =
          Finsupp.weight skew C.ray.facetExponent := by
            symm
            exact HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
              1 F.V skew hskewNeutral C.ray.facetExponent
      _ = qsOtherFacetSkewLevel C .pr := by
        dsimp [skew]
        exact C.qsOtherFacetSkewWeight_facet_eq_level
          hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
  have hskewE :
      Finsupp.weight skew e =
        HC4.Polynomial.rankThreeQuotientWeight skew q :=
    HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
      1 F.V skew hskewNeutral e
  have hskewH :
      Finsupp.weight skew F.highest.e0 =
        HC4.Polynomial.rankThreeQuotientWeight skew qH :=
    HC4.Polynomial.finsupp_weight_eq_rankThreeQuotientWeight
      1 F.V skew hskewNeutral F.highest.e0
  have hpairE : qsOtherFacetPairDegree .pr e = (q.pair : ℤ) := by
    simp [q, qsOtherFacetPairDegree,
      HC4.Polynomial.rankThreeQuotientCoordinate]
  have hpairH :
      qsOtherFacetPairDegree .pr F.highest.e0 = (qH.pair : ℤ) := by
    simp [qH, qsOtherFacetPairDegree,
      HC4.Polynomial.rankThreeQuotientCoordinate]
  have hv := P.support_wall_ratio he F.highest.e0_provenance.carrier_mem
  rw [hpairE, hpairH, hskewE, hskewH, ← hskewL] at hv
  have hdet := pr_final_skew_transverseDet_ne_zero C P hthree houtThree
  exact rankThreeQuotientCoordinate_affine_interpolation
    P.finalWeight skew qL qH q hpairL hdet hwq hwH hv

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
