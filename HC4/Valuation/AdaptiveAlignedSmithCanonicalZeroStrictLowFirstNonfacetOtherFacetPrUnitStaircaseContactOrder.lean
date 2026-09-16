import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseClassification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseContactOrder
import Mathlib.Tactic

/-!
# A19 exact contact order on the unit PR staircase

The state-free wall/contact arithmetic used in the non-unit implementation
has no strict `V > 1` hypothesis.  At the genuine unit direction the honest
source contact order is simply twice the staircase contact deficit.  This file
records the exact left-oriented interpolation law needed by the locked-side
reverse Rees selector.
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

/-- Exact honest contact order of a classified left unit staircase point. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.contactOrder_eq_of_staircase_height
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    {j : ℕ}
    (hj : (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).firstTransverse = j + 1) :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 1 e =
      2 * (F.locked.ell + 1 -
        ((HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair + j)) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hcurveZ := hs.2
  rw [hj] at hcurveZ
  norm_num at hcurveZ
  have hjNat : e 0 + e 2 = j + 1 := by
    simpa only [HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
      one_mul] using hj
  have hcurve : e 0 + e 3 = e 0 + e 1 + j := by
    have hcurveZ' :
        (e 0 : ℤ) + (e 3 : ℤ) =
          (e 0 : ℤ) + (e 1 : ℤ) + (j : ℤ) := by
      convert hcurveZ using 1 <;> ring
    exact_mod_cast hcurveZ'
  have hk := F.support_pair_pos hthree houtThree he
  have hslopeZ := hs.1
  rw [hj] at hslopeZ
  norm_num at hslopeZ
  have hdef := prVGreaterOne_wallSlope_contactDeficit_nat
    F.locked.ell F.highest.n q.pair j
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree) hk
    (by simpa [q] using hslopeZ)
  unfold qsOtherFacetPrQuotientContactOrder
  rw [F.topFace_degree_eq]
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    one_mul]
  rw [hjNat, hcurve]
  have hweight :
      e 0 + e 1 + (j + 1) + (e 0 + e 1 + j) =
        2 * (e 0 + e 1 + j) + 1 := by ring
  rw [hweight, Nat.mul_sub_left_distrib]
  omega

/-- The unit left contact order satisfies the exact endpoint interpolation
law.  In particular it is strictly increasing with pair degree. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.contactOrder_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    (F.highest.n - 1) *
        qsOtherFacetPrQuotientContactOrder (T := T) 1 1 e =
      2 * (F.locked.ell + 1 - F.highest.n) *
        ((HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair - 1) := by
  rcases F.support_staircase_classification hthree houtThree he with
    ⟨j, hj, _hkN, _hjell, _hj0, _hjellEq⟩
  have hk := F.support_pair_pos hthree houtThree he
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hslopeZ := hs.1
  rw [hj] at hslopeZ
  norm_num at hslopeZ
  have hdef := prVGreaterOne_wallSlope_contactDeficit_nat
    F.locked.ell F.highest.n
    (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair j
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree) hk
    (by simpa using hslopeZ)
  rw [F.contactOrder_eq_of_staircase_height hthree houtThree he hj]
  calc
    (F.highest.n - 1) *
        (2 * (F.locked.ell + 1 -
          ((HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair + j))) =
      2 * ((F.highest.n - 1) *
        (F.locked.ell + 1 -
          ((HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair + j))) := by ring
    _ = 2 * ((F.locked.ell + 1 - F.highest.n) *
        ((HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair - 1)) := by
      rw [hdef.2]
    _ = 2 * (F.locked.ell + 1 - F.highest.n) *
        ((HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair - 1) := by ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
