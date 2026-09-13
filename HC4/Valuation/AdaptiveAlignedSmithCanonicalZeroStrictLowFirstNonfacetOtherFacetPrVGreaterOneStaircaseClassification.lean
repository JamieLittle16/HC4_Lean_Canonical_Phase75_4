import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseBounds
import Mathlib.Tactic

/-!
# A19 exhaustive quotient-staircase classification in the non-unit PR branch

The whole-carrier quotient line plus the honest contact source bound rules out
pair degree zero.  Indeed such a point would lie beyond the locked endpoint:
its wall equation requires too much transverse height, while the contact bound
forces that height to stay at most `ell+1`.

Consequently every actual carrier support point has pair degree between `1`
and the primitive highest degree `n`, and hence is exactly one of:

* the locked endpoint (`k=1`, `j=ell`);
* the primitive highest endpoint (`k=n`, `j=0`); or
* a strict interior quotient point (`1<k<n`, `0<j<ell`).

This file still makes no claim that the strict-interior alternative is
possible.  Its elimination is the next local step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- State-free contact exclusion of pair degree zero on the non-unit quotient
staircase. -/
theorem prVGreaterOne_quotientStaircase_pair_pos
    (V ell n k r s : ℕ)
    (hell : 0 < ell) (hn : 2 ≤ n) (hnell : n < ell + 1)
    (hwall :
      ((n : ℤ) - 1) * ((r : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ)))
    (hcurve :
      (s : ℤ) = (V : ℤ) * ((k : ℤ) + (r : ℤ) - 1))
    (hcontact :
      k + r + s ≤ (V + 1) * (ell + 1) + 1) :
    1 ≤ k := by
  have hnleell : n ≤ ell := by omega
  by_contra hknot
  have hk0 : k = 0 := by omega
  have hcontactZ :
      (k : ℤ) + (r : ℤ) + (s : ℤ) ≤
        ((V + 1) * (ell + 1) + 1 : ℕ) := by
    exact_mod_cast hcontact
  have hVpos : (0 : ℤ) < (V : ℤ) + 1 := by positivity
  have hjle : (r : ℤ) - 1 ≤ (ell : ℤ) + 1 := by
    rw [hk0] at hcurve hcontactZ
    norm_num at hcurve hcontactZ
    nlinarith
  have hncoeff : (0 : ℤ) ≤ (n : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (show 1 ≤ n by omega)
    omega
  have hmul :
      ((n : ℤ) - 1) * ((r : ℤ) - 1) ≤
        ((n : ℤ) - 1) * ((ell : ℤ) + 1) :=
    mul_le_mul_of_nonneg_left hjle hncoeff
  have hnleellZ : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnleell
  rw [hk0] at hwall
  norm_num at hwall
  nlinarith

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Left orientation: every actual carrier point has positive pair degree. -/
theorem QsOtherFacetPrLeftVContactFrontierData.support_pair_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    1 ≤ (rankThreeQuotientCoordinate 1 F.V e).pair := by
  let q := rankThreeQuotientCoordinate 1 F.V e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hsource := P.support_source he
  have hbound := R.source_weight_le hsource
  have hweight := F.quotient.contactWeight_eq_quotientSum
    R hthree houtThree e
  rw [hweight, F.topFace_degree_eq] at hbound
  have hcontact :
      q.pair + q.firstTransverse + q.secondTransverse ≤
        (F.V + 1) * (F.locked.ell + 1) + 1 := by
    simpa [q] using hbound
  exact prVGreaterOne_quotientStaircase_pair_pos
    F.V F.locked.ell F.highest.n
    q.pair q.firstTransverse q.secondTransverse
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree)
    hs.1 hs.2 hcontact

/-- Right orientation: every actual carrier point likewise has positive pair
degree. -/
theorem QsOtherFacetPrRightVContactFrontierData.support_pair_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    1 ≤ (rankThreeQuotientCoordinate F.V 1 e).pair := by
  let q := rankThreeQuotientCoordinate F.V 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hsource := P.support_source he
  have hbound := R.source_weight_le hsource
  have hweight := F.quotient.contactWeight_eq_quotientSum
    R hthree houtThree e
  rw [hweight, F.topFace_degree_eq] at hbound
  have hcontact :
      q.pair + q.secondTransverse + q.firstTransverse ≤
        (F.V + 1) * (F.locked.ell + 1) + 1 := by
    have h := hbound
    simpa [q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  exact prVGreaterOne_quotientStaircase_pair_pos
    F.V F.locked.ell F.highest.n
    q.pair q.secondTransverse q.firstTransverse
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree)
    hs.1 hs.2 hcontact

/-- Left orientation: exhaustive endpoint/interior quotient classification for
an arbitrary actual carrier monomial. -/
theorem QsOtherFacetPrLeftVContactFrontierData.support_staircase_classification
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    ∃ j : ℕ,
      (rankThreeQuotientCoordinate 1 F.V e).firstTransverse = j + 1 ∧
      (rankThreeQuotientCoordinate 1 F.V e).pair ≤ F.highest.n ∧
      j ≤ F.locked.ell ∧
      (j = 0 ↔
        (rankThreeQuotientCoordinate 1 F.V e).pair = F.highest.n) ∧
      (j = F.locked.ell ↔
        (rankThreeQuotientCoordinate 1 F.V e).pair = 1) :=
  F.support_staircase_bounds_of_pair_pos hthree houtThree he
    (F.support_pair_pos hthree houtThree he)

/-- Right orientation: exhaustive endpoint/interior quotient classification. -/
theorem QsOtherFacetPrRightVContactFrontierData.support_staircase_classification
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    ∃ j : ℕ,
      (rankThreeQuotientCoordinate F.V 1 e).secondTransverse = j + 1 ∧
      (rankThreeQuotientCoordinate F.V 1 e).pair ≤ F.highest.n ∧
      j ≤ F.locked.ell ∧
      (j = 0 ↔
        (rankThreeQuotientCoordinate F.V 1 e).pair = F.highest.n) ∧
      (j = F.locked.ell ↔
        (rankThreeQuotientCoordinate F.V 1 e).pair = 1) :=
  F.support_staircase_bounds_of_pair_pos hthree houtThree he
    (F.support_pair_pos hthree houtThree he)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
