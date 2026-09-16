import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitContactSeparation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import Mathlib.Tactic

/-!
# A19 exhaustive unit PR quotient-staircase classification

The state-free staircase arithmetic used in the non-unit branch does not
require `1 < V`; it only needs the exact wall/curve equations, the honest
source bound, and the strict endpoint separation.  The preceding unit files
supply precisely those ingredients at `V=1`.

Thus every actual unit carrier point has pair degree between `1` and the
primitive highest degree `n`, and is the locked endpoint, the highest endpoint,
or a strict interior staircase point.
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

/-- Left unit orientation: every actual carrier point has positive pair
degree. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.support_pair_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    1 ≤ (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hsource := P.support_source he
  have hbound := R.source_weight_le hsource
  have hweight := F.quotient.contactWeight_eq_quotientSum
    R hthree houtThree e
  rw [hweight, F.topFace_degree_eq] at hbound
  have hcontact :
      q.pair + q.firstTransverse + q.secondTransverse ≤
        2 * (F.locked.ell + 1) + 1 := by
    simpa [q] using hbound
  exact prVGreaterOne_quotientStaircase_pair_pos
    1 F.locked.ell F.highest.n
    q.pair q.firstTransverse q.secondTransverse
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree)
    hs.1 (by simpa using hs.2) hcontact

/-- Right unit orientation: every actual carrier point has positive pair
degree. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.support_pair_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    1 ≤ (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hsource := P.support_source he
  have hbound := R.source_weight_le hsource
  have hweight := F.quotient.contactWeight_eq_quotientSum
    R hthree houtThree e
  rw [hweight, F.topFace_degree_eq] at hbound
  have hcontact :
      q.pair + q.secondTransverse + q.firstTransverse ≤
        2 * (F.locked.ell + 1) + 1 := by
    have h := hbound
    simpa [q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  exact prVGreaterOne_quotientStaircase_pair_pos
    1 F.locked.ell F.highest.n
    q.pair q.secondTransverse q.firstTransverse
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree)
    hs.1 (by simpa using hs.2) hcontact

/-- Left unit orientation: exhaustive endpoint/interior quotient
classification for an arbitrary actual carrier monomial. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.support_staircase_classification
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    ∃ j : ℕ,
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).firstTransverse = j + 1 ∧
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair ≤ F.highest.n ∧
      j ≤ F.locked.ell ∧
      (j = 0 ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = F.highest.n) ∧
      (j = F.locked.ell ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = 1) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  rcases prVGreaterOne_quotientStaircase_bounds
      F.locked.ell F.highest.n q.pair q.firstTransverse
      F.locked.ell_pos F.highest.n_two_le
      (F.highest_n_lt_locked_height hthree houtThree)
      (F.support_pair_pos hthree houtThree he) hs.1 with
    ⟨j, hj, hkN, hjell, hj0, hjellEq⟩
  exact ⟨j, hj, hkN, hjell, hj0, hjellEq⟩

/-- Right unit orientation: exhaustive endpoint/interior quotient
classification. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.support_staircase_classification
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    ∃ j : ℕ,
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).secondTransverse = j + 1 ∧
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair ≤ F.highest.n ∧
      j ≤ F.locked.ell ∧
      (j = 0 ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = F.highest.n) ∧
      (j = F.locked.ell ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).pair = 1) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  rcases prVGreaterOne_quotientStaircase_bounds
      F.locked.ell F.highest.n q.pair q.secondTransverse
      F.locked.ell_pos F.highest.n_two_le
      (F.highest_n_lt_locked_height hthree houtThree)
      (F.support_pair_pos hthree houtThree he) hs.1 with
    ⟨j, hj, hkN, hjell, hj0, hjellEq⟩
  exact ⟨j, hj, hkN, hjell, hj0, hjellEq⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation