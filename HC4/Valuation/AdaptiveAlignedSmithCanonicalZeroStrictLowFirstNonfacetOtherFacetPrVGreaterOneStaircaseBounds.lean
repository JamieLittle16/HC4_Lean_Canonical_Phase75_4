import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseSupport
import Mathlib.Tactic

/-!
# A19 endpoint bounds for every non-unit PR quotient point

Once the whole-carrier staircase equation is known, the earlier endpoint
arithmetic applies on quotient space rather than only to a pre-normalised
`e0=0` representative.

For pair degree `k >= 1`, strict contact separation `n < ell+1` first rules
out transverse quotient height zero.  Writing the remaining height as `j+1`
then gives

    (n-1) j = ell (n-k),

so every actual quotient point is the locked endpoint, the primitive highest
endpoint, or a strict interior lattice point.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- State-free conversion from the quotient staircase equation to the exact
endpoint classification. -/
theorem prVGreaterOne_quotientStaircase_bounds
    (ell n k r : ℕ)
    (hell : 0 < ell) (hn : 2 ≤ n) (hnell : n < ell + 1)
    (hk : 1 ≤ k)
    (hwall :
      ((n : ℤ) - 1) * ((r : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    ∃ j : ℕ,
      r = j + 1 ∧
      k ≤ n ∧ j ≤ ell ∧
      (j = 0 ↔ k = n) ∧ (j = ell ↔ k = 1) := by
  have hnleell : n ≤ ell := by omega
  have hellZ : (0 : ℤ) < (ell : ℤ) := by exact_mod_cast hell
  have hnZ : (1 : ℤ) < (n : ℤ) := by
    exact_mod_cast (show 1 < n by omega)
  have hrpos : 1 ≤ r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    have hkgt : n < k := by
      by_contra hnk
      have hkle : k ≤ n := Nat.le_of_not_gt hnk
      have hdiff : (0 : ℤ) ≤ (n : ℤ) - (k : ℤ) := by
        exact sub_nonneg.mpr (by exact_mod_cast hkle)
      have hprod :
          (0 : ℤ) ≤ (ell : ℤ) * ((n : ℤ) - (k : ℤ)) :=
        mul_nonneg (le_of_lt hellZ) hdiff
      rw [hr0] at hwall
      norm_num at hwall
      nlinarith
    have hkdiff : 1 ≤ k - n := by omega
    have heqZ :
        (n : ℤ) - 1 = (ell : ℤ) * ((k : ℤ) - (n : ℤ)) := by
      rw [hr0] at hwall
      norm_num at hwall
      nlinarith
    have hn1 : 1 ≤ n := by omega
    have hnk : n ≤ k := by omega
    have heqNat : n - 1 = ell * (k - n) := by
      apply Int.ofNat.inj
      simpa only [Nat.cast_sub hn1, Nat.cast_mul, Nat.cast_sub hnk] using heqZ
    have hmul : ell ≤ ell * (k - n) := by
      have h := Nat.mul_le_mul_left ell hkdiff
      simpa using h
    omega
  let j : ℕ := r - 1
  have hrj : r = j + 1 := by
    dsimp [j]
    omega
  have hslope :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ)) := by
    rw [← hwall]
    dsimp [j]
    rw [Nat.cast_sub hrpos]
    norm_num
  rcases prVGreaterOne_wallSlope_bounds ell n k j hell hn hk hslope with
    ⟨hkn, hjell, hj0, hjellEq⟩
  exact ⟨j, hrj, hkn, hjell, hj0, hjellEq⟩

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Left orientation: every actual carrier point of positive pair degree has a
canonical quotient height and the exact locked/highest endpoint alternatives. -/
theorem QsOtherFacetPrLeftVContactFrontierData.support_staircase_bounds_of_pair_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    (hk : 1 ≤ (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair) :
    ∃ j : ℕ,
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).firstTransverse = j + 1 ∧
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair ≤ F.highest.n ∧
      j ≤ F.locked.ell ∧
      (j = 0 ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair = F.highest.n) ∧
      (j = F.locked.ell ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair = 1) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hsep := F.highest_n_lt_locked_height hthree houtThree
  rcases prVGreaterOne_quotientStaircase_bounds
      F.locked.ell F.highest.n q.pair q.firstTransverse
      F.locked.ell_pos F.highest.n_two_le hsep hk hs.1 with
    ⟨j, hj, hkN, hjell, hj0, hjellEq⟩
  exact ⟨j, hj, hkN, hjell, hj0, hjellEq⟩

/-- Right orientation: the second transverse quotient coordinate is the
canonical staircase height. -/
theorem QsOtherFacetPrRightVContactFrontierData.support_staircase_bounds_of_pair_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    (hk : 1 ≤ (HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair) :
    ∃ j : ℕ,
      (HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).secondTransverse = j + 1 ∧
      (HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair ≤ F.highest.n ∧
      j ≤ F.locked.ell ∧
      (j = 0 ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair = F.highest.n) ∧
      (j = F.locked.ell ↔
        (HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair = 1) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hsep := F.highest_n_lt_locked_height hthree houtThree
  rcases prVGreaterOne_quotientStaircase_bounds
      F.locked.ell F.highest.n q.pair q.secondTransverse
      F.locked.ell_pos F.highest.n_two_le hsep hk hs.1 with
    ⟨j, hj, hkN, hjell, hj0, hjellEq⟩
  exact ⟨j, hj, hkN, hjell, hj0, hjellEq⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
