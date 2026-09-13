import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import Mathlib.Tactic

/-!
# A19 exact honest-contact order of every non-unit PR staircase fibre

For a left staircase quotient point

    (k, j+1, V(k+j))

the honest source contact weight is

    (V+1)(k+j)+1,

while the locked top degree is `(V+1)(ell+1)+1`.  Thus its contact-Rees order
is

    delta = (V+1)(ell+1-k-j).

Combining this with the retained wall equation gives the particularly useful
interpolation law

    (n-1) delta = (V+1)(ell+1-n)(k-1).

Hence contact order strictly increases with pair degree between the locked and
highest endpoints.  The same formula holds in the swapped orientation.

This is still the canonical contact-Rees filtration; no identification with
the zero blocker or with the auxiliary planar/ray refinements is made.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Natural-number form of the wall/contact interpolation identity. -/
theorem prVGreaterOne_wallSlope_contactDeficit_nat
    (ell n k j : ℕ)
    (hell : 0 < ell) (hn : 2 ≤ n) (hnell : n < ell + 1)
    (hk : 1 ≤ k)
    (hslope :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    k + j ≤ ell + 1 ∧
      (n - 1) * (ell + 1 - (k + j)) =
        (ell + 1 - n) * (k - 1) := by
  rcases prVGreaterOne_wallSlope_bounds ell n k j hell hn hk hslope with
    ⟨hkn, _hjell, _hj0, _hjellEq⟩
  have hdefZ := prVGreaterOne_wallSlope_contactDeficit_identity
    ell n k j hslope
  have hn1Z : (0 : ℤ) < (n : ℤ) - 1 := by
    have : (1 : ℤ) < (n : ℤ) := by exact_mod_cast (show 1 < n by omega)
    omega
  have hnellZ : (n : ℤ) < ((ell + 1 : ℕ) : ℤ) := by
    exact_mod_cast hnell
  have hgapZ : (0 : ℤ) < (ell : ℤ) + 1 - (n : ℤ) := by
    push_cast at hnellZ
    omega
  have hkZ : (1 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast hk
  have hk1Z : (0 : ℤ) ≤ (k : ℤ) - 1 := by
    omega
  have hdefNonnegZ :
      (0 : ℤ) ≤ (ell : ℤ) + 1 - (k : ℤ) - (j : ℤ) := by
    have hrhs :
        (0 : ℤ) ≤
          ((ell : ℤ) + 1 - (n : ℤ)) * ((k : ℤ) - 1) :=
      mul_nonneg (le_of_lt hgapZ) hk1Z
    nlinarith [hdefZ]
  have hsum : k + j ≤ ell + 1 := by
    exact_mod_cast (show
      (k : ℤ) + (j : ℤ) ≤ (ell : ℤ) + 1 by omega)
  have hcast1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hcast2 : ((ell + 1 - (k + j) : ℕ) : ℤ) =
      (ell : ℤ) + 1 - (k : ℤ) - (j : ℤ) := by
    rw [Nat.cast_sub hsum]
    push_cast
    ring
  have hcast3 : ((ell + 1 - n : ℕ) : ℤ) =
      (ell : ℤ) + 1 - (n : ℤ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hnell)]
    push_cast
    ring
  have hcast4 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  refine ⟨hsum, ?_⟩
  exact_mod_cast (show
    ((n - 1 : ℕ) : ℤ) * ((ell + 1 - (k + j) : ℕ) : ℤ) =
      ((ell + 1 - n : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ) by
        rw [hcast1, hcast2, hcast3, hcast4]
        exact hdefZ)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Exact contact order of a classified left staircase point. -/
theorem QsOtherFacetPrLeftVContactFrontierData.contactOrder_eq_of_staircase_height
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    {j : ℕ}
    (hj : (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).firstTransverse = j + 1) :
    qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V e =
      (F.V + 1) *
        (F.locked.ell + 1 -
          ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair + j)) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hcurveZ := hs.2
  rw [hj] at hcurveZ
  have hjNat : e 0 + e 2 = j + 1 := by
    simpa only [HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
      one_mul] using hj
  have hcurve : F.V * e 0 + e 3 = F.V * (e 0 + e 1 + j) := by
    apply Int.ofNat.inj
    push_cast
    nlinarith [hcurveZ]
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
  omega

/-- Swapped exact contact-order formula. -/
theorem QsOtherFacetPrRightVContactFrontierData.contactOrder_eq_of_staircase_height
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support)
    {j : ℕ}
    (hj : (HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).secondTransverse = j + 1) :
    qsOtherFacetPrQuotientContactOrder (T := T) F.V 1 e =
      (F.V + 1) *
        (F.locked.ell + 1 -
          ((HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair + j)) := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp only at hs
  have hcurveZ := hs.2
  rw [hj] at hcurveZ
  have hjNat : e 0 + e 3 = j + 1 := by
    simpa only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
      one_mul] using hj
  have hcurve : F.V * e 0 + e 2 = F.V * (e 0 + e 1 + j) := by
    apply Int.ofNat.inj
    push_cast
    nlinarith [hcurveZ]
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
  omega

/-- The left contact order satisfies the exact endpoint interpolation law. -/
theorem QsOtherFacetPrLeftVContactFrontierData.contactOrder_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    (F.highest.n - 1) *
        qsOtherFacetPrQuotientContactOrder (T := T) 1 F.V e =
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair - 1) := by
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
    (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair j
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree) hk
    (by simpa using hslopeZ)
  rw [F.contactOrder_eq_of_staircase_height hthree houtThree he hj]
  calc
    (F.highest.n - 1) *
        ((F.V + 1) *
          (F.locked.ell + 1 -
            ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair + j))) =
      (F.V + 1) *
        ((F.highest.n - 1) *
          (F.locked.ell + 1 -
            ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair + j))) := by
        ring
    _ = (F.V + 1) *
        ((F.locked.ell + 1 - F.highest.n) *
          ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair - 1)) := by
        rw [hdef.2]
    _ = (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair - 1) := by
        ring

/-- Symmetric endpoint interpolation law. -/
theorem QsOtherFacetPrRightVContactFrontierData.contactOrder_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    (F.highest.n - 1) *
        qsOtherFacetPrQuotientContactOrder (T := T) F.V 1 e =
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair - 1) := by
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
    (HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair j
    F.locked.ell_pos F.highest.n_two_le
    (F.highest_n_lt_locked_height hthree houtThree) hk
    (by simpa using hslopeZ)
  rw [F.contactOrder_eq_of_staircase_height hthree houtThree he hj]
  calc
    (F.highest.n - 1) *
        ((F.V + 1) *
          (F.locked.ell + 1 -
            ((HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair + j))) =
      (F.V + 1) *
        ((F.highest.n - 1) *
          (F.locked.ell + 1 -
            ((HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair + j))) := by
        ring
    _ = (F.V + 1) *
        ((F.locked.ell + 1 - F.highest.n) *
          ((HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair - 1)) := by
        rw [hdef.2]
    _ = (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((HC4.Polynomial.rankThreeQuotientCoordinate F.V 1 e).pair - 1) := by
        ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
