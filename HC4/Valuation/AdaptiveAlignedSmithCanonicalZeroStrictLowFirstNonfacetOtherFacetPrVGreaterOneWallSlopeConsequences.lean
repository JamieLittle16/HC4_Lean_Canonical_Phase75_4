import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneWallSlope
import Mathlib.Tactic

/-!
# A19 endpoint and interior consequences of the non-unit PR wall slope

The source-facing wall calculation has reduced every left/right staircase
candidate to

    (n - 1) * j = ell * (n - k)

in the integer lattice, where `n >= 2`, `ell > 0`, and the relevant nonlinear
pair degrees satisfy `k >= 1`.

This file records the elementary consequences once:

* `k <= n` and `j <= ell`;
* `j = 0` exactly at the highest pair degree `k = n`;
* `j = ell` exactly at the locked pair degree `k = 1`;
* therefore every other nonlinear two-term fibre is a strict interior fibre
  `1 < k < n`, `0 < j < ell`.

The final contact-aware classification only has to exclude/absorb this strict
interior alternative (or send it to the singleton/developable branch).
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- State-free endpoint classification for the affine wall equation. -/
theorem prVGreaterOne_wallSlope_bounds
    (ell n k j : ℕ)
    (hell : 0 < ell) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hslope :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    k ≤ n ∧ j ≤ ell ∧ (j = 0 ↔ k = n) ∧ (j = ell ↔ k = 1) := by
  have hnZ : (1 : ℤ) < (n : ℤ) := by exact_mod_cast (show 1 < n by omega)
  have hellZ : (0 : ℤ) < (ell : ℤ) := by exact_mod_cast hell
  have hkZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hjZ : (0 : ℤ) ≤ (j : ℤ) := by positivity
  have hkn : k ≤ n := by
    by_contra h
    have hnkZ : (n : ℤ) < (k : ℤ) := by exact_mod_cast Nat.lt_of_not_ge h
    nlinarith
  have hknZ : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkn
  have hjell : j ≤ ell := by
    by_contra h
    have helljZ : (ell : ℤ) < (j : ℤ) := by exact_mod_cast Nat.lt_of_not_ge h
    nlinarith
  refine ⟨hkn, hjell, ?_, ?_⟩
  · constructor
    · intro hj0
      have hj0Z : (j : ℤ) = 0 := by exact_mod_cast hj0
      have hnk : n = k := by nlinarith
      exact hnk.symm
    · intro hknEq
      have hknEqZ : (k : ℤ) = (n : ℤ) := by exact_mod_cast hknEq
      have hj0Z : (j : ℤ) = 0 := by nlinarith
      exact_mod_cast hj0Z
  · constructor
    · intro hjellEq
      have hjellEqZ : (j : ℤ) = (ell : ℤ) := by exact_mod_cast hjellEq
      have hk1Z : (k : ℤ) = 1 := by nlinarith
      exact_mod_cast hk1Z
    · intro hk1
      have hk1Z : (k : ℤ) = 1 := by exact_mod_cast hk1
      have hjellZ : (j : ℤ) = (ell : ℤ) := by nlinarith
      exact_mod_cast hjellZ

/-- A non-endpoint nonlinear fibre is forced strictly between the highest and
locked heights. -/
theorem prVGreaterOne_wallSlope_strictInterior
    (ell n k j : ℕ)
    (hell : 0 < ell) (hn : 2 ≤ n) (hk : 1 < k) (hkn : k ≠ n)
    (hslope :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    1 < k ∧ k < n ∧ 0 < j ∧ j < ell := by
  rcases prVGreaterOne_wallSlope_bounds ell n k j hell hn (by omega) hslope with
    ⟨hkle, hjle, hj0, hjell⟩
  have hklt : k < n := lt_of_le_of_ne hkle hkn
  have hjpos : 0 < j := by
    by_contra h
    have : j = 0 := by omega
    exact hkn (hj0.mp this)
  have hjlt : j < ell := by
    apply lt_of_le_of_ne hjle
    intro heq
    have hk1 := hjell.mp heq
    omega
  exact ⟨hk, hklt, hjpos, hjlt⟩

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Source-facing endpoint classification for a left-oriented staircase point
of the actual carrier. -/
theorem QsOtherFacetPrLeftVContactFrontierData.wallSlope_bounds
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {e : Fin 4 →₀ ℕ} {k j : ℕ}
    (he : e ∈ P.carrier.support)
    (he0 : e 0 = 0) (he1 : e 1 = k)
    (he2 : e 2 = j + 1) (he3 : e 3 = F.V * (k + j))
    (hk : 1 ≤ k) :
    k ≤ F.highest.n ∧ j ≤ F.locked.ell ∧
      (j = 0 ↔ k = F.highest.n) ∧
      (j = F.locked.ell ↔ k = 1) := by
  exact prVGreaterOne_wallSlope_bounds
    F.locked.ell F.highest.n k j F.locked.ell_pos
    F.highest.n_two_le hk (F.wallSlope_eq he he0 he1 he2 he3)

/-- Symmetric source-facing endpoint classification. -/
theorem QsOtherFacetPrRightVContactFrontierData.wallSlope_bounds
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    {e : Fin 4 →₀ ℕ} {k j : ℕ}
    (he : e ∈ P.carrier.support)
    (he0 : e 0 = 0) (he1 : e 1 = k)
    (he2 : e 2 = F.V * (k + j)) (he3 : e 3 = j + 1)
    (hk : 1 ≤ k) :
    k ≤ F.highest.n ∧ j ≤ F.locked.ell ∧
      (j = 0 ↔ k = F.highest.n) ∧
      (j = F.locked.ell ↔ k = 1) := by
  exact prVGreaterOne_wallSlope_bounds
    F.locked.ell F.highest.n k j F.locked.ell_pos
    F.highest.n_two_le hk (F.wallSlope_eq he he0 he1 he2 he3)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
