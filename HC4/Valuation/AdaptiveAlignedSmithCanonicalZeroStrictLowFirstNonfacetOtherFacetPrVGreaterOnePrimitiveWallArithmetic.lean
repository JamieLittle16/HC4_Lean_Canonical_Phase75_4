import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneWallSlopeConsequences
import Mathlib.Tactic

/-!
# A19 primitive non-unit PR wall arithmetic

The source wall equation alone can contain intermediate lattice points when
`n-1` and `ell` have a common divisor.  The paper classification uses one
additional, genuinely geometric input: the quotient/contact step is primitive,
so `n-1` and `ell` are coprime.

This file isolates the arithmetic consequence.  It deliberately does **not**
manufacture the coprimality hypothesis from the planar wall.  The next
source-facing adapter must derive it from the retained primitive
quotient/contact data.
-/

namespace HC4.Valuation

noncomputable section

/-- A primitive integer segment admits no strict lattice point satisfying the
A19 wall interpolation equation.

The endpoint `k=n` is the primitive highest pair (`j=0`), while `k=1` is the
locked source ray (`j=ell`). -/
theorem prVGreaterOne_wallSlope_endpoints_of_coprime
    (ell n k j : ℕ)
    (hn : 2 ≤ n)
    (hk_one : 1 ≤ k)
    (hk_n : k ≤ n)
    (hcop : Nat.Coprime (n - 1) ell)
    (hslope : (n - 1) * j = ell * (n - k)) :
    (k = n ∧ j = 0) ∨ (k = 1 ∧ j = ell) := by
  have hnsub_pos : 0 < n - 1 := by omega
  have hdiv_prod : n - 1 ∣ ell * (n - k) := by
    exact ⟨j, hslope.symm⟩
  have hdiv : n - 1 ∣ n - k := by
    exact hcop.dvd_of_dvd_mul_left hdiv_prod
  rcases hdiv with ⟨t, ht⟩
  have hnk_le : n - k ≤ n - 1 := by omega
  have hmul_le : (n - 1) * t ≤ (n - 1) * 1 := by
    rw [← ht]
    simpa using hnk_le
  have ht_le : t ≤ 1 :=
    Nat.le_of_mul_le_mul_left hmul_le hnsub_pos
  have ht_cases : t = 0 ∨ t = 1 := by omega
  rcases ht_cases with rfl | rfl
  · left
    have hk : k = n := by simpa using ht
    subst k
    have hzero : (n - 1) * j = 0 := by simpa using hslope
    have hj : j = 0 :=
      (Nat.mul_eq_zero.mp hzero).resolve_left (Nat.ne_of_gt hnsub_pos)
    exact ⟨rfl, hj⟩
  · right
    have hk : k = 1 := by
      have : n - k = n - 1 := by simpa using ht
      omega
    subst k
    have hsame : (n - 1) * j = (n - 1) * ell := by
      simpa [Nat.mul_comm] using hslope
    have hj : j = ell := Nat.mul_left_cancel hnsub_pos hsame
    exact ⟨rfl, hj⟩

/-- Integer-coordinate wrapper matching `wallSlope_eq`.  The bound hypotheses
are exactly those already supplied by `WallSlopeConsequences`; no new geometry
is hidden in the cast conversion. -/
theorem prVGreaterOne_wallSlope_endpoints_of_coprime_int
    (ell n k j : ℕ)
    (hn : 2 ≤ n)
    (hk_one : 1 ≤ k)
    (hk_n : k ≤ n)
    (hcop : Nat.Coprime (n - 1) ell)
    (hslope :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    (k = n ∧ j = 0) ∨ (k = 1 ∧ j = ell) := by
  have hn_one : 1 ≤ n := by omega
  have hslope' :
      (((n - 1 : ℕ) : ℤ) * (j : ℤ)) =
        (ell : ℤ) * (((n - k : ℕ) : ℤ)) := by
    rw [Nat.cast_sub hn_one, Nat.cast_one, Nat.cast_sub hk_n]
    exact hslope
  have hslopeNat : (n - 1) * j = ell * (n - k) := by
    exact_mod_cast hslope'
  exact prVGreaterOne_wallSlope_endpoints_of_coprime
    ell n k j hn hk_one hk_n hcop hslopeNat

end

end HC4.Valuation
