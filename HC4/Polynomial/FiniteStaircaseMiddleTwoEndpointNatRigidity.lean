import HC4.Polynomial.FiniteStaircaseMiddleTwoEndpointRigidity
import Mathlib.Tactic

/-!
# Natural-parameter wrapper for middle two-endpoint rigidity

The A19 application carries `V,n,ell,k` as natural-number exponents.  This
wrapper discharges all characteristic-zero cast nonvanishing required by the
state-free field-valued rigidity theorem.
-/

namespace HC4.Polynomial

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **Natural middle rigidity.**  In the live positive range, simultaneous
vanishing of the highest- and locked-end second variations forces the lower
translated mode coefficient to vanish. -/
theorem middleLowerMode_eq_zero_of_twoEndpoint_secondVariations_nat
    (V n ell k : ℕ) (a b u0 v0 : K)
    (hV : 1 < V)
    (hn : 2 ≤ n)
    (hell : 0 < ell)
    (hk : 1 < k)
    (hnell : n ≤ ell)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hHigh :
      TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (middleHighestSecondJet (V : K) (n : K) (k : K)
            a u0 v0).det) = 0)
    (hLock :
      TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (middleLockedSecondJet (V : K) (ell : K) (k : K)
            b u0 v0).det) = 0) :
    u0 = 0 := by
  have h8 : (8 : K) ≠ 0 := by norm_num
  have hVK : (V : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hVp1 : (V : K) + 1 ≠ 0 := by
    have h : ((V + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa [Nat.cast_add] using h
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1K : (n : K) - 1 ≠ 0 := by
    have h : ((n - 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa [Nat.cast_sub (by omega : 1 ≤ n)] using h
  have hellK : (ell : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hellp1 : (ell : K) + 1 ≠ 0 := by
    have h : ((ell + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa [Nat.cast_add] using h
  have hk1K : (k : K) - 1 ≠ 0 := by
    have h : ((k - 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa [Nat.cast_sub (by omega : 1 ≤ k)] using h
  have hsepTerm : (ell : K) - (n : K) + 1 ≠ 0 := by
    have hnat : 0 < ell - n + 1 := by omega
    have hcast : ((ell - n + 1 : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnat)
    rw [Nat.cast_add, Nat.cast_sub hnell] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hHighPref :
      8 * (V : K) * ((V : K) + 1) * a ^ 2 * (n : K) ^ 2 *
          ((n : K) - 1) ^ 2 * ((k : K) - 1) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero h8 hVK) hVp1)
              (pow_ne_zero 2 ha))
            (pow_ne_zero 2 hnK))
          (pow_ne_zero 2 hn1K))
      hk1K
  have hLockPref :
      8 * (V : K) * ((V : K) + 1) * b ^ 2 * (ell : K) ^ 2 *
          ((ell : K) + 1) ^ 2 * ((k : K) - 1) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero h8 hVK) hVp1)
              (pow_ne_zero 2 hb))
            (pow_ne_zero 2 hellK))
          (pow_ne_zero 2 hellp1))
      hk1K
  have hSep :
      ((k : K) - 1) * ((ell : K) - (n : K) + 1) ≠ 0 :=
    mul_ne_zero hk1K hsepTerm
  exact middleLowerMode_eq_zero_of_twoEndpoint_secondVariations
    (V : K) (n : K) (ell : K) (k : K) a b u0 v0
    hHighPref hLockPref hSep hHigh hLock

end

end HC4.Polynomial
