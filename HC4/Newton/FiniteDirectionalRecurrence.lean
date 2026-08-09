import HC4.Newton.DirectionalCoefficientRecurrence
import Mathlib.Tactic

/-!
# Uniqueness for the finite directional coefficient recurrence

Phase 91.6 extracted the coefficient relation satisfied by every frozen
external slice of a polynomial annihilated by a fixed directional
derivative.

For a degree-`n` transverse slice, write `c k` for the coefficient with
`i`-exponent `k` and `j`-exponent `n-k`.  The directional equation gives

    u * (k+1) * c(k+1) + v * (n-k) * c(k) = 0

for `k < n`.

This file proves the finite uniqueness theorem behind the
one-linear-form classification: in characteristic zero, if `u ≠ 0`, this
recurrence and the single endpoint value `c 0` determine the entire slice.

The next phase only needs to exhibit one canonical solution -- the
coefficient sequence of a power of a linear form -- and uniqueness will
identify every HC4 slice with a scalar multiple of it.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- A scalar sequence satisfies the homogeneous directional recurrence of
transverse degree `n`. -/
def SatisfiesDirectionalRecurrence
    (u v : K) (n : ℕ) (c : ℕ → K) : Prop :=
  ∀ k, k < n ->
    (u * ((k + 1 : ℕ) : K)) * c (k + 1) +
      (v * ((n - k : ℕ) : K)) * c k = 0

/-- The zero sequence satisfies every directional recurrence. -/
theorem zero_satisfiesDirectionalRecurrence
    (u v : K) (n : ℕ) :
    SatisfiesDirectionalRecurrence u v n (fun _ => (0 : K)) := by
  intro k hk
  simp

/-- **Finite recurrence uniqueness.**
Over a characteristic-zero field, if the coefficient of `c(k+1)` has
nonzero direction scalar `u`, then the recurrence and `c 0` determine all
coefficients through degree `n`. -/
theorem directionalRecurrence_unique
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    (n : ℕ)
    (c d : ℕ → K)
    (hc : SatisfiesDirectionalRecurrence u v n c)
    (hd : SatisfiesDirectionalRecurrence u v n d)
    (hzero : c 0 = d 0) :
    ∀ k, k ≤ n -> c k = d k := by
  intro k hk
  induction k with
  | zero =>
      exact hzero
  | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      have hprev : c k = d k :=
        ih (Nat.le_of_lt hklt)
      have hmult : (((k + 1 : ℕ) : K)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      have hden :
          u * ((k + 1 : ℕ) : K) ≠ 0 :=
        mul_ne_zero hu hmult
      have hcRel := hc k hklt
      have hdRel := hd k hklt
      have hcNext :
          (u * ((k + 1 : ℕ) : K)) * c (k + 1) =
            - ((v * ((n - k : ℕ) : K)) * c k) := by
        linear_combination hcRel
      have hdNext :
          (u * ((k + 1 : ℕ) : K)) * d (k + 1) =
            - ((v * ((n - k : ℕ) : K)) * d k) := by
        linear_combination hdRel
      have hmul :
          (u * ((k + 1 : ℕ) : K)) * c (k + 1) =
            (u * ((k + 1 : ℕ) : K)) * d (k + 1) := by
        calc
          (u * ((k + 1 : ℕ) : K)) * c (k + 1) =
              - ((v * ((n - k : ℕ) : K)) * c k) := hcNext
          _ = - ((v * ((n - k : ℕ) : K)) * d k) := by
              rw [hprev]
          _ = (u * ((k + 1 : ℕ) : K)) * d (k + 1) :=
              hdNext.symm
      have hprod :
          (u * ((k + 1 : ℕ) : K)) *
              (c (k + 1) - d (k + 1)) = 0 := by
        calc
          (u * ((k + 1 : ℕ) : K)) *
                (c (k + 1) - d (k + 1)) =
              (u * ((k + 1 : ℕ) : K)) * c (k + 1) -
                (u * ((k + 1 : ℕ) : K)) * d (k + 1) := by
              ring
          _ = 0 := sub_eq_zero.mpr hmul
      have hdiff : c (k + 1) - d (k + 1) = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hden
      exact sub_eq_zero.mp hdiff

/-- Endpoint-zero propagation: a recurrence solution with zero left
endpoint vanishes identically through degree `n`. -/
theorem directionalRecurrence_eq_zero_of_endpoint_zero
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    (n : ℕ)
    (c : ℕ → K)
    (hc : SatisfiesDirectionalRecurrence u v n c)
    (hzero : c 0 = 0) :
    ∀ k, k ≤ n -> c k = 0 := by
  intro k hk
  have huniq :=
    directionalRecurrence_unique
      u v hu n c (fun _ => (0 : K))
      hc (zero_satisfiesDirectionalRecurrence u v n)
      (by simpa using hzero)
  simpa using huniq k hk

/-- If two recurrence solutions agree at the right endpoint as well as
satisfying the recurrence with `u ≠ 0`, the left-endpoint hypothesis is
still the only input needed for equality.  This wrapper is convenient when
both endpoint values are already present in a homogeneous-slice package. -/
theorem directionalRecurrence_unique_of_leftEndpoint
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    (n : ℕ)
    (c d : ℕ → K)
    (hc : SatisfiesDirectionalRecurrence u v n c)
    (hd : SatisfiesDirectionalRecurrence u v n d)
    (hleft : c 0 = d 0) :
    ∀ k ≤ n, c k = d k :=
  directionalRecurrence_unique u v hu n c d hc hd hleft

end

end HC4.Newton
