import HC4.Newton.FiniteDirectionalRecurrence
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The linear-form power profile solves the directional recurrence

Phase 91.7 proves uniqueness for the finite recurrence

    u*(k+1)*c(k+1) + v*(n-k)*c(k) = 0.

The canonical degree-`n` solution is the coefficient profile of

    (v*X - u*Y)^n:

    c(k) = choose(n,k) * v^k * (-u)^(n-k).

This file proves directly that this binomial profile satisfies the same
recurrence.  The only combinatorial input is the standard identity

    choose(n,k+1) * (k+1) = choose(n,k) * (n-k).

Consequently every scalar multiple of the profile also satisfies the
recurrence.  Together with Phase 91.7, this reduces the one-linear-form
classification to matching one endpoint coefficient on each frozen
external slice.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Coefficient profile of the binary linear-form power
`(v*X - u*Y)^n`, indexed by the exponent of `X`. -/
def linearPowerProfile
    (u v : K) (n k : ℕ) : K :=
  (Nat.choose n k : K) * v ^ k * (-u) ^ (n - k)

/-- The left endpoint of the linear-power profile. -/
@[simp] theorem linearPowerProfile_zero
    (u v : K) (n : ℕ) :
    linearPowerProfile u v n 0 = (-u) ^ n := by
  simp [linearPowerProfile]

/-- The right endpoint of the linear-power profile. -/
@[simp] theorem linearPowerProfile_self
    (u v : K) (n : ℕ) :
    linearPowerProfile u v n n = v ^ n := by
  simp [linearPowerProfile]

/-- The binomial coefficient profile of `(v*X-u*Y)^n` satisfies the
directional recurrence. -/
theorem linearPowerProfile_satisfiesDirectionalRecurrence
    (u v : K) (n : ℕ) :
    SatisfiesDirectionalRecurrence
      u v n (linearPowerProfile u v n) := by
  intro k hk
  have hchooseNat := Nat.choose_succ_right_eq n k
  have hchoose :
      ((Nat.choose n (k + 1) : ℕ) : K) *
          (((k + 1 : ℕ) : K)) =
        ((Nat.choose n k : ℕ) : K) *
          (((n - k : ℕ) : K)) := by
    have hcast :=
      congrArg (fun t : ℕ => (t : K)) hchooseNat
    simpa only [Nat.cast_mul] using hcast
  have hv :
      v ^ (k + 1) = v ^ k * v := by
    rw [pow_succ]
  have hsub :
      n - k = (n - (k + 1)) + 1 := by
    omega
  have huPow :
      (-u) ^ (n - k) =
        (-u) ^ (n - (k + 1)) * (-u) := by
    rw [hsub, pow_succ]
  unfold linearPowerProfile
  rw [hv, huPow]
  calc
    (u * (((k + 1 : ℕ) : K))) *
          (((Nat.choose n (k + 1) : ℕ) : K) *
            (v ^ k * v) *
            (-u) ^ (n - (k + 1))) +
        (v * (((n - k : ℕ) : K))) *
          (((Nat.choose n k : ℕ) : K) *
            v ^ k *
            ((-u) ^ (n - (k + 1)) * (-u))) =
      u *
          (((Nat.choose n (k + 1) : ℕ) : K) *
            (((k + 1 : ℕ) : K))) *
          (v ^ k * v * (-u) ^ (n - (k + 1))) +
        (((Nat.choose n k : ℕ) : K) *
            (((n - k : ℕ) : K))) *
          (v ^ k * v * (-u) ^ (n - (k + 1))) *
          (-u) := by
      ring
    _ =
      u *
          (((Nat.choose n k : ℕ) : K) *
            (((n - k : ℕ) : K))) *
          (v ^ k * v * (-u) ^ (n - (k + 1))) +
        (((Nat.choose n k : ℕ) : K) *
            (((n - k : ℕ) : K))) *
          (v ^ k * v * (-u) ^ (n - (k + 1))) *
          (-u) := by
      rw [hchoose]
    _ = 0 := by
      ring

/-- Scalar multiples of the linear-power profile satisfy the same
homogeneous recurrence. -/
theorem smulLinearPowerProfile_satisfiesDirectionalRecurrence
    (a u v : K) (n : ℕ) :
    SatisfiesDirectionalRecurrence
      u v n (fun k => a * linearPowerProfile u v n k) := by
  intro k hk
  have hbase :=
    linearPowerProfile_satisfiesDirectionalRecurrence
      (K := K) u v n k hk
  calc
    (u * (((k + 1 : ℕ) : K))) *
          (a * linearPowerProfile u v n (k + 1)) +
        (v * (((n - k : ℕ) : K))) *
          (a * linearPowerProfile u v n k) =
      a *
        ((u * (((k + 1 : ℕ) : K))) *
            linearPowerProfile u v n (k + 1) +
          (v * (((n - k : ℕ) : K))) *
            linearPowerProfile u v n k) := by
      ring
    _ = 0 := by
      rw [hbase]
      simp

end

end HC4.Newton
