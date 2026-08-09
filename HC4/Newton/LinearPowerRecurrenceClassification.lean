import HC4.Newton.LinearPowerRecurrence
import Mathlib.Tactic

/-!
# Classification of the finite directional recurrence

Phase 91.7 proves uniqueness for the finite recurrence

    u*(k+1)*c(k+1) + v*(n-k)*c(k) = 0

when `u ≠ 0` over a characteristic-zero field.

Phase 91.8 proves that the binomial profile

    choose(n,k) * v^k * (-u)^(n-k)

of the linear-form power `(v*X-u*Y)^n` satisfies exactly that recurrence.

This file combines those results.

Because the left endpoint of the profile is `(-u)^n`, which is nonzero
when `u ≠ 0`, any recurrence solution `c` has a unique scalar

    a = c(0) / (-u)^n

such that

    c(k) = a * choose(n,k) * v^k * (-u)^(n-k)

for every `k ≤ n`.

This is the scalar-slice theorem underlying the HC4 normal form
`a(X) * L(Y)^n`.  The remaining assembly step is to identify the sequence
`c(k)` with the coefficients of each frozen external multi-index of the
original `MvPolynomial`.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Scalar determined by the left endpoint of a recurrence solution. -/
def linearPowerScalar
    (u : K) (n : ℕ) (c : ℕ → K) : K :=
  c 0 / (-u) ^ n

/-- The chosen scalar matches the left endpoint of the linear-power
profile whenever `u ≠ 0`. -/
theorem linearPowerScalar_mul_profile_zero
    (u v : K)
    (hu : u ≠ 0)
    (n : ℕ)
    (c : ℕ → K) :
    linearPowerScalar u n c *
        linearPowerProfile u v n 0 =
      c 0 := by
  have hneg : -u ≠ 0 := neg_ne_zero.mpr hu
  have hpow : (-u) ^ n ≠ 0 := pow_ne_zero n hneg
  rw [linearPowerProfile_zero]
  unfold linearPowerScalar
  field_simp [hpow]

/-- **Classification of a directional recurrence solution.**
Every solution is the scalar multiple of the coefficient profile of
`(v*X-u*Y)^n` determined by its left endpoint. -/
theorem directionalRecurrence_eq_linearPowerProfile
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    (n : ℕ)
    (c : ℕ → K)
    (hc : SatisfiesDirectionalRecurrence u v n c) :
    ∀ k, k ≤ n ->
      c k =
        linearPowerScalar u n c *
          linearPowerProfile u v n k := by
  let d : ℕ → K :=
    fun k =>
      linearPowerScalar u n c *
        linearPowerProfile u v n k
  have hd : SatisfiesDirectionalRecurrence u v n d := by
    dsimp [d]
    exact
      smulLinearPowerProfile_satisfiesDirectionalRecurrence
        (linearPowerScalar u n c) u v n
  have hleft : c 0 = d 0 := by
    dsimp [d]
    exact
      (linearPowerScalar_mul_profile_zero
        u v hu n c).symm
  exact
    directionalRecurrence_unique
      u v hu n c d hc hd hleft

/-- Existential form of the recurrence classification. -/
theorem exists_scalar_directionalRecurrence_eq_linearPowerProfile
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    (n : ℕ)
    (c : ℕ → K)
    (hc : SatisfiesDirectionalRecurrence u v n c) :
    ∃ a : K, ∀ k, k ≤ n ->
      c k = a * linearPowerProfile u v n k := by
  refine ⟨linearPowerScalar u n c, ?_⟩
  exact directionalRecurrence_eq_linearPowerProfile
    u v hu n c hc

/-- Expanded binomial form of the classification. -/
theorem directionalRecurrence_eq_binomialProfile
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    (n : ℕ)
    (c : ℕ → K)
    (hc : SatisfiesDirectionalRecurrence u v n c) :
    ∀ k, k ≤ n ->
      c k =
        linearPowerScalar u n c *
          ((Nat.choose n k : ℕ) : K) *
          v ^ k *
          (-u) ^ (n - k) := by
  intro k hk
  rw [directionalRecurrence_eq_linearPowerProfile
    u v hu n c hc k hk]
  unfold linearPowerProfile
  ring

end

end HC4.Newton
