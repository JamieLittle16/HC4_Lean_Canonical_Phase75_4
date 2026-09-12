import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# Extremal Hessian coefficient for a line-supported carrier

The final A19 line-rigidity argument only needs the first two extremal
Hessian coefficients.  If the top exponent has one zero coordinate, then the
coefficient which is first order in the next exponent is supported by the
corresponding diagonal Hessian entry.  Its complementary `3 x 3` minor is the
three-variable exponent-Hessian core.

This file isolates the state-free algebraic factorisation used by the later
support adapter.  No Newton, valuation, or JC2 input occurs here.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {R : Type u} [CommRing R]

/-- The `3 x 3` exponent-Hessian core on the complementary coordinates. -/
def exponentHessianMinor3 (u₁ u₂ u₃ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![u₁ * (u₁ - 1), u₁ * u₂,       u₁ * u₃;
     u₁ * u₂,       u₂ * (u₂ - 1), u₂ * u₃;
     u₁ * u₃,       u₂ * u₃,       u₃ * (u₃ - 1)]

/-- Exact determinant of the complementary exponent-Hessian minor. -/
theorem det_exponentHessianMinor3 (u₁ u₂ u₃ : R) :
    (exponentHessianMinor3 u₁ u₂ u₃).det =
      u₁ * u₂ * u₃ * (u₁ + u₂ + u₃ - 1) := by
  rw [Matrix.det_fin_three]
  simp [exponentHessianMinor3]
  ring

/-- The first mixed Hessian-core contribution when the top exponent vanishes
in the distinguished coordinate.  The next exponent contributes only its
second derivative in that coordinate at first order. -/
def firstMixedHessianCoreAtZero
    (u₁ u₂ u₃ v₀ : R) : R :=
  v₀ * (v₀ - 1) * (exponentHessianMinor3 u₁ u₂ u₃).det

/-- Factorisation of the first mixed extremal coefficient. -/
theorem firstMixedHessianCoreAtZero_factor
    (u₁ u₂ u₃ v₀ : R) :
    firstMixedHessianCoreAtZero u₁ u₂ u₃ v₀ =
      u₁ * u₂ * u₃ * v₀ * (v₀ - 1) *
        (u₁ + u₂ + u₃ - 1) := by
  rw [firstMixedHessianCoreAtZero, det_exponentHessianMinor3]
  ring

/-- Characteristic-zero rigidity of the mixed coefficient: for positive
complementary top exponents of total degree at least two, a positive next
exponent in the missing coordinate must equal one. -/
theorem nat_eq_one_of_firstMixedHessianCoreAtZero_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {u₁ u₂ u₃ v₀ : ℕ}
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hu₃ : 0 < u₃)
    (hsum : 2 ≤ u₁ + u₂ + u₃)
    (hv₀ : 0 < v₀)
    (hzero :
      firstMixedHessianCoreAtZero
        (u₁ : K) (u₂ : K) (u₃ : K) (v₀ : K) = 0) :
    v₀ = 1 := by
  rw [firstMixedHessianCoreAtZero_factor] at hzero
  have hu₁K : (u₁ : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu₁)
  have hu₂K : (u₂ : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu₂)
  have hu₃K : (u₃ : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu₃)
  have hsumK : (u₁ : K) + (u₂ : K) + (u₃ : K) - 1 ≠ 0 := by
    intro h
    have hcast : ((u₁ + u₂ + u₃ : ℕ) : K) = 1 := by
      push_cast
      linarith
    have hnat : u₁ + u₂ + u₃ = 1 := by exact_mod_cast hcast
    omega
  have hvfactor : (v₀ : K) * ((v₀ : K) - 1) = 0 := by
    apply (mul_eq_zero.mp ?_)
    · exact hu₁K
    · apply (mul_eq_zero.mp ?_)
      · exact hu₂K
      · apply (mul_eq_zero.mp ?_)
        · exact hu₃K
        · exact hzero
  rcases mul_eq_zero.mp hvfactor with hvzero | hvone
  · have : v₀ = 0 := by exact_mod_cast hvzero
    omega
  · have : (v₀ : K) = 1 := sub_eq_zero.mp hvone
    exact_mod_cast this

end

end HC4.Polynomial
