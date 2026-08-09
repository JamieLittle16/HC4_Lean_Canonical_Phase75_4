import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# The Euler equation in the toric-facet classification

After the degree obstruction has shown that a facet polynomial is linear in
`p` or `q`, the determinant-one equation reduces to

    (C + n X C')² = 1,

with constant coefficient `C(0)=1`.  In characteristic zero this forces
`C=1`.  This module proves that univariate rigidity independently of the
preceding Hessian calculation.
-/

namespace HC4.FacetRigidity

open Polynomial

/-- The weighted Euler operator `C ↦ C + n X C'`. -/
noncomputable def eulerLinear {K : Type*} [Semiring K] (n : ℕ) (C : K[X]) : K[X] :=
  C + Polynomial.C (n : K) * (Polynomial.X * C.derivative)

@[simp] theorem coeff_eulerLinear_zero
    {K : Type*} [Semiring K] (n : ℕ) (C : K[X]) :
    (eulerLinear n C).coeff 0 = C.coeff 0 := by
  simp [eulerLinear]

/-- Coefficient formula for the positive-degree part of the Euler operator. -/
theorem coeff_eulerLinear_succ
    {K : Type*} [CommSemiring K] (n k : ℕ) (C : K[X]) :
    (eulerLinear n C).coeff (k + 1) =
      C.coeff (k + 1) +
        (n : K) * (C.coeff (k + 1) * (k + 1 : ℕ)) := by
  simp [eulerLinear, Polynomial.coeff_derivative]

/-- In characteristic zero, `C + nXC' = 1` forces `C=1`. -/
theorem eulerLinear_eq_one
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (_hn : 0 < n) (C : K[X])
    (h : eulerLinear n C = 1) :
    C = 1 := by
  ext k
  cases k with
  | zero =>
      have h0 := congrArg (fun P : K[X] => P.coeff 0) h
      change (eulerLinear n C).coeff 0 = (1 : K[X]).coeff 0 at h0
      simpa using h0
  | succ k =>
      have hkOne : (1 : K[X]).coeff (k + 1) = 0 := by
        rw [Polynomial.coeff_one]
        simp
      have hkRaw := congrArg (fun P : K[X] => P.coeff (k + 1)) h
      change (eulerLinear n C).coeff (k + 1) = (1 : K[X]).coeff (k + 1) at hkRaw
      rw [coeff_eulerLinear_succ, hkOne] at hkRaw
      have hNat : 1 + n * (k + 1) ≠ 0 := by omega
      have hFactor :
          (1 + (n : K) * (((k + 1 : ℕ) : K))) ≠ 0 := by
        exact_mod_cast hNat
      have hProd :
          C.coeff (k + 1) *
            (1 + (n : K) * (((k + 1 : ℕ) : K))) = 0 := by
        calc
          C.coeff (k + 1) *
                (1 + (n : K) * (((k + 1 : ℕ) : K))) =
              C.coeff (k + 1) +
                (n : K) *
                  (C.coeff (k + 1) * (((k + 1 : ℕ) : K))) := by ring
          _ = 0 := by
            simpa [Nat.cast_add, Nat.cast_one] using hkRaw
      have hCoeff : C.coeff (k + 1) = 0 :=
        (mul_eq_zero.mp hProd).resolve_right hFactor
      rw [hCoeff, hkOne]

/-- A polynomial square root of `1` with constant coefficient `1` is `1`. -/
theorem eq_one_of_sq_eq_one_of_coeff_zero_eq_one
    {K : Type*} [Field K] [CharZero K]
    {E : K[X]} (hsq : E ^ 2 = 1) (h0 : E.coeff 0 = 1) :
    E = 1 := by
  have hprod : (E - 1) * (E + 1) = 0 := by
    calc
      (E - 1) * (E + 1) = E ^ 2 - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact sub_eq_zero.mp hminus
  · have he : E = -1 := by
      calc
        E = (E + 1) - 1 := by ring
        _ = 0 - 1 := by rw [hplus]
        _ = -1 := by ring
    have hc := congrArg (fun P : K[X] => P.coeff 0) he
    change E.coeff 0 = (-1 : K[X]).coeff 0 at hc
    rw [h0] at hc
    norm_num at hc

/-- The exact facet equation `(C+nXC')²=1`, normalised at zero, forces `C=1`. -/
theorem eulerLinear_eq_one_of_sq_eq_one
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (hn : 0 < n) (C : K[X])
    (hsq : (eulerLinear n C) ^ 2 = 1)
    (h0 : C.coeff 0 = 1) :
    C = 1 := by
  have hE0 : (eulerLinear n C).coeff 0 = 1 := by
    simpa using h0
  have hE : eulerLinear n C = 1 :=
    eq_one_of_sq_eq_one_of_coeff_zero_eq_one hsq hE0
  exact eulerLinear_eq_one n hn C hE

end HC4.FacetRigidity
