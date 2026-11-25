import HC4.Polynomial.RationalCharacteristicRankOneTraceLift

/-!
# Rank-one Hessian obstruction in the affine parameter chart

In the normalized chart t = x/y, write F(t,y,z) = f(ty,y,z).
The coefficient P(j,l) of y^j z^l is a polynomial in t of degree
at most j. Symmetry of the Hessian times the rank-one Jacobian
will give the coefficient recurrence for the directional derivative
U1(t) F_y + U2(t) F_z to be independent of y,z.

Instead of choosing the highest z degree of F, treat each homogeneous
degree in y,z separately. The recurrence at y degree zero, together
with independence of U0 = t U1, U1 and U2, kills the pure z term.
Induction on the y degree kills all other terms of that degree.

This module proves the coefficient obstruction. The affine coordinate
change, chart coefficient extraction, and derivation of the recurrence
from the Hessian symmetry identity are separate source obligations.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

/-- A polynomial of degree at most one has this explicit coefficient
representation. -/
private theorem rankOne_parameter_eq_linear
    (P : _root_.Polynomial K) (hP : P.natDegree ≤ 1) :
    P = _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X +
      _root_.Polynomial.C (P.coeff 0) := by
  apply _root_.Polynomial.ext
  intro n
  rcases n with _ | n
  · simp [_root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul_X]
  rcases n with _ | n
  · simp [_root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul_X]
  · have hn : P.natDegree < n + 2 := by omega
    rw [_root_.Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    simp [_root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul_X,
      _root_.Polynomial.coeff_C]

variable [CharZero K]

/-- The coefficient recurrence in the normalized affine rank-one
chart kills every coefficient of total y,z degree at least two.
Only the degree bounds at y degrees zero and one are necessary. -/
theorem rankOne_chart_coefficients_zero_of_independent
    (U0 U1 U2 : _root_.Polynomial K)
    (P : ℕ → ℕ → _root_.Polynomial K)
    (hU : U0 = _root_.Polynomial.X * U1)
    (hind : ∀ a b c : K,
      _root_.Polynomial.C a * U0 + _root_.Polynomial.C b * U1 +
        _root_.Polynomial.C c * U2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hP0 : ∀ l : ℕ, (P 0 l).natDegree = 0)
    (hP1 : ∀ l : ℕ, (P 1 l).natDegree ≤ 1)
    (hrec : ∀ j l : ℕ, 1 ≤ j + l →
      _root_.Polynomial.C ((j + 1 : ℕ) : K) * U1 * P (j + 1) l +
        _root_.Polynomial.C ((l + 1 : ℕ) : K) * U2 * P j (l + 1) = 0) :
    ∀ j l : ℕ, 2 ≤ j + l → P j l = 0 := by
  have hU1 : U1 ≠ 0 := by
    intro hz
    have h := hind 0 1 0 (by simp [hz])
    exact one_ne_zero h.2.1
  intro j
  induction j with
  | zero =>
    intro l hl
    cases l with
    | zero => omega
    | succ l =>
      have h := hrec 0 l (by omega)
      have hc : P 0 (l + 1) = _root_.Polynomial.C ((P 0 (l + 1)).coeff 0) :=
        _root_.Polynomial.eq_C_of_natDegree_eq_zero (hP0 (l + 1))
      have ha := rankOne_parameter_eq_linear (P 1 l) (hP1 l)
      simp only [zero_add, Nat.cast_one, map_one, one_mul] at h
      rw [ha, hc] at h
      have hrel :
          _root_.Polynomial.C ((P 1 l).coeff 1) * U0 +
            _root_.Polynomial.C ((P 1 l).coeff 0) * U1 +
            _root_.Polynomial.C (((l + 1 : ℕ) : K) * (P 0 (l + 1)).coeff 0) * U2 = 0 := by
        rw [hU, map_mul]
        linear_combination h
      have hh := (hind _ _ _ hrel).2.2
      have hcast : (((l + 1 : ℕ) : K)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero l)
      have hcz := (mul_eq_zero.mp hh).resolve_left hcast
      change P 0 (l + 1) = 0
      rw [hc, hcz, map_zero]
  | succ j ih =>
    intro l hl
    have h := hrec j l (by omega)
    have hz : P j (l + 1) = 0 := ih (l + 1) (by omega)
    rw [hz, mul_zero, add_zero] at h
    have hcast : (((j + 1 : ℕ) : K)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
    exact (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (_root_.Polynomial.C_ne_zero.mpr hcast) hU1)

/-- Finite support in the y,z chart is not required for the obstruction:
the recurrence and independence leave only an affine coefficient family. -/
theorem rankOne_chart_coefficients_affine_of_independent
    (U0 U1 U2 : _root_.Polynomial K)
    (P : ℕ → ℕ → _root_.Polynomial K)
    (hU : U0 = _root_.Polynomial.X * U1)
    (hind : ∀ a b c : K,
      _root_.Polynomial.C a * U0 + _root_.Polynomial.C b * U1 +
        _root_.Polynomial.C c * U2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hP0 : ∀ l : ℕ, (P 0 l).natDegree = 0)
    (hP1 : ∀ l : ℕ, (P 1 l).natDegree ≤ 1)
    (hrec : ∀ j l : ℕ, 1 ≤ j + l →
      _root_.Polynomial.C ((j + 1 : ℕ) : K) * U1 * P (j + 1) l +
        _root_.Polynomial.C ((l + 1 : ℕ) : K) * U2 * P j (l + 1) = 0) :
    ∀ j l : ℕ, P j l =
      if j = 0 ∧ l = 0 then _root_.Polynomial.C ((P 0 0).coeff 0)
      else if j = 1 ∧ l = 0 then
        _root_.Polynomial.C ((P 1 0).coeff 1) * _root_.Polynomial.X +
          _root_.Polynomial.C ((P 1 0).coeff 0)
      else if j = 0 ∧ l = 1 then _root_.Polynomial.C ((P 0 1).coeff 0)
      else 0 := by
  intro j l
  split_ifs with h0 h1 h2
  · obtain ⟨rfl, rfl⟩ := h0
    exact _root_.Polynomial.eq_C_of_natDegree_eq_zero (hP0 0)
  · obtain ⟨rfl, rfl⟩ := h1
    exact rankOne_parameter_eq_linear (P 1 0) (hP1 0)
  · obtain ⟨rfl, rfl⟩ := h2
    exact _root_.Polynomial.eq_C_of_natDegree_eq_zero (hP0 1)
  · apply rankOne_chart_coefficients_zero_of_independent U0 U1 U2 P hU hind hP0 hP1 hrec
    omega

end
end HC4.Polynomial.RankThreeCubic
