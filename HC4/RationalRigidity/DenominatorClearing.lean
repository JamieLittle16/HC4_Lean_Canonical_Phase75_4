import Mathlib

/-!
# Denominator clearing for the HC4 rational-rigidity bridge

This module isolates the algebraic assembly step used after the finite- and
infinity-chart arguments have shown that the relevant denominator has no
zeros on the domain under consideration.

The central statement is deliberately pointwise.  If

    N(y x) / D(y x) = (z x)^m

and `D(y x) ≠ 0`, then this rational identity is equivalent to the cleared
polynomial identity

    N(y x) = (z x)^m * D(y x).

No analytic, valuation-theoretic, or pole-removal assertion is hidden here;
those enter only through the non-vanishing hypothesis.
-/

namespace HC4.RationalRigidity

open Polynomial

section Field

variable {K : Type*} [Field K]

/-- Clear one nonzero denominator. -/
theorem clear_denominator {a b c : K} (hb : b ≠ 0) :
    a / b = c ↔ a = c * b :=
  div_eq_iff hb

/-- The two-denominator cross-multiplication equivalence. -/
theorem div_eq_div_iff_cross {a b c d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b := by
  constructor
  · intro h
    field_simp [hb, hd] at h ⊢
    exact h
  · intro h
    field_simp [hb, hd] at h ⊢
    exact h

/-- Clear the denominator after evaluating two polynomials at a point. -/
theorem clear_polynomial_rational_identity
    (N D : K[X]) (y rhs : K)
    (hD : D.eval y ≠ 0) :
    N.eval y / D.eval y = rhs ↔ N.eval y = rhs * D.eval y :=
  div_eq_iff hD

/-- The specialised form used by the cyclic rational-rigidity equation. -/
theorem clear_power_rational_identity
    (N D : K[X]) (y z : K) (m : ℕ)
    (hD : D.eval y ≠ 0) :
    N.eval y / D.eval y = z ^ m ↔
      N.eval y = z ^ m * D.eval y :=
  div_eq_iff hD

/--
Pointwise denominator clearing for a composed rational identity.

This is the assembly theorem needed once the chart arguments supply
`D.eval (y x) ≠ 0` at every point.
-/
theorem clear_power_rational_identity_pointwise
    {X : Type*}
    (N D : K[X]) (y z : X → K) (m : ℕ)
    (hD : ∀ x, D.eval (y x) ≠ 0) :
    (∀ x, N.eval (y x) / D.eval (y x) = (z x) ^ m) ↔
      (∀ x, N.eval (y x) = (z x) ^ m * D.eval (y x)) := by
  constructor
  · intro h x
    exact (clear_power_rational_identity N D (y x) (z x) m (hD x)).mp (h x)
  · intro h x
    exact (clear_power_rational_identity N D (y x) (z x) m (hD x)).mpr (h x)

/-- Extract the cleared identity from the rational one. -/
theorem cleared_identity_of_rational_identity
    {X : Type*}
    (N D : K[X]) (y z : X → K) (m : ℕ)
    (hD : ∀ x, D.eval (y x) ≠ 0)
    (hRat : ∀ x, N.eval (y x) / D.eval (y x) = (z x) ^ m) :
    ∀ x, N.eval (y x) = (z x) ^ m * D.eval (y x) :=
  (clear_power_rational_identity_pointwise N D y z m hD).mp hRat

/-- Reconstruct the rational identity from its cleared form. -/
theorem rational_identity_of_cleared_identity
    {X : Type*}
    (N D : K[X]) (y z : X → K) (m : ℕ)
    (hD : ∀ x, D.eval (y x) ≠ 0)
    (hClear : ∀ x, N.eval (y x) = (z x) ^ m * D.eval (y x)) :
    ∀ x, N.eval (y x) / D.eval (y x) = (z x) ^ m :=
  (clear_power_rational_identity_pointwise N D y z m hD).mpr hClear

/--
If the polynomial denominator has already been identified with a nonzero
constant polynomial, the evaluated denominator can be replaced by that
constant in the cleared identity.
-/
theorem clear_constant_polynomial_denominator
    (N D : K[X]) (d y rhs : K)
    (hD : D = C d) (hd : d ≠ 0)
    (hRat : N.eval y / D.eval y = rhs) :
    N.eval y = rhs * d := by
  subst D
  simpa using (clear_polynomial_rational_identity N (C d) y rhs (by simpa using hd)).mp hRat

/-- A denominator normalised to `1` disappears entirely. -/
theorem eliminate_unit_polynomial_denominator
    (N D : K[X]) (y rhs : K)
    (hD : D = 1)
    (hRat : N.eval y / D.eval y = rhs) :
    N.eval y = rhs := by
  subst D
  simpa using hRat

end Field

end HC4.RationalRigidity
