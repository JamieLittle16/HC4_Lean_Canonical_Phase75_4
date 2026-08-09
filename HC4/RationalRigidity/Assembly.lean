import HC4.RationalRigidity.DenominatorClearing

/-!
# Assembly of the HC4 rational-rigidity bridge

The preceding denominator-clearing module converts a pointwise rational
identity into a pointwise polynomial identity.  This module performs the next
logical step: when the chart parameter reaches every scalar, pointwise equality
of evaluations determines equality of the underlying univariate polynomials.

The important hypotheses are deliberately explicit:

* the coefficient field is infinite, so polynomial functions determine
  polynomials;
* the parameter map is surjective, so every scalar value is represented;
* the upstream pole-removal argument has identified the denominator with a
  nonzero constant polynomial, or with the unit polynomial.

No pole-removal, chart geometry, or classification theorem is assumed here.
Those results must be supplied by earlier modules in the full HC4 development.
-/

namespace HC4.RationalRigidity

open Polynomial

section InfiniteField

variable {K : Type*} [Field K] [Infinite K]

/--
Evaluation on a surjective parametrisation determines a polynomial over an
infinite field.
-/
theorem polynomial_eq_of_surjective_eval
    {S : Type*}
    (P Q : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hEval : ∀ s, P.eval (y s) = Q.eval (y s)) :
    P = Q := by
  apply Polynomial.funext
  intro t
  obtain ⟨s, rfl⟩ := hy t
  exact hEval s

/--
A rational identity with a nonzero constant denominator becomes a polynomial
identity once the parameter is surjective.
-/
theorem polynomial_identity_of_constant_denominator
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (d : K) (hd : d ≠ 0)
    (hD : D = C d)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = P.eval (y s)) :
    N = C d * P := by
  apply polynomial_eq_of_surjective_eval N (C d * P) y hy
  intro s
  have hClear :=
    clear_constant_polynomial_denominator
      N D d (y s) (P.eval (y s)) hD hd (hRat s)
  simpa [mul_comm] using hClear

/--
The unit-denominator form: a pointwise rational identity on a surjective chart
is equality of the numerator polynomial with the target polynomial.
-/
theorem polynomial_identity_of_unit_denominator
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hD : D = 1)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = P.eval (y s)) :
    N = P := by
  apply polynomial_eq_of_surjective_eval N P y hy
  intro s
  exact eliminate_unit_polynomial_denominator
    N D (y s) (P.eval (y s)) hD (hRat s)

/--
Specialisation to the power target.  If the rational identity is

    N(y) / D(y) = y^m

on a surjective parameter and `D = C d`, then

    N = C d * X^m.
-/
theorem power_polynomial_identity_of_constant_denominator
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (d : K) (hd : d ≠ 0) (m : ℕ)
    (hD : D = C d)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = (y s) ^ m) :
    N = C d * X ^ m := by
  apply polynomial_identity_of_constant_denominator N D (X ^ m) y hy d hd hD
  intro s
  simpa using hRat s

/--
Normalised power form.  Under a unit denominator, the numerator is exactly the
monomial `X^m`.
-/
theorem power_polynomial_identity_of_unit_denominator
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (m : ℕ)
    (hD : D = 1)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = (y s) ^ m) :
    N = X ^ m := by
  apply polynomial_identity_of_unit_denominator N D (X ^ m) y hy hD
  intro s
  simpa using hRat s

/--
A convenient packaged conclusion of the constant-denominator branch: it records
both the denominator and numerator classifications.
-/
theorem rational_power_pair_of_constant_denominator
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (d : K) (hd : d ≠ 0) (m : ℕ)
    (hD : D = C d)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = (y s) ^ m) :
    D = C d ∧ N = C d * X ^ m := by
  refine ⟨hD, ?_⟩
  exact power_polynomial_identity_of_constant_denominator
    N D y hy d hd m hD hRat

/--
The corresponding packaged conclusion after normalising the denominator to
one.
-/
theorem rational_power_pair_of_unit_denominator
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (m : ℕ)
    (hD : D = 1)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = (y s) ^ m) :
    D = 1 ∧ N = X ^ m := by
  refine ⟨hD, ?_⟩
  exact power_polynomial_identity_of_unit_denominator
    N D y hy m hD hRat

end InfiniteField

end HC4.RationalRigidity
