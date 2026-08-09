import HC4.RationalRigidity.Assembly

/-!
# Algebraic pole-removal assembly for the HC4 rational-rigidity bridge

Phase 9 assumed that an upstream argument had already identified the
univariate denominator with a nonzero constant polynomial.  This module
removes that assumption once nonvanishing is known on every scalar of an
algebraically closed field.

The key algebraic fact is elementary but important: a nonconstant polynomial
over an algebraically closed field has a root.  Consequently, a polynomial
whose evaluation is never zero is a nonzero constant.  Surjectivity of the
chart parameter promotes pointwise nonvanishing on the chart to global
nonvanishing on the coefficient field.

This module still does not prove that the original HC4 chart equations imply
pointwise nonvanishing.  It formalises the exact downstream consequence once
that chart-level hypothesis has been established.
-/

namespace HC4.RationalRigidity

open Polynomial

section AlgebraicallyClosedField

variable {K : Type*} [Field K] [IsAlgClosed K]

/--
A univariate polynomial over an algebraically closed field that never vanishes
is a nonzero constant polynomial.
-/
theorem constant_polynomial_of_eval_ne_zero
    (D : K[X])
    (hD : ∀ x : K, D.eval x ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ D = C d := by
  have hDegree : D.degree = 0 := by
    by_contra hDegree
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root D hDegree
    exact (hD x) hx
  have hConst : D = C (D.coeff 0) :=
    (Polynomial.degree_le_zero_iff).mp (le_of_eq hDegree)
  refine ⟨D.coeff 0, ?_, hConst⟩
  intro hCoeff
  apply hD 0
  rw [hConst]
  simp [hCoeff]

/--
If a chart parameter is surjective and the evaluated denominator is nonzero at
every chart point, then the denominator is a nonzero constant polynomial.
-/
theorem constant_polynomial_of_surjective_eval_ne_zero
    {S : Type*}
    (D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hD : ∀ s, D.eval (y s) ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ D = C d := by
  apply constant_polynomial_of_eval_ne_zero D
  intro t
  obtain ⟨s, rfl⟩ := hy t
  exact hD s

/--
A monic polynomial over an algebraically closed field that never vanishes is
exactly the unit polynomial.
-/
theorem monic_polynomial_eq_one_of_eval_ne_zero
    (D : K[X])
    (hMonic : D.Monic)
    (hD : ∀ x : K, D.eval x ≠ 0) :
    D = 1 := by
  apply (hMonic.degree_le_zero_iff_eq_one).mp
  by_contra hDegree
  have hDegreeNe : D.degree ≠ 0 := by
    intro hZero
    exact hDegree (le_of_eq hZero)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root D hDegreeNe
  exact (hD x) hx

/--
The general polynomial-target rigidity statement with no pre-classified
constant denominator.  Global nonvanishing is obtained from the surjective
chart, after which Phase 9 identifies the numerator.
-/
theorem rational_identity_of_nonvanishing_denominator
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hD : ∀ s, D.eval (y s) ≠ 0)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = P.eval (y s)) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * P := by
  obtain ⟨d, hd, hConst⟩ :=
    constant_polynomial_of_surjective_eval_ne_zero D y hy hD
  refine ⟨d, hd, hConst, ?_⟩
  exact polynomial_identity_of_constant_denominator
    N D P y hy d hd hConst hRat

/--
Power-target rigidity without assuming in advance that the denominator is
constant.
-/
theorem rational_power_pair_of_nonvanishing_denominator
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (m : ℕ)
    (hD : ∀ s, D.eval (y s) ≠ 0)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = (y s) ^ m) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * X ^ m := by
  obtain ⟨d, hd, hConst⟩ :=
    constant_polynomial_of_surjective_eval_ne_zero D y hy hD
  refine ⟨d, hd, hConst, ?_⟩
  exact power_polynomial_identity_of_constant_denominator
    N D y hy d hd m hConst hRat

/--
If the denominator is monic, nonvanishing normalises it automatically to one,
and the numerator equals the target polynomial.
-/
theorem rational_identity_of_monic_nonvanishing_denominator
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hMonic : D.Monic)
    (hD : ∀ s, D.eval (y s) ≠ 0)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = P.eval (y s)) :
    D = 1 ∧ N = P := by
  have hGlobal : ∀ t : K, D.eval t ≠ 0 := by
    intro t
    obtain ⟨s, rfl⟩ := hy t
    exact hD s
  have hUnit : D = 1 :=
    monic_polynomial_eq_one_of_eval_ne_zero D hMonic hGlobal
  refine ⟨hUnit, ?_⟩
  exact polynomial_identity_of_unit_denominator N D P y hy hUnit hRat

/--
The fully normalised power-target conclusion: a monic nonvanishing denominator
is one and the numerator is the monomial `X^m`.
-/
theorem rational_power_pair_of_monic_nonvanishing_denominator
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (m : ℕ)
    (hMonic : D.Monic)
    (hD : ∀ s, D.eval (y s) ≠ 0)
    (hRat : ∀ s, N.eval (y s) / D.eval (y s) = (y s) ^ m) :
    D = 1 ∧ N = X ^ m := by
  have hGlobal : ∀ t : K, D.eval t ≠ 0 := by
    intro t
    obtain ⟨s, rfl⟩ := hy t
    exact hD s
  have hUnit : D = 1 :=
    monic_polynomial_eq_one_of_eval_ne_zero D hMonic hGlobal
  exact rational_power_pair_of_unit_denominator
    N D y hy m hUnit hRat

end AlgebraicallyClosedField

end HC4.RationalRigidity
