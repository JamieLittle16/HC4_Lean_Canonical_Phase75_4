import HC4.RationalRigidity.Assembly

/-!
# Reduced-fraction assembly for the HC4 rational-rigidity bridge

The previous phases classified a rational identity after denominator
nonvanishing had been established.  This module provides a second, purely
algebraic route which is often better suited to chart calculations.

Suppose `N` and `D` are a reduced numerator-denominator pair, expressed by
`IsCoprime N D`.  If a cleared chart equation shows that `D ∣ N`, then
coprimality forces `D` to be a unit.  Over a field, a unit polynomial is a
nonzero constant; if it is monic, it is exactly `1`.

The important point is that this route needs neither algebraic closure nor an
independent nonvanishing argument.  It turns a globally cleared chart identity
and reducedness directly into the desired denominator classification.
-/

namespace HC4.RationalRigidity

open Polynomial

section Field

variable {K : Type*} [Field K]

/-- If a reduced denominator divides its numerator, then it is a unit. -/
theorem unit_denominator_of_coprime_dvd
    {N D : K[X]}
    (hCoprime : IsCoprime N D)
    (hDvd : D ∣ N) :
    IsUnit D :=
  hCoprime.symm.isUnit_of_dvd hDvd

/-- A unit polynomial over a field is a nonzero constant polynomial. -/
theorem constant_polynomial_of_isUnit
    (D : K[X])
    (hUnit : IsUnit D) :
    ∃ d : K, d ≠ 0 ∧ D = C d := by
  obtain ⟨d, hd, hCd⟩ := (Polynomial.isUnit_iff.mp hUnit)
  exact ⟨d, hd.ne_zero, hCd.symm⟩

/-- A reduced denominator which divides its numerator is a nonzero constant. -/
theorem constant_denominator_of_coprime_dvd
    {N D : K[X]}
    (hCoprime : IsCoprime N D)
    (hDvd : D ∣ N) :
    ∃ d : K, d ≠ 0 ∧ D = C d :=
  constant_polynomial_of_isUnit D
    (unit_denominator_of_coprime_dvd hCoprime hDvd)

/-- A monic reduced denominator which divides its numerator equals one. -/
theorem monic_denominator_eq_one_of_coprime_dvd
    {N D : K[X]}
    (hCoprime : IsCoprime N D)
    (hDvd : D ∣ N)
    (hMonic : D.Monic) :
    D = 1 :=
  hMonic.eq_one_of_isUnit
    (unit_denominator_of_coprime_dvd hCoprime hDvd)

end Field

section InfiniteField

variable {K : Type*} [Field K] [Infinite K]

/--
A cleared identity on a surjective chart is an identity of polynomials.
-/
theorem polynomial_identity_of_surjective_cleared_chart
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hClear : ∀ s, N.eval (y s) = P.eval (y s) * D.eval (y s)) :
    N = P * D := by
  apply polynomial_eq_of_surjective_eval N (P * D) y hy
  intro s
  simpa using hClear s

/--
The cleared chart identity makes the denominator divide the numerator.
-/
theorem denominator_dvd_of_surjective_cleared_chart
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hClear : ∀ s, N.eval (y s) = P.eval (y s) * D.eval (y s)) :
    D ∣ N := by
  refine ⟨P, ?_⟩
  have hPoly :=
    polynomial_identity_of_surjective_cleared_chart N D P y hy hClear
  simpa [mul_comm] using hPoly

/--
A reduced rational presentation and a globally cleared chart identity force the
denominator to be a unit.
-/
theorem unit_denominator_of_reduced_cleared_chart
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hCoprime : IsCoprime N D)
    (hClear : ∀ s, N.eval (y s) = P.eval (y s) * D.eval (y s)) :
    IsUnit D := by
  apply unit_denominator_of_coprime_dvd hCoprime
  exact denominator_dvd_of_surjective_cleared_chart N D P y hy hClear

/--
The unnormalised reduced-fraction conclusion: the denominator is a nonzero
constant and the numerator is the same constant times the target polynomial.
-/
theorem reduced_polynomial_pair_of_cleared_chart
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hCoprime : IsCoprime N D)
    (hClear : ∀ s, N.eval (y s) = P.eval (y s) * D.eval (y s)) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * P := by
  have hUnit : IsUnit D :=
    unit_denominator_of_reduced_cleared_chart
      N D P y hy hCoprime hClear
  obtain ⟨d, hd, hConst⟩ := constant_polynomial_of_isUnit D hUnit
  have hPoly : N = P * D :=
    polynomial_identity_of_surjective_cleared_chart N D P y hy hClear
  refine ⟨d, hd, hConst, ?_⟩
  calc
    N = P * D := hPoly
    _ = C d * P := by rw [hConst]; ac_rfl

/--
If the reduced denominator is monic, the cleared chart equation gives the
normalised pair `D = 1` and `N = P`.
-/
theorem reduced_polynomial_pair_of_monic_cleared_chart
    {S : Type*}
    (N D P : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hCoprime : IsCoprime N D)
    (hMonic : D.Monic)
    (hClear : ∀ s, N.eval (y s) = P.eval (y s) * D.eval (y s)) :
    D = 1 ∧ N = P := by
  have hUnit : IsUnit D :=
    unit_denominator_of_reduced_cleared_chart
      N D P y hy hCoprime hClear
  have hOne : D = 1 := hMonic.eq_one_of_isUnit hUnit
  refine ⟨hOne, ?_⟩
  have hPoly : N = P * D :=
    polynomial_identity_of_surjective_cleared_chart N D P y hy hClear
  simpa [hOne] using hPoly

/--
Power-target form of the unnormalised reduced-fraction conclusion.
-/
theorem reduced_power_pair_of_cleared_chart
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hCoprime : IsCoprime N D)
    (m : ℕ)
    (hClear : ∀ s, N.eval (y s) = (y s) ^ m * D.eval (y s)) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * X ^ m := by
  apply reduced_polynomial_pair_of_cleared_chart
    N D (X ^ m) y hy hCoprime
  intro s
  simpa using hClear s

/--
Power-target form with a monic reduced denominator.
-/
theorem reduced_power_pair_of_monic_cleared_chart
    {S : Type*}
    (N D : K[X]) (y : S → K)
    (hy : Function.Surjective y)
    (hCoprime : IsCoprime N D)
    (hMonic : D.Monic)
    (m : ℕ)
    (hClear : ∀ s, N.eval (y s) = (y s) ^ m * D.eval (y s)) :
    D = 1 ∧ N = X ^ m := by
  apply reduced_polynomial_pair_of_monic_cleared_chart
    N D (X ^ m) y hy hCoprime hMonic
  intro s
  simpa using hClear s

end InfiniteField

end HC4.RationalRigidity
