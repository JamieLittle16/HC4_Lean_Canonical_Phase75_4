import HC4.Newton.TerminalOneZeroPlanarFibre
import HC4.Newton.PositiveWeightTriangularEvaluation
import Mathlib.Tactic

/-!
# Ambient decoupling in the standard one-zero terminal branch

Phase 93.35 recovers the unique zero-weight coordinate from gradient
coordinate `1`.

Phase 93.36 proves that every fixed `X₀` fibre in coordinates `2,3` is a
planar Keller map under `JC₂`.

This module records the ambient independence statements needed to connect
those two facts and to recover the final coordinate.

The key general lemma is elementary but useful:

* over characteristic zero, if `pderiv i P = 0`, then changing only
  coordinate `i` does not change the value of `P`.

It follows coefficientwise from the already-proved theorem
`exponent_eq_zero_of_pderiv_eq_zero`.

For the one-zero face, the green sparse Hessian row gives

    pderiv 1 (pderiv 2 F) = 0
    pderiv 1 (pderiv 3 F) = 0,

so gradient coordinates `2,3` ignore `X₁`.

Finally, if the affine slope is `s ≠ 0`, then

    pderiv 0 F - C s * X 1

also ignores `X₁`.  Thus, once coordinates `0,2,3` agree, equality of
gradient coordinate `0` forces coordinate `1` to agree.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/- Keep this one-zero module isolated from the two-zero derivative aliases. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- If a partial derivative vanishes in characteristic zero, evaluation is
unchanged when only that coordinate is changed. -/
theorem eval_eq_of_pderiv_eq_zero
    [CharZero K]
    (i : Fin 4)
    (P : MvPolynomial (Fin 4) K)
    (hderiv : MvPolynomial.pderiv i P = 0)
    (p q : Fin 4 -> K)
    (heq :
      ∀ j : Fin 4,
        j ≠ i ->
          p j = q j) :
    MvPolynomial.eval p P =
      MvPolynomial.eval q P := by
  rw [MvPolynomial.as_sum P]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply
    eval_monomial_eq_of_eq_on_exponent_support
      m (MvPolynomial.coeff m P) p q
  intro j hmj
  by_cases hji : j = i
  · subst j
    have hmcoeff :
        MvPolynomial.coeff m P ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    have hmi :
        m i = 0 :=
      exponent_eq_zero_of_pderiv_eq_zero
        i P hderiv m hmcoeff
    exact (hmj hmi).elim
  · exact heq j hji

/-- In the standard one-zero face, gradient coordinate `2` is independent
of source coordinate `1`. -/
theorem standardOneZero_pderiv_two_independent_of_one
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F) :
    MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 2 F) = 0 := by
  have hz :=
    standardOneZero_pderiv_one_crossHessian_zero
      ha had hhom
  rw [pderiv_comm_backport]
  exact hz.2.1

/-- Likewise gradient coordinate `3` is independent of source coordinate
`1`. -/
theorem standardOneZero_pderiv_three_independent_of_one
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F) :
    MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 3 F) = 0 := by
  have hz :=
    standardOneZero_pderiv_one_crossHessian_zero
      ha had hhom
  rw [pderiv_comm_backport]
  exact hz.2.2

/-- If two points differ only in coordinate `1`, their gradient coordinate
`2` values agree. -/
theorem standardOneZero_gradient_two_eq_of_eq_off_one
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (p q : Fin 4 -> K)
    (heq :
      ∀ j : Fin 4,
        j ≠ 1 ->
          p j = q j) :
    mvGradientMap F p 2 =
      mvGradientMap F q 2 := by
  change
    MvPolynomial.eval p
        (MvPolynomial.pderiv 2 F) =
      MvPolynomial.eval q
        (MvPolynomial.pderiv 2 F)
  exact
    eval_eq_of_pderiv_eq_zero
      1 (MvPolynomial.pderiv 2 F)
      (standardOneZero_pderiv_two_independent_of_one
        ha had hhom)
      p q heq

/-- The analogous statement for gradient coordinate `3`. -/
theorem standardOneZero_gradient_three_eq_of_eq_off_one
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (p q : Fin 4 -> K)
    (heq :
      ∀ j : Fin 4,
        j ≠ 1 ->
          p j = q j) :
    mvGradientMap F p 3 =
      mvGradientMap F q 3 := by
  change
    MvPolynomial.eval p
        (MvPolynomial.pderiv 3 F) =
      MvPolynomial.eval q
        (MvPolynomial.pderiv 3 F)
  exact
    eval_eq_of_pderiv_eq_zero
      1 (MvPolynomial.pderiv 3 F)
      (standardOneZero_pderiv_three_independent_of_one
        ha had hhom)
      p q heq

/-- After subtracting its explicit nonzero `X₁` linear term, gradient
coordinate `0` is independent of `X₁`. -/
theorem standardOneZero_pderiv_zero_remainder_independent_of_one
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    ∃ s : K,
      s ≠ 0 ∧
      MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 0 F -
          MvPolynomial.C s * MvPolynomial.X 1) = 0 := by
  rcases
      standardOneZero_slope_eq_C_nonzero
        ha had hhom hMA with
    ⟨s, hs, hslope⟩
  refine ⟨s, hs, ?_⟩
  rw [map_sub]
  have hmixed :
      MvPolynomial.pderiv 1
          (MvPolynomial.pderiv 0 F) =
        MvPolynomial.C s := by
    rw [pderiv_comm_backport]
    exact hslope
  rw [hmixed]
  simp

/-- **Final-coordinate recovery for the standard one-zero branch.**

Once coordinates `0,2,3` of two points are known to agree, equality of
gradient coordinate `0` recovers coordinate `1`. -/
theorem standardOneZero_gradient_zero_recovers_one
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    {p q : Fin 4 -> K}
    (h0 : p 0 = q 0)
    (h2 : p 2 = q 2)
    (h3 : p 3 = q 3)
    (hgrad0 :
      mvGradientMap F p 0 =
        mvGradientMap F q 0) :
    p 1 = q 1 := by
  rcases
      standardOneZero_pderiv_zero_remainder_independent_of_one
        ha had hhom hMA with
    ⟨s, hs, hrem⟩
  let R : MvPolynomial (Fin 4) K :=
    MvPolynomial.pderiv 0 F -
      MvPolynomial.C s * MvPolynomial.X 1
  have heqOff :
      ∀ j : Fin 4,
        j ≠ 1 ->
          p j = q j := by
    intro j hj
    fin_cases j
    · exact h0
    · exact (hj rfl).elim
    · exact h2
    · exact h3
  have hReval :
      MvPolynomial.eval p R =
        MvPolynomial.eval q R := by
    apply
      eval_eq_of_pderiv_eq_zero
        1 R
    · simpa [R] using hrem
    · exact heqOff
  change
    MvPolynomial.eval p
        (MvPolynomial.pderiv 0 F) =
      MvPolynomial.eval q
        (MvPolynomial.pderiv 0 F) at hgrad0
  dsimp [R] at hReval
  simp only [map_sub, map_mul,
    MvPolynomial.eval_C,
    MvPolynomial.eval_X] at hReval
  rw [hgrad0] at hReval
  have hmul :
      s * p 1 = s * q 1 := by
    linear_combination -hReval
  exact (mul_left_cancel₀ hs) hmul

end

end HC4.Newton
