import HC4.Newton.TerminalPermutedGradient
import Mathlib.Tactic

/-!
# Positive-weight triangular support

This is the finite support lemma behind the positive-weight inverse.

Let all four weights be strictly positive and let `P` be weighted
homogeneous of positive degree `t`.

For any supported monomial `X^m`:

* every variable occurring in `m` has weight at most `t`;
* if an occurring variable has weight exactly `t`, then the entire monomial
  is just that one linear variable;
* therefore every supported monomial is either a linear variable of weight
  exactly `t`, or all variables occurring in it have strictly smaller
  weight.

Applied componentwise to a weight-preserving polynomial map, this is the
precise triangularity needed for recursive inversion by increasing weight.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Explicit four-coordinate expansion of the integral weighted degree. -/
theorem integralWeightedDegree_fin_four
    (lambda : Fin 4 -> ℤ)
    (m : Fin 4 →₀ ℕ) :
    integralWeightedDegree lambda m =
      (m 0 : ℤ) * lambda 0 +
      (m 1 : ℤ) * lambda 1 +
      (m 2 : ℤ) * lambda 2 +
      (m 3 : ℤ) * lambda 3 := by
  unfold integralWeightedDegree
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_four]
  · intro i
    simp

/-- Every coordinate contribution to a positive weighted degree is
nonnegative. -/
theorem positiveWeight_term_nonnegative
    {lambda : Fin 4 -> ℤ}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (m : Fin 4 →₀ ℕ)
    (i : Fin 4) :
    0 ≤ (m i : ℤ) * lambda i := by
  exact mul_nonneg
    (by positivity)
    (le_of_lt (hpos i))

/-- If an exponent is nonzero, one copy of its positive weight is bounded
by that exponent's full weighted contribution. -/
theorem positiveWeight_le_weightedTerm
    {lambda : Fin 4 -> ℤ}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (m : Fin 4 →₀ ℕ)
    {i : Fin 4}
    (hmi : m i ≠ 0) :
    lambda i ≤ (m i : ℤ) * lambda i := by
  have honeNat : 1 ≤ m i :=
    Nat.one_le_iff_ne_zero.mpr hmi
  have hone : (1 : ℤ) ≤ (m i : ℤ) := by
    exact_mod_cast honeNat
  calc
    lambda i = (1 : ℤ) * lambda i := by ring
    _ ≤ (m i : ℤ) * lambda i :=
      mul_le_mul_of_nonneg_right
        hone (le_of_lt (hpos i))

/-- A zero weighted contribution with positive weight forces the exponent
itself to vanish. -/
theorem exponent_eq_zero_of_positiveWeightedTerm_eq_zero
    {lambda : Fin 4 -> ℤ}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (m : Fin 4 →₀ ℕ)
    (i : Fin 4)
    (hterm :
      (m i : ℤ) * lambda i = 0) :
    m i = 0 := by
  have hlambda : lambda i ≠ 0 :=
    ne_of_gt (hpos i)
  have hmcast : (m i : ℤ) = 0 :=
    (mul_eq_zero.mp hterm).resolve_right hlambda
  exact_mod_cast hmcast

/-- If a nonzero exponent contributes exactly one copy of its positive
weight, then that exponent is exactly one. -/
theorem exponent_eq_one_of_positiveWeightedTerm_eq_weight
    {lambda : Fin 4 -> ℤ}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (m : Fin 4 →₀ ℕ)
    {i : Fin 4}
    (hmi : m i ≠ 0)
    (hterm :
      (m i : ℤ) * lambda i = lambda i) :
    m i = 1 := by
  have hlambda : lambda i ≠ 0 :=
    ne_of_gt (hpos i)
  have hfactor :
      ((m i : ℤ) - 1) * lambda i = 0 := by
    calc
      ((m i : ℤ) - 1) * lambda i =
          (m i : ℤ) * lambda i - lambda i := by
            ring
      _ = 0 := by rw [hterm]; ring
  have hmminus :
      (m i : ℤ) - 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hlambda
  have hmcast : (m i : ℤ) = 1 := by
    linarith
  exact_mod_cast hmcast

/-- If a variable occurs in a supported monomial of a positive weighted
homogeneous polynomial, its weight cannot exceed the component degree. -/
theorem positiveWeightedHomogeneous_support_weight_le
    {lambda : Fin 4 -> ℤ}
    {t : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (hhom :
      IsIntegralWeightedHomogeneous lambda t P)
    {m : Fin 4 →₀ ℕ}
    (hm :
      MvPolynomial.coeff m P ≠ 0)
    {j : Fin 4}
    (hmj : m j ≠ 0) :
    lambda j ≤ t := by
  have hdeg := hhom m hm
  rw [integralWeightedDegree_fin_four] at hdeg
  have h0 :=
    positiveWeight_term_nonnegative hpos m (0 : Fin 4)
  have h1 :=
    positiveWeight_term_nonnegative hpos m (1 : Fin 4)
  have h2 :=
    positiveWeight_term_nonnegative hpos m (2 : Fin 4)
  have h3 :=
    positiveWeight_term_nonnegative hpos m (3 : Fin 4)
  have hjLower :=
    positiveWeight_le_weightedTerm hpos m hmj
  fin_cases j
  · change lambda 0 ≤ t
    change lambda 0 ≤ (m 0 : ℤ) * lambda 0 at hjLower
    linarith
  · change lambda 1 ≤ t
    change lambda 1 ≤ (m 1 : ℤ) * lambda 1 at hjLower
    linarith
  · change lambda 2 ≤ t
    change lambda 2 ≤ (m 2 : ℤ) * lambda 2 at hjLower
    linarith
  · change lambda 3 ≤ t
    change lambda 3 ≤ (m 3 : ℤ) * lambda 3 at hjLower
    linarith

/-- If a supported monomial contains a variable whose weight already equals
the full component degree, positivity forces that monomial to be exactly
that one linear variable. -/
theorem positiveWeightedHomogeneous_equalWeight_forces_single
    {lambda : Fin 4 -> ℤ}
    {t : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (hhom :
      IsIntegralWeightedHomogeneous lambda t P)
    {m : Fin 4 →₀ ℕ}
    (hm :
      MvPolynomial.coeff m P ≠ 0)
    {j : Fin 4}
    (hmj : m j ≠ 0)
    (hj : lambda j = t) :
    m = Finsupp.single j 1 := by
  have hdeg := hhom m hm
  rw [integralWeightedDegree_fin_four] at hdeg

  have h0 :=
    positiveWeight_term_nonnegative hpos m (0 : Fin 4)
  have h1 :=
    positiveWeight_term_nonnegative hpos m (1 : Fin 4)
  have h2 :=
    positiveWeight_term_nonnegative hpos m (2 : Fin 4)
  have h3 :=
    positiveWeight_term_nonnegative hpos m (3 : Fin 4)

  fin_cases j
  · change m 0 ≠ 0 at hmj
    change lambda 0 = t at hj
    rw [← hj] at hdeg
    have h0Lower :
        lambda 0 ≤ (m 0 : ℤ) * lambda 0 :=
      positiveWeight_le_weightedTerm hpos m hmj
    have hterm0 :
        (m 0 : ℤ) * lambda 0 = lambda 0 := by
      linarith
    have ht1 :
        (m 1 : ℤ) * lambda 1 = 0 := by
      linarith
    have ht2 :
        (m 2 : ℤ) * lambda 2 = 0 := by
      linarith
    have ht3 :
        (m 3 : ℤ) * lambda 3 = 0 := by
      linarith
    have hm0 :
        m 0 = 1 :=
      exponent_eq_one_of_positiveWeightedTerm_eq_weight
        hpos m hmj hterm0
    have hm1 :
        m 1 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 1 ht1
    have hm2 :
        m 2 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 2 ht2
    have hm3 :
        m 3 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 3 ht3
    apply Finsupp.ext
    intro k
    fin_cases k <;>
      simp [hm0, hm1, hm2, hm3]
  · change m 1 ≠ 0 at hmj
    change lambda 1 = t at hj
    rw [← hj] at hdeg
    have h1Lower :
        lambda 1 ≤ (m 1 : ℤ) * lambda 1 :=
      positiveWeight_le_weightedTerm hpos m hmj
    have hterm1 :
        (m 1 : ℤ) * lambda 1 = lambda 1 := by
      linarith
    have ht0 :
        (m 0 : ℤ) * lambda 0 = 0 := by
      linarith
    have ht2 :
        (m 2 : ℤ) * lambda 2 = 0 := by
      linarith
    have ht3 :
        (m 3 : ℤ) * lambda 3 = 0 := by
      linarith
    have hm0 :
        m 0 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 0 ht0
    have hm1 :
        m 1 = 1 :=
      exponent_eq_one_of_positiveWeightedTerm_eq_weight
        hpos m hmj hterm1
    have hm2 :
        m 2 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 2 ht2
    have hm3 :
        m 3 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 3 ht3
    apply Finsupp.ext
    intro k
    fin_cases k <;>
      simp [hm0, hm1, hm2, hm3]
  · change m 2 ≠ 0 at hmj
    change lambda 2 = t at hj
    rw [← hj] at hdeg
    have h2Lower :
        lambda 2 ≤ (m 2 : ℤ) * lambda 2 :=
      positiveWeight_le_weightedTerm hpos m hmj
    have hterm2 :
        (m 2 : ℤ) * lambda 2 = lambda 2 := by
      linarith
    have ht0 :
        (m 0 : ℤ) * lambda 0 = 0 := by
      linarith
    have ht1 :
        (m 1 : ℤ) * lambda 1 = 0 := by
      linarith
    have ht3 :
        (m 3 : ℤ) * lambda 3 = 0 := by
      linarith
    have hm0 :
        m 0 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 0 ht0
    have hm1 :
        m 1 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 1 ht1
    have hm2 :
        m 2 = 1 :=
      exponent_eq_one_of_positiveWeightedTerm_eq_weight
        hpos m hmj hterm2
    have hm3 :
        m 3 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 3 ht3
    apply Finsupp.ext
    intro k
    fin_cases k <;>
      simp [hm0, hm1, hm2, hm3]
  · change m 3 ≠ 0 at hmj
    change lambda 3 = t at hj
    rw [← hj] at hdeg
    have h3Lower :
        lambda 3 ≤ (m 3 : ℤ) * lambda 3 :=
      positiveWeight_le_weightedTerm hpos m hmj
    have hterm3 :
        (m 3 : ℤ) * lambda 3 = lambda 3 := by
      linarith
    have ht0 :
        (m 0 : ℤ) * lambda 0 = 0 := by
      linarith
    have ht1 :
        (m 1 : ℤ) * lambda 1 = 0 := by
      linarith
    have ht2 :
        (m 2 : ℤ) * lambda 2 = 0 := by
      linarith
    have hm0 :
        m 0 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 0 ht0
    have hm1 :
        m 1 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 1 ht1
    have hm2 :
        m 2 = 0 :=
      exponent_eq_zero_of_positiveWeightedTerm_eq_zero
        hpos m 2 ht2
    have hm3 :
        m 3 = 1 :=
      exponent_eq_one_of_positiveWeightedTerm_eq_weight
        hpos m hmj hterm3
    apply Finsupp.ext
    intro k
    fin_cases k <;>
      simp [hm0, hm1, hm2, hm3]

/-- Exact triangular support alternative for a positive weighted-homogeneous
component. -/
def HasPositiveWeightTriangularSupport
    (lambda : Fin 4 -> ℤ)
    (t : ℤ)
    (P : MvPolynomial (Fin 4) K) : Prop :=
  ∀ m : Fin 4 →₀ ℕ,
    MvPolynomial.coeff m P ≠ 0 ->
      (∃ j : Fin 4,
        m = Finsupp.single j 1 ∧
        lambda j = t) ∨
      (∀ j : Fin 4,
        m j ≠ 0 ->
          lambda j < t)

/-- Positive weighted homogeneity implies exact triangular support. -/
theorem positiveWeightedHomogeneous_hasTriangularSupport
    {lambda : Fin 4 -> ℤ}
    {t : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (hhom :
      IsIntegralWeightedHomogeneous lambda t P) :
    HasPositiveWeightTriangularSupport lambda t P := by
  intro m hm
  by_cases heq :
      ∃ j : Fin 4,
        m j ≠ 0 ∧ lambda j = t
  · rcases heq with ⟨j, hmj, hj⟩
    exact Or.inl
      ⟨j,
        positiveWeightedHomogeneous_equalWeight_forces_single
          hpos hhom hm hmj hj,
        hj⟩
  · right
    intro j hmj
    have hle :
        lambda j ≤ t :=
      positiveWeightedHomogeneous_support_weight_le
        hpos hhom hm hmj
    have hne :
        lambda j ≠ t := by
      intro hEq
      exact heq ⟨j, hmj, hEq⟩
    omega

/-- At a minimum positive component degree, the lower-weight alternative is
impossible; every supported monomial is therefore linear in a variable of
the same weight.

The explicit hypothesis `0 < t` is necessary: without it the constant
polynomial of weighted degree zero would be a counterexample. -/
theorem minimumPositiveWeight_support_is_linear
    {lambda : Fin 4 -> ℤ}
    {t : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (hpos :
      ∀ i : Fin 4, 0 < lambda i)
    (ht :
      0 < t)
    (hmin :
      ∀ j : Fin 4, t ≤ lambda j)
    (hhom :
      IsIntegralWeightedHomogeneous lambda t P) :
    ∀ m : Fin 4 →₀ ℕ,
      MvPolynomial.coeff m P ≠ 0 ->
        ∃ j : Fin 4,
          m = Finsupp.single j 1 ∧
          lambda j = t := by
  intro m hm
  rcases
      positiveWeightedHomogeneous_hasTriangularSupport
        hpos hhom m hm with
    hlinear | hlower
  · exact hlinear
  · have hmnonzero : m ≠ 0 := by
      intro hm0
      subst m
      have hdeg := hhom 0 hm
      simp [integralWeightedDegree] at hdeg
      linarith
    have hex :
        ∃ j : Fin 4, m j ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hmnonzero
      apply Finsupp.ext
      intro j
      simp [hnone j]
    rcases hex with ⟨j, hmj⟩
    have hlt := hlower j hmj
    have hge := hmin j
    linarith

end

end HC4.Newton
