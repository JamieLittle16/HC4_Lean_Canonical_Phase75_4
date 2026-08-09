import HC4.Newton.SmithPoleMinimality
import Mathlib.Tactic

/-!
# Finite Smith balance closure

Phases 93.5--93.9 provide all ingredients of the finite Smith balance
argument:

* the surviving grade arithmetic;
* an explicit separator when `k*l > 1`;
* the exact valuation derivative;
* a small rational tilt;
* denominator clearing;
* contradiction to finite pole minimality.

This file composes them.

The only input left abstract is the finite grade classification that the
actual first-wall theorem must provide.  On the old minimum face, every
grade is required to be one of

    (-1,k),
    (l,-1),
    (0,0),

or a nonzero first-quadrant integral grade.

Under pole minimality, either `(0,0)` actually occurs on the face, or
`k*l <= 1`.  For positive integral `k,l`, the latter forces `k=l=1`.

Thus the whole finite convex-balance calculation is now reduced to a
single first-wall classification interface rather than a general convex
separation theorem.
-/

namespace HC4.Newton

noncomputable section

/-- A face grade in the nonnegative quadrant, represented by its natural
coordinates and required to be nonzero. -/
def IsNonzeroFirstQuadrantGrade
    (gamma : ℤ × ℤ) : Prop :=
  ∃ a b : ℕ,
    gamma = ((a : ℤ), (b : ℤ)) ∧
      (a ≠ 0 ∨ b ≠ 0)

/-- The surviving Smith-grade classification expected from the directional
first-wall analysis. -/
def HasSurvivingSmithFaceShape
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (k l : ℕ) : Prop :=
  ∀ e ∈ S,
    base e = m ->
      e.grade = smithNegativeFirstExtreme k ∨
      e.grade = smithNegativeSecondExtreme l ∨
      e.grade = (0, 0) ∨
      IsNonzeroFirstQuadrantGrade e.grade

/-- The explicit separator is strictly positive on every nonzero
first-quadrant face grade. -/
theorem smithSeparatorDelta_pos_of_nonzeroFirstQuadrant
    {k l : ℕ}
    (hk : 1 ≤ k)
    {e : SmithSupportExponent}
    (hquad : IsNonzeroFirstQuadrantGrade e.grade) :
    0 < smithSeparatorDelta k l e := by
  rcases hquad with ⟨a, b, hgrade, hnz⟩
  unfold smithSeparatorDelta
  rw [hgrade]
  exact
    smithExtremeSeparator_pos_nonnegative
      hk a b hnz

/-- If the zero grade is absent from the old minimum face and `k*l > 1`,
the explicit Phase 93.6 separator is positive on every old minimum-face
monomial. -/
theorem survivingSmithFace_separator_positive_of_product_gt_one
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    {k l : ℕ}
    (hk : 1 ≤ k)
    (hprod : 1 < k * l)
    (hshape : HasSurvivingSmithFaceShape S m base k l)
    (hnoZero :
      ¬ ∃ e ∈ S,
          base e = m ∧
          e.grade = (0, 0)) :
    ∀ e ∈ S,
      base e = m ->
        (1 : ℤ) ≤ smithSeparatorDelta k l e := by
  intro e heS hemin
  rcases hshape e heS hemin with
    hnegFirst | hnegSecond | hzero | hquad
  · have hpos : 0 < smithSeparatorDelta k l e := by
      unfold smithSeparatorDelta
      rw [hnegFirst]
      exact
        smithExtremeSeparator_pos_negativeFirst
          hk hprod
    omega
  · have hpos : 0 < smithSeparatorDelta k l e := by
      unfold smithSeparatorDelta
      rw [hnegSecond]
      exact
        smithExtremeSeparator_pos_negativeSecond
          hprod
    omega
  · exfalso
    apply hnoZero
    exact ⟨e, heS, hemin, hzero⟩
  · have hpos :
        0 < smithSeparatorDelta k l e :=
      smithSeparatorDelta_pos_of_nonzeroFirstQuadrant
        hk hquad
    omega

/-- **Finite pole balance without abstract convexity.**
Under the surviving-grade classification and finite pole minimality, either
the zero grade occurs on the old minimum face or the two negative extreme
parameters satisfy `k*l <= 1`. -/
theorem poleMinimal_survivingSmithFace_zero_or_product_le_one
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    {k l : ℕ}
    (hk : 1 ≤ k)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hshape :
      HasSurvivingSmithFaceShape S m base k l) :
    (∃ e ∈ S,
        base e = m ∧
        e.grade = (0, 0)) ∨
      k * l ≤ 1 := by
  by_cases hzero :
      ∃ e ∈ S,
        base e = m ∧
        e.grade = (0, 0)
  · exact Or.inl hzero
  · right
    by_contra hnotLe
    have hprod : 1 < k * l := by
      omega
    have hpositive :
        ∀ e ∈ S,
          base e = m ->
            (1 : ℤ) ≤ smithSeparatorDelta k l e :=
      survivingSmithFace_separator_positive_of_product_gt_one
        S m base hk hprod hshape hzero
    exact
      (poleMinimal_no_positive_smithSeparator
        S m base hpole hmin k l)
        hpositive

/-- Positive integral extreme parameters therefore collapse to the target
Smith grades unless the zero grade already occurs on the face. -/
theorem poleMinimal_survivingSmithFace_zero_or_target_extremes
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    {k l : ℕ}
    (hk : 1 ≤ k)
    (hl : 1 ≤ l)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hshape :
      HasSurvivingSmithFaceShape S m base k l) :
    (∃ e ∈ S,
        base e = m ∧
        e.grade = (0, 0)) ∨
      (smithNegativeFirstExtreme k = (-1, 1) ∧
        smithNegativeSecondExtreme l = (1, -1)) := by
  rcases
      poleMinimal_survivingSmithFace_zero_or_product_le_one
        S m base hk hpole hmin hshape with
    hzero | hprod
  · exact Or.inl hzero
  · exact Or.inr
      (by
        rcases
            smithBalancedExtreme_productBound
              k l hk hl hprod with
          ⟨hk1, hl1⟩
        subst k
        subst l
        norm_num
          [smithNegativeFirstExtreme,
           smithNegativeSecondExtreme])

/-- A zero-grade face exponent is exactly the `yz` pattern once the
`w`-linear zero-grade blocker is excluded. -/
theorem zeroGradeFaceExponent_is_yz_of_not_wLinear
    {e : SmithSupportExponent}
    (hgrade : e.grade = (0, 0))
    (hnotW :
      ¬ (e.b = 0 ∧ e.c = 0 ∧ e.d = 1)) :
    e.b = 1 ∧ e.c = 1 ∧ e.d = 0 := by
  unfold SmithSupportExponent.grade at hgrade
  exact
    smithGrade_eq_zero_zero_exponents_of_not_wLinear
      e.b e.c e.d hgrade hnotW

/-- Final finite face conclusion after excluding the `w`-linear wall:
either the face contains the `yz` exponent pattern, or the only possible
negative-coordinate extreme grades are `(-1,1)` and `(1,-1)`. -/
theorem poleMinimal_survivingSmithFace_yz_or_target_extremes
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    {k l : ℕ}
    (hk : 1 ≤ k)
    (hl : 1 ≤ l)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hshape :
      HasSurvivingSmithFaceShape S m base k l)
    (hnoW :
      ∀ e ∈ S,
        base e = m ->
          ¬ (e.b = 0 ∧ e.c = 0 ∧ e.d = 1)) :
    (∃ e ∈ S,
        base e = m ∧
        e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (smithNegativeFirstExtreme k = (-1, 1) ∧
        smithNegativeSecondExtreme l = (1, -1)) := by
  rcases
      poleMinimal_survivingSmithFace_zero_or_target_extremes
        S m base hk hl hpole hmin hshape with
    hzero | htargets
  · rcases hzero with ⟨e, heS, hemin, hgrade⟩
    left
    have hyz :
        e.b = 1 ∧ e.c = 1 ∧ e.d = 0 :=
      zeroGradeFaceExponent_is_yz_of_not_wLinear
        hgrade (hnoW e heS hemin)
    exact ⟨e, heS, hemin, hyz.1, hyz.2.1, hyz.2.2⟩
  · exact Or.inr htargets

end

end HC4.Newton
