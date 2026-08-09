import HC4.Newton.SmithFirstWallGradeClassification
import Mathlib.Tactic

/-!
# Symmetric Smith balance refinement

Phase 93.14 corrects the surviving-grade interface: different
negative-first terms may initially have grades `(-1,k)` with different
positive `k`, and similarly on the negative-second side.

A finite-minimum argument is possible, but unnecessary.

Take the single explicit Phase 93.6 separator with

    k = l = 1.

Its direction is

    theta = (2,2).

On every grade allowed by the general Phase 93.14 classification,

    (-1,k), k >= 1;
    (l,-1), l >= 1;
    (0,0);
    a nonzero first-quadrant grade,

the Smith derivative is nonnegative.  It vanishes exactly at

    (-1,1), (0,0), (1,-1).

Pole minimality therefore forces a zero-derivative old-face term.  Refining
the old face by this symmetric Smith direction discards every term with
strictly positive derivative and leaves a nonempty subface consisting only
of those three target grades.

After excluding the w-linear zero-grade pattern, the refined subface
consists exactly of the transverse quadratic exponent patterns

    z^2, yz, y^2.

This is a cleaner replacement for the over-rigid fixed-(k,l) interface in
Phase 93.10.
-/

namespace HC4.Newton

noncomputable section

/-- The three Smith grades surviving the symmetric `(2,2)` refinement. -/
def IsSymmetricSmithTargetGrade
    (gamma : ℤ × ℤ) : Prop :=
  gamma = (-1, 1) ∨
  gamma = (0, 0) ∨
  gamma = (1, -1)

/-- The symmetric separator derivative is nonnegative on every general
surviving Smith grade. -/
theorem smithSeparatorDelta_one_one_nonnegative_of_generalShape
    (e : SmithSupportExponent)
    (hshape : HasGeneralSurvivingSmithGradeShape e) :
    0 ≤ smithSeparatorDelta 1 1 e := by
  rcases hshape with
    ⟨k, hk, hgrade⟩ |
    ⟨l, hl, hgrade⟩ |
    hzero |
    hquad
  · unfold smithSeparatorDelta
    rw [hgrade]
    simp [smithGradeDot, smithExtremeSeparator,
      smithNegativeFirstExtreme]
    exact_mod_cast hk
  · unfold smithSeparatorDelta
    rw [hgrade]
    simp [smithGradeDot, smithExtremeSeparator,
      smithNegativeSecondExtreme]
    exact_mod_cast hl
  · unfold smithSeparatorDelta
    rw [hzero]
    norm_num [smithGradeDot, smithExtremeSeparator]
  · exact
      le_of_lt
        (smithSeparatorDelta_pos_of_nonzeroFirstQuadrant
          (k := 1) (l := 1) (by omega) hquad)

/-- Under the general surviving-grade classification, a nonpositive
symmetric separator derivative forces one of the three target grades. -/
theorem symmetricTargetGrade_of_separatorDelta_one_one_nonpositive
    (e : SmithSupportExponent)
    (hshape : HasGeneralSurvivingSmithGradeShape e)
    (hdelta : smithSeparatorDelta 1 1 e ≤ 0) :
    IsSymmetricSmithTargetGrade e.grade := by
  rcases hshape with
    ⟨k, hk, hgrade⟩ |
    ⟨l, hl, hgrade⟩ |
    hzero |
    hquad
  · have hle := hdelta
    unfold smithSeparatorDelta at hle
    rw [hgrade] at hle
    simp [smithGradeDot, smithExtremeSeparator,
      smithNegativeFirstExtreme] at hle
    have hk1 : k = 1 := by
      omega
    left
    subst k
    simpa [smithNegativeFirstExtreme] using hgrade
  · have hle := hdelta
    unfold smithSeparatorDelta at hle
    rw [hgrade] at hle
    simp [smithGradeDot, smithExtremeSeparator,
      smithNegativeSecondExtreme] at hle
    have hl1 : l = 1 := by
      omega
    right
    right
    subst l
    simpa [smithNegativeSecondExtreme] using hgrade
  · exact Or.inr (Or.inl hzero)
  · have hpos :
        0 < smithSeparatorDelta 1 1 e :=
      smithSeparatorDelta_pos_of_nonzeroFirstQuadrant
        (k := 1) (l := 1) (by omega) hquad
    omega

/-- On a general surviving grade, zero symmetric derivative is equivalent
to being one of the three target grades. -/
theorem separatorDelta_one_one_eq_zero_iff_targetGrade
    (e : SmithSupportExponent)
    (hshape : HasGeneralSurvivingSmithGradeShape e) :
    smithSeparatorDelta 1 1 e = 0 ↔
      IsSymmetricSmithTargetGrade e.grade := by
  constructor
  · intro hzero
    apply
      symmetricTargetGrade_of_separatorDelta_one_one_nonpositive
        e hshape
    omega
  · intro htarget
    rcases htarget with hnegFirst | hzero | hnegSecond
    · unfold smithSeparatorDelta
      rw [hnegFirst]
      norm_num [smithGradeDot, smithExtremeSeparator]
    · unfold smithSeparatorDelta
      rw [hzero]
      norm_num [smithGradeDot, smithExtremeSeparator]
    · unfold smithSeparatorDelta
      rw [hnegSecond]
      norm_num [smithGradeDot, smithExtremeSeparator]

/-- The symmetric Smith refinement of the old minimum face. -/
def smithSymmetricBalancedSubface
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ) :
    Finset SmithSupportExponent :=
  S.filter
    (fun e =>
      base e = m ∧
      smithSeparatorDelta 1 1 e = 0)

@[simp] theorem mem_smithSymmetricBalancedSubface
    {S : Finset SmithSupportExponent}
    {m : ℤ}
    {base : SmithSupportExponent -> ℤ}
    {e : SmithSupportExponent} :
    e ∈ smithSymmetricBalancedSubface S m base ↔
      e ∈ S ∧
      base e = m ∧
      smithSeparatorDelta 1 1 e = 0 := by
  classical
  simp [smithSymmetricBalancedSubface]

/-- Pole minimality forces the symmetric refined subface to be nonempty. -/
theorem poleMinimal_smithSymmetricBalancedSubface_nonempty
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m)
    (hshape :
      HasGeneralSurvivingSmithFaceShape S m base) :
    (smithSymmetricBalancedSubface S m base).Nonempty := by
  rcases
      poleMinimal_exists_nonpositive_face_grade
        S m base hpole hmin hattain 1 1 with
    ⟨e, heS, hemin, hdeltaLe⟩
  have hdeltaNonneg :
      0 ≤ smithSeparatorDelta 1 1 e :=
    smithSeparatorDelta_one_one_nonnegative_of_generalShape
      e (hshape e heS hemin)
  have hdeltaZero :
      smithSeparatorDelta 1 1 e = 0 := by
    omega
  exact
    ⟨e,
      (mem_smithSymmetricBalancedSubface).2
        ⟨heS, hemin, hdeltaZero⟩⟩

/-- Every exponent in the symmetric refined subface has one of the three
target Smith grades. -/
theorem smithSymmetricBalancedSubface_targetGrade
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hshape :
      HasGeneralSurvivingSmithFaceShape S m base) :
    ∀ e ∈ smithSymmetricBalancedSubface S m base,
      IsSymmetricSmithTargetGrade e.grade := by
  intro e he
  rcases
      (mem_smithSymmetricBalancedSubface).1 he with
    ⟨heS, hemin, hdeltaZero⟩
  exact
    (separatorDelta_one_one_eq_zero_iff_targetGrade
      e (hshape e heS hemin)).1 hdeltaZero

/-- The three target grades correspond, after excluding the w-linear
zero-grade pattern, exactly to the three transverse quadratic exponent
patterns. -/
theorem symmetricTargetGrade_exponent_cases_of_noWLinear
    (e : SmithSupportExponent)
    (htarget : IsSymmetricSmithTargetGrade e.grade)
    (hnoW : ¬ IsWLinearSmithPattern e) :
    (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
    (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
    (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
  rcases htarget with hnegFirst | hzero | hnegSecond
  · left
    exact
      smithGrade_eq_minusOne_one_exponents
        e.b e.c e.d
        (by
          exact congrArg Prod.fst hnegFirst)
        (by
          exact congrArg Prod.snd hnegFirst)
  · right
    left
    exact zeroSmithGrade_is_yz_of_noWLinear e hzero hnoW
  · right
    right
    exact
      smithGrade_eq_one_minusOne_exponents
        e.b e.c e.d
        (by
          exact congrArg Prod.fst hnegSecond)
        (by
          exact congrArg Prod.snd hnegSecond)

/-- **Symmetric Smith balance closure.**
Under pole minimality, the corrected first-wall grade classification, and
exclusion of the w-linear blocker, there exists a nonempty refined old-face
subface and every exponent on it is exactly one of the three transverse
quadratic patterns `z^2`, `yz`, `y^2`. -/
theorem poleMinimal_symmetricSmithRefinement_quadratic
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m)
    (hshape :
      HasGeneralSurvivingSmithFaceShape S m base)
    (hnoW :
      ∀ e ∈ S,
        base e = m ->
          ¬ IsWLinearSmithPattern e) :
    (smithSymmetricBalancedSubface S m base).Nonempty ∧
      ∀ e ∈ smithSymmetricBalancedSubface S m base,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
  constructor
  · exact
      poleMinimal_smithSymmetricBalancedSubface_nonempty
        S m base hpole hmin hattain hshape
  · intro e he
    rcases
        (mem_smithSymmetricBalancedSubface).1 he with
      ⟨heS, hemin, hdeltaZero⟩
    have htarget :
        IsSymmetricSmithTargetGrade e.grade :=
      (separatorDelta_one_one_eq_zero_iff_targetGrade
        e (hshape e heS hemin)).1 hdeltaZero
    exact
      symmetricTargetGrade_exponent_cases_of_noWLinear
        e htarget (hnoW e heS hemin)

end

end HC4.Newton
