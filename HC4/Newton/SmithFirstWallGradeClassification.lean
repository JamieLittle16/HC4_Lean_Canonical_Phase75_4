import HC4.Newton.SmithFirstWallLongitudinal
import Mathlib.Tactic

/-!
# Pointwise Smith grade classification after low-wall exclusion

The green first-wall collision theorems exclude the four low monomial
patterns.  Before taking minima over a finite exposed face, we isolate the
exact pointwise arithmetic consequence on the Smith exponent triple
`(b,c,d)`.

Once the three genuinely negative low patterns are absent, every Smith
grade is one of

    (-1,k),  k >= 1;
    (l,-1),  l >= 1;
    (0,0);
    a nonzero first-quadrant integral grade.

The `w`-linear pattern has grade `(0,0)`, so it is not needed for this
coarse classification.  Excluding it later identifies zero grade uniquely
with the `yz` pattern.

This corrects an over-rigid intermediate interface from Phase 93.10:
different negative-first face terms may initially have different positive
parameters `k`, and similarly on the other side.  Finite minima should be
taken only after this pointwise classification.
-/

namespace HC4.Newton

noncomputable section

/-- Smith exponent pattern corresponding to a pure longitudinal term. -/
def IsPureLongitudinalSmithPattern
    (e : SmithSupportExponent) : Prop :=
  e.b = 0 ∧ e.c = 0 ∧ e.d = 0

/-- Smith exponent pattern of the low negative-first blocker. -/
def IsLowNegativeFirstSmithPattern
    (e : SmithSupportExponent) : Prop :=
  e.b = 0 ∧ e.c = 1 ∧ e.d = 0

/-- Smith exponent pattern of the low negative-second blocker. -/
def IsLowNegativeSecondSmithPattern
    (e : SmithSupportExponent) : Prop :=
  e.b = 1 ∧ e.c = 0 ∧ e.d = 0

/-- The zero-grade `w`-linear pattern. -/
def IsWLinearSmithPattern
    (e : SmithSupportExponent) : Prop :=
  e.b = 0 ∧ e.c = 0 ∧ e.d = 1

/-- The three low patterns whose exclusion is needed merely to obtain the
coarse surviving-grade shape. -/
def HasNoNegativeLowSmithPatterns
    (e : SmithSupportExponent) : Prop :=
  ¬ IsPureLongitudinalSmithPattern e ∧
  ¬ IsLowNegativeFirstSmithPattern e ∧
  ¬ IsLowNegativeSecondSmithPattern e

/-- Pointwise surviving Smith-grade classification, with no assumption that
all negative-first or negative-second terms have a common parameter. -/
def HasGeneralSurvivingSmithGradeShape
    (e : SmithSupportExponent) : Prop :=
  (∃ k : ℕ,
      1 ≤ k ∧
      e.grade = smithNegativeFirstExtreme k) ∨
  (∃ l : ℕ,
      1 ≤ l ∧
      e.grade = smithNegativeSecondExtreme l) ∨
  e.grade = (0, 0) ∨
  IsNonzeroFirstQuadrantGrade e.grade

/-- **Pointwise first-wall grade classification.**
Excluding the pure longitudinal and two low transverse negative-grade
patterns leaves exactly the four coarse grade types needed by the finite
balance argument. -/
theorem generalSurvivingSmithGradeShape_of_noNegativeLowPatterns
    (e : SmithSupportExponent)
    (hno : HasNoNegativeLowSmithPatterns e) :
    HasGeneralSurvivingSmithGradeShape e := by
  rcases e with ⟨b, c, d⟩
  unfold HasGeneralSurvivingSmithGradeShape
  by_cases hfirstNeg : smithGradeFirst b d < 0
  · rcases smithGradeFirst_neg_shape
        b d hfirstNeg with
      ⟨hb, hd, hfirst⟩
    subst b
    subst d
    by_cases hsecondNeg : smithGradeSecond c 0 < 0
    · rcases smithGradeSecond_neg_shape
          c 0 hsecondNeg with
        ⟨hc, _, _⟩
      subst c
      exfalso
      apply hno.1
      exact ⟨rfl, rfl, rfl⟩
    · by_cases hsecondZero :
          smithGradeSecond c 0 = 0
      · have hc : c = 1 := by
          unfold smithGradeSecond at hsecondZero
          omega
        subst c
        exfalso
        apply hno.2.1
        exact ⟨rfl, rfl, rfl⟩
      · left
        have hcTwo : 2 ≤ c := by
          unfold smithGradeSecond at hsecondNeg hsecondZero
          omega
        refine ⟨c - 1, by omega, ?_⟩
        apply Prod.ext
        · simp [SmithSupportExponent.grade,
            smithGrade, smithGradeFirst,
            smithNegativeFirstExtreme]
        · simp [SmithSupportExponent.grade,
            smithGrade, smithGradeSecond,
            smithNegativeFirstExtreme]
          omega
  · by_cases hsecondNeg : smithGradeSecond c d < 0
    · rcases smithGradeSecond_neg_shape
          c d hsecondNeg with
        ⟨hc, hd, hsecond⟩
      subst c
      subst d
      by_cases hfirstZero :
          smithGradeFirst b 0 = 0
      · have hb : b = 1 := by
          unfold smithGradeFirst at hfirstZero
          omega
        subst b
        exfalso
        apply hno.2.2
        exact ⟨rfl, rfl, rfl⟩
      · right
        left
        have hbTwo : 2 ≤ b := by
          unfold smithGradeFirst at hfirstNeg hfirstZero
          omega
        refine ⟨b - 1, by omega, ?_⟩
        apply Prod.ext
        · simp [SmithSupportExponent.grade,
            smithGrade, smithGradeFirst,
            smithNegativeSecondExtreme]
          omega
        · simp [SmithSupportExponent.grade,
            smithGrade, smithGradeSecond,
            smithNegativeSecondExtreme]
    · by_cases hzero :
          (SmithSupportExponent.grade
            ⟨b, c, d⟩) = (0, 0)
      · exact Or.inr (Or.inr (Or.inl hzero))
      · right
        right
        right
        unfold IsNonzeroFirstQuadrantGrade
        have hfirstNonneg :
            0 ≤ smithGradeFirst b d := by
          omega
        have hsecondNonneg :
            0 ≤ smithGradeSecond c d := by
          omega
        have hbd : 1 ≤ b + d := by
          unfold smithGradeFirst at hfirstNonneg
          omega
        have hcd : 1 ≤ c + d := by
          unfold smithGradeSecond at hsecondNonneg
          omega
        refine
          ⟨b + d - 1,
           c + d - 1,
           ?_, ?_⟩
        · apply Prod.ext
          · simp [SmithSupportExponent.grade,
              smithGrade, smithGradeFirst]
            omega
          · simp [SmithSupportExponent.grade,
              smithGrade, smithGradeSecond]
            omega
        · by_cases ha : b + d - 1 = 0
          · right
            intro hbzero
            apply hzero
            apply Prod.ext
            · simp [SmithSupportExponent.grade,
                smithGrade, smithGradeFirst]
              omega
            · simp [SmithSupportExponent.grade,
                smithGrade, smithGradeSecond]
              omega
          · exact Or.inl ha

/-- Finite-face version of the corrected general surviving-grade
classification. -/
def HasGeneralSurvivingSmithFaceShape
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ) : Prop :=
  ∀ e ∈ S,
    base e = m ->
      HasGeneralSurvivingSmithGradeShape e

/-- Pointwise low-pattern exclusion on the old minimum face gives the
corrected finite surviving-grade interface. -/
theorem generalSurvivingSmithFaceShape_of_noNegativeLowPatterns
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hno :
      ∀ e ∈ S,
        base e = m ->
          HasNoNegativeLowSmithPatterns e) :
    HasGeneralSurvivingSmithFaceShape S m base := by
  intro e heS hemin
  exact
    generalSurvivingSmithGradeShape_of_noNegativeLowPatterns
      e (hno e heS hemin)

/-- If the `w`-linear pattern is excluded as well, zero Smith grade is
exactly the `yz` exponent pattern. -/
theorem zeroSmithGrade_is_yz_of_noWLinear
    (e : SmithSupportExponent)
    (hzero : e.grade = (0, 0))
    (hnoW : ¬ IsWLinearSmithPattern e) :
    e.b = 1 ∧ e.c = 1 ∧ e.d = 0 := by
  apply zeroGradeFaceExponent_is_yz_of_not_wLinear hzero
  exact hnoW

end

end HC4.Newton
