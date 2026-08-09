import HC4.Newton.SmithExtremeBalance
import Mathlib.Tactic

/-!
# Finite valuation tilt above an integral pole face

The Smith convex-balance argument has two logically separate pieces.

Phase 93.6 supplies the finite separator.  This file supplies the
quantitative "sufficiently small tilt" lemma.

Suppose the old normalised coefficient valuations have minimum `m`.
Because the valuations are integral, every coefficient off the old
minimal face has value at least `m+1`.

Assume a rational tilt direction changes every support value by `delta`,
with

    -B <= delta <= B,

and changes every old face value positively:

    1 <= delta.

For

    epsilon = 1 / (2(B+1)),

every old face coefficient rises strictly above `m`, while an off-face
coefficient can fall by less than one.  Consequently every coefficient in
the finite support has tilted value strictly above the old minimum `m`.

This is the quantitative core of the pole-minimality contradiction.  The
next adapter only needs to identify the Smith dot product with the change
in normalised valuation under a conformal weight tilt.
-/

namespace HC4.Newton

noncomputable section

/-- Explicit small positive tilt used for a support whose tilt changes are
bounded in absolute value by `B`. -/
def finiteTiltEpsilon
    (B : ℚ) : ℚ :=
  1 / (2 * (B + 1))

/-- The explicit tilt is positive for a nonnegative bound. -/
theorem finiteTiltEpsilon_pos
    {B : ℚ}
    (hB : 0 ≤ B) :
    0 < finiteTiltEpsilon B := by
  unfold finiteTiltEpsilon
  positivity

/-- The maximal downward movement `epsilon * B` is strictly less than one. -/
theorem finiteTiltEpsilon_mul_bound_lt_one
    {B : ℚ}
    (hB : 0 ≤ B) :
    finiteTiltEpsilon B * B < 1 := by
  have heps :
      0 < finiteTiltEpsilon B :=
    finiteTiltEpsilon_pos hB
  have hden :
      0 < 2 * (B + 1) := by
    positivity
  have heq :
      finiteTiltEpsilon B * (2 * (B + 1)) = 1 := by
    unfold finiteTiltEpsilon
    field_simp
  have hlt :
      B < 2 * (B + 1) := by
    linarith
  have hmul :
      finiteTiltEpsilon B * B <
        finiteTiltEpsilon B * (2 * (B + 1)) :=
    mul_lt_mul_of_pos_left hlt heps
  rw [heq] at hmul
  exact hmul

/-- Integer-valued valuations are either on the minimum face or at least
one unit above it. -/
theorem integer_min_or_unit_gap
    {m v : ℤ}
    (hmin : m ≤ v) :
    v = m ∨ m + 1 ≤ v := by
  omega

/-- Rational tilted value attached to an old value and a tilt derivative. -/
def finiteTiltedValue
    (epsilon base delta : ℚ) : ℚ :=
  base + epsilon * delta

/-- Pointwise small-tilt lemma in rational form.

If `base=m`, positivity of the separator raises the value.
If `base>=m+1`, bounded downward motion cannot consume the full unit gap. -/
theorem finiteTiltedValue_gt_minimum
    {B m base delta : ℚ}
    (hB : 0 ≤ B)
    (hfaceOrGap : base = m ∨ m + 1 ≤ base)
    (hdeltaLower : -B ≤ delta)
    (hfacePositive : base = m -> 1 ≤ delta) :
    m <
      finiteTiltedValue
        (finiteTiltEpsilon B) base delta := by
  have heps :
      0 < finiteTiltEpsilon B :=
    finiteTiltEpsilon_pos hB
  have hepsB :
      finiteTiltEpsilon B * B < 1 :=
    finiteTiltEpsilon_mul_bound_lt_one hB
  rcases hfaceOrGap with hface | hgap
  · have hdelta : 1 ≤ delta :=
      hfacePositive hface
    have hprod :
        0 < finiteTiltEpsilon B * delta := by
      have hone : (0 : ℚ) < 1 := by norm_num
      have hdeltaPos : 0 < delta := lt_of_lt_of_le hone hdelta
      exact mul_pos heps hdeltaPos
    unfold finiteTiltedValue
    rw [hface]
    linarith
  · have hdown :
        -(finiteTiltEpsilon B * B) ≤
          finiteTiltEpsilon B * delta := by
      have hmul :=
        mul_le_mul_of_nonneg_left
          hdeltaLower (le_of_lt heps)
      simpa [mul_neg] using hmul
    unfold finiteTiltedValue
    linarith

/-- Integral version of the pointwise small-tilt lemma.

This is the form used for Laurent coefficient valuations and integral Smith
grades. -/
theorem finiteIntegralTilt_gt_minimum
    {B : ℕ}
    {m base delta : ℤ}
    (hmin : m ≤ base)
    (hdeltaLower : -((B : ℤ)) ≤ delta)
    (hfacePositive : base = m -> (1 : ℤ) ≤ delta) :
    (m : ℚ) <
      finiteTiltedValue
        (finiteTiltEpsilon (B : ℚ))
        (base : ℚ)
        (delta : ℚ) := by
  have hBq : (0 : ℚ) ≤ (B : ℚ) := by
    positivity
  have hfaceOrGapZ :
      base = m ∨ m + 1 ≤ base :=
    integer_min_or_unit_gap hmin
  have hfaceOrGapQ :
      (base : ℚ) = (m : ℚ) ∨
        (m : ℚ) + 1 ≤ (base : ℚ) := by
    rcases hfaceOrGapZ with hface | hgap
    · left
      exact_mod_cast hface
    · right
      exact_mod_cast hgap
  have hdeltaLowerQ :
      -((B : ℚ)) ≤ (delta : ℚ) := by
    exact_mod_cast hdeltaLower
  apply
    finiteTiltedValue_gt_minimum
      hBq hfaceOrGapQ hdeltaLowerQ
  intro hfaceQ
  have hfaceZ : base = m := by
    exact_mod_cast hfaceQ
  have hposZ : (1 : ℤ) ≤ delta :=
    hfacePositive hfaceZ
  exact_mod_cast hposZ

/-- Finite-support package of the small-tilt argument.

If all old support valuations are at least `m`, all tilt changes are bounded
below by `-B`, and every old minimal-face change is at least one, then the
explicit small rational tilt raises every supported value strictly above
the old minimum. -/
theorem finiteSupportTilt_strictly_raises_minimum
    {α : Type*}
    (S : Finset α)
    (B : ℕ)
    (m : ℤ)
    (base delta : α -> ℤ)
    (hmin :
      ∀ x ∈ S, m ≤ base x)
    (hdeltaLower :
      ∀ x ∈ S, -((B : ℤ)) ≤ delta x)
    (hfacePositive :
      ∀ x ∈ S, base x = m -> (1 : ℤ) ≤ delta x) :
    ∀ x ∈ S,
      (m : ℚ) <
        finiteTiltedValue
          (finiteTiltEpsilon (B : ℚ))
          (base x : ℚ)
          (delta x : ℚ) := by
  intro x hx
  exact
    finiteIntegralTilt_gt_minimum
      (hmin x hx)
      (hdeltaLower x hx)
      (hfacePositive x hx)

end

end HC4.Newton
