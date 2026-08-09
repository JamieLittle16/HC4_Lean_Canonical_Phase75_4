import HC4.Newton.SmithValuationTiltAdapter
import Mathlib.Tactic

/-!
# Smith separator contradiction to integral pole minimality

Phase 93.8 gives the exact rational conformal tilt

    epsilon = 1 / (2(B+1))

and proves that a positive Smith separator raises every supported
normalised valuation strictly above the old minimum.

The restart proof then says: clear denominators.  This file formalises that
step exactly.

Let

    D = 2(B+1).

Then

    D * (base + epsilon * delta) = D*base + delta.

The right-hand side is integral whenever the old valuation and Smith
derivative are integral.  Thus a strict rational improvement is equivalent
to an honest integral rescaled-weight improvement.

We package the minimality property needed here as follows: against every
explicit Phase 93.6 Smith separator, the corresponding denominator-cleared
integral tilt must leave at least one supported coefficient at or below the
rescaled old minimum.  A separator positive on the whole old minimum face
contradicts this property.

This is deliberately the minimal finite interface.  A later adapter must
show that pole-minimal pointed Laurent models from the global extraction
satisfy this finite predicate because the denominator-cleared conformal
tilts are legal cocharacters fixing the primitive x-direction.
-/

namespace HC4.Newton

noncomputable section

/-- Denominator clearing the explicit Phase 93.7 tilt. -/
def finiteTiltDenominator
    (B : ℕ) : ℕ :=
  2 * (B + 1)

/-- The clearing denominator is strictly positive. -/
theorem finiteTiltDenominator_pos
    (B : ℕ) :
    0 < finiteTiltDenominator B := by
  unfold finiteTiltDenominator
  omega

/-- The rational epsilon from Phase 93.7 is exactly the reciprocal of the
natural clearing denominator. -/
theorem finiteTiltEpsilon_eq_denominator_inv
    (B : ℕ) :
    finiteTiltEpsilon (B : ℚ) =
      1 / (finiteTiltDenominator B : ℚ) := by
  unfold finiteTiltEpsilon finiteTiltDenominator
  push_cast
  ring

/-- Denominator-cleared integral tilted value. -/
def finiteIntegralRescaledTilt
    (B : ℕ)
    (base delta : ℤ) : ℤ :=
  (finiteTiltDenominator B : ℤ) * base + delta

/-- **Clearing denominators identity.**
Scaling the rational small tilt by its positive denominator gives the
integral rescaled tilt exactly. -/
theorem finiteIntegralRescaledTilt_cast
    (B : ℕ)
    (base delta : ℤ) :
    (finiteTiltDenominator B : ℚ) *
        finiteTiltedValue
          (finiteTiltEpsilon (B : ℚ))
          (base : ℚ)
          (delta : ℚ) =
      (finiteIntegralRescaledTilt B base delta : ℤ) := by
  have hDpos :
      (0 : ℚ) < (finiteTiltDenominator B : ℚ) := by
    exact_mod_cast finiteTiltDenominator_pos B
  have hDne :
      (finiteTiltDenominator B : ℚ) ≠ 0 :=
    ne_of_gt hDpos
  rw [finiteTiltEpsilon_eq_denominator_inv]
  unfold finiteTiltedValue
  unfold finiteIntegralRescaledTilt
  push_cast
  field_simp [hDne]

/-- A strict rational small-tilt improvement gives a strict
denominator-cleared integral improvement. -/
theorem finiteIntegralRescaledTilt_gt_of_rational_gt
    (B : ℕ)
    (m base delta : ℤ)
    (h :
      (m : ℚ) <
        finiteTiltedValue
          (finiteTiltEpsilon (B : ℚ))
          (base : ℚ)
          (delta : ℚ)) :
    (finiteTiltDenominator B : ℤ) * m <
      finiteIntegralRescaledTilt B base delta := by
  have hDposQ :
      (0 : ℚ) < (finiteTiltDenominator B : ℚ) := by
    exact_mod_cast finiteTiltDenominator_pos B
  have hmul :
      (finiteTiltDenominator B : ℚ) * (m : ℚ) <
        (finiteTiltDenominator B : ℚ) *
          finiteTiltedValue
            (finiteTiltEpsilon (B : ℚ))
            (base : ℚ)
            (delta : ℚ) :=
    mul_lt_mul_of_pos_left h hDposQ
  rw [finiteIntegralRescaledTilt_cast] at hmul
  exact_mod_cast hmul

/-- Integral value obtained from the explicit Smith separator after clearing
the Phase 93.7 small-tilt denominator. -/
def smithIntegralSeparatorTilt
    (k l : ℕ)
    (base : SmithSupportExponent -> ℤ)
    (e : SmithSupportExponent) : ℤ :=
  finiteIntegralRescaledTilt
    (smithExtremeSeparatorBound k l)
    (base e)
    (smithSeparatorDelta k l e)

/-- Rescaled old minimum associated to the same denominator clearing. -/
def smithRescaledOldMinimum
    (k l : ℕ)
    (m : ℤ) : ℤ :=
  (finiteTiltDenominator
      (smithExtremeSeparatorBound k l) : ℤ) * m

/-- The finite pole-minimality condition needed for the Smith balance
argument.

For every explicit Smith separator, its denominator-cleared integral
conformal tilt fails to improve the old minimum everywhere on the support. -/
def IsPoleMinimalAgainstSmithSeparators
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ) : Prop :=
  ∀ k l : ℕ,
    ∃ e ∈ S,
      smithIntegralSeparatorTilt k l base e ≤
        smithRescaledOldMinimum k l m

/-- The Phase 93.8 rational improvement becomes a strict integral
improvement at every supported exponent. -/
theorem smithFiniteSupportIntegralTilt_strictly_raises_minimum
    (S : Finset SmithSupportExponent)
    (k l : ℕ)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hfacePositive :
      ∀ e ∈ S,
        base e = m ->
          (1 : ℤ) ≤ smithSeparatorDelta k l e) :
    ∀ e ∈ S,
      smithRescaledOldMinimum k l m <
        smithIntegralSeparatorTilt k l base e := by
  have hrat :=
    smithFiniteSupportTilt_strictly_raises_minimum
      S k l m base hmin hfacePositive
  intro e he
  have heRat := hrat e he
  unfold smithRescaledOldMinimum
  unfold smithIntegralSeparatorTilt
  exact
    finiteIntegralRescaledTilt_gt_of_rational_gt
      (smithExtremeSeparatorBound k l)
      m (base e) (smithSeparatorDelta k l e)
      heRat

/-- **Pole-minimality excludes a positive explicit Smith separator.**
If the finite model is pole-minimal against the denominator-cleared
conformal tilts, then no explicit Phase 93.6 separator can be positive on
every monomial of the old minimum face. -/
theorem poleMinimal_no_positive_smithSeparator
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (k l : ℕ) :
    ¬ (∀ e ∈ S,
      base e = m ->
        (1 : ℤ) ≤ smithSeparatorDelta k l e) := by
  intro hfacePositive
  have himprove :=
    smithFiniteSupportIntegralTilt_strictly_raises_minimum
      S k l m base hmin hfacePositive
  rcases hpole k l with ⟨e, heS, hnotImprove⟩
  have hstrict := himprove e heS
  omega

/-- Equivalent witness form: under pole minimality, every explicit Smith
separator has some old minimal-face exponent on which it is nonpositive,
provided the minimum is attained.

This is the form used by the later finite grade argument. -/
theorem poleMinimal_exists_nonpositive_face_grade
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m)
    (k l : ℕ) :
    ∃ e ∈ S,
      base e = m ∧
      smithSeparatorDelta k l e ≤ 0 := by
  by_contra hnone
  have hpositive :
      ∀ e ∈ S,
        base e = m ->
          (1 : ℤ) ≤ smithSeparatorDelta k l e := by
    intro e heS hemin
    have hnotLe :
        ¬ smithSeparatorDelta k l e ≤ 0 := by
      intro hle
      apply hnone
      exact ⟨e, heS, hemin, hle⟩
    omega
  exact
    (poleMinimal_no_positive_smithSeparator
      S m base hpole hmin k l)
      hpositive

end

end HC4.Newton
