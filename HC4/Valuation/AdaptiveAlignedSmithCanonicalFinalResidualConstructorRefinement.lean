import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalResidualReduction
import HC4.Valuation.AdaptiveAlignedSmithClassifierDispatcher
import HC4.Valuation.AdaptiveSmithWallExposure
import HC4.Valuation.CoupledSmithWallClosure
import Mathlib.Tactic

/-!
# A19.25: refine the final residuals by terminal constructor

The three residual fields isolated in A19.24 are not independent of the
canonical terminal constructor.

* A canonical surviving wall has zero primary Smith base and zero affine
  realisation.  Hence every projected support exponent lies on its surviving
  level.  The already-proved surviving-shape sign theorem makes the symmetric
  Smith separator nonnegative there, excluding the three genuinely strict-low
  patterns.
* A canonical blocker carries an actual blocker exponent in the special
  fibre.  On the represented polynomial family that coefficient has parameter
  order zero, while every blocker pattern has total transverse degree at most
  one.  At positive determinant clock the A19 transverse Rees coefficient
  inequality would therefore say `2*Delta <= Delta`, a contradiction.

Thus zero-clock strict-low residuals are blocker-only, while a successful
positive Rees coefficient bound is surviving-only.  No new geometry or
termination relation is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Every exponent on a canonical surviving wall excludes the three strict-low
Smith patterns. -/
theorem AdaptiveAlignedSmithSurvivingWallEndpoint.noStrictLow_on_rawSpecialFiber
    {degreeCap : ℕ}
    (W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) degreeCap)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      W.aligned.endpoint.rawSpecialFiber) :
    ¬ IsPureLongitudinalSmithPattern e ∧
      ¬ IsLowNegativeFirstSmithPattern e ∧
      ¬ IsLowNegativeSecondSmithPattern e := by
  have hreal := W.wall.realization.realizes e he
  have hlevel : W.wall.base e = W.wall.level := by
    rw [W.wall_transverseWeight_eq_zero, W.wall_offset_eq_zero] at hreal
    simp at hreal
    rw [W.wall_level_eq_zero]
    exact hreal
  have hshape := W.wall.survivingShape e he hlevel
  have hnonneg : 0 ≤ smithSeparatorDelta 1 1 e :=
    smithSeparatorDelta_one_one_nonnegative_of_generalShape e hshape
  have hformula := smithSeparatorDelta_one_one_formula e
  constructor
  · intro hpure
    rcases hpure with ⟨hb, hc, hd⟩
    rw [hformula] at hnonneg
    rw [hb, hc, hd] at hnonneg
    omega
  constructor
  · intro hfirst
    rcases hfirst with ⟨hb, hc, hd⟩
    rw [hformula] at hnonneg
    rw [hb, hc, hd] at hnonneg
    omega
  · intro hsecond
    rcases hsecond with ⟨hb, hc, hd⟩
    rw [hformula] at hnonneg
    rw [hb, hc, hd] at hnonneg
    omega

/-- A represented surviving terminal has no strict-low exponent on its actual
special fibre. -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.noStrictLow_on_specialFiber
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family)) :
    ¬ IsPureLongitudinalSmithPattern e ∧
      ¬ IsLowNegativeFirstSmithPattern e ∧
      ¬ IsLowNegativeSecondSmithPattern e := by
  have he' : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      D.wall.aligned.endpoint.rawSpecialFiber := by
    simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq] using he
  exact D.wall.noStrictLow_on_rawSpecialFiber e he'

/-- The distinguished canonical blocker exponent has transverse degree at most
one. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.canonicalTransverseDegree_le_one
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    {d : Fin 4 →₀ ℕ}
    (hde : smithSupportExponentOf (1 : Fin 4) 2 3 d = B.exponent) :
    canonicalTransverseDegree d ≤ 1 := by
  rcases B.pattern with hpure | hfirst | hsecond | hw
  · have h := hpure
    rw [← hde] at h
    rcases h with ⟨h1, h2, h3⟩
    simp [smithSupportExponentOf] at h1 h2 h3
    simp [canonicalTransverseDegree, h1, h2, h3]
  · have h := hfirst
    rw [← hde] at h
    rcases h with ⟨h1, h2, h3⟩
    simp [smithSupportExponentOf] at h1 h2 h3
    simp [canonicalTransverseDegree, h1, h2, h3]
  · have h := hsecond
    rw [← hde] at h
    rcases h with ⟨h1, h2, h3⟩
    simp [smithSupportExponentOf] at h1 h2 h3
    simp [canonicalTransverseDegree, h1, h2, h3]
  · have h := hw
    rw [← hde] at h
    rcases h with ⟨h1, h2, h3⟩
    simp [smithSupportExponentOf] at h1 h2 h3
    simp [canonicalTransverseDegree, h1, h2, h3]

/-- At positive represented clock, a canonical blocker cannot satisfy the A19
coefficient bound: its own special-fibre blocker coefficient has order zero
and transverse degree at most one. -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.not_positiveTransverseReesCoefficientBound
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (hpositive : 0 < D.presented.rawDefect) :
    ¬ HasCanonicalPositiveTransverseReesCoefficientBound
        D.presented.rawDefect D.presented.family := by
  intro hbound
  rcases smithProjectedSupport_realised (1 : Fin 4) 2 3
      D.blocker.aligned.endpoint.rawSpecialFiber
      D.blocker.exponent D.blocker.mem with
    ⟨d, hdSpecial, hde⟩
  have hdSpecial' :
      d ∈ (polynomialFamilySpecialFiber D.presented.family).support := by
    simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq] using hdSpecial
  have hdata := (mem_polynomialFamilySpecialFiber_support_iff
    D.presented.family d).1 hdSpecial'
  have hd : d ∈ D.presented.family.support := hdata.1
  have horder : smithFamilyCoefficientOrder D.presented.family d = 0 :=
    (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
      D.presented.family hd).2 hdSpecial'
  have hdegree : canonicalTransverseDegree d ≤ 1 :=
    D.blocker.canonicalTransverseDegree_le_one hde
  have hineq := hbound d hd
  rw [canonicalPositiveTransverseReesWeight_finsupp, horder] at hineq
  simp only [zero_mul, zero_add] at hineq
  have hcases : canonicalTransverseDegree d = 0 ∨
      canonicalTransverseDegree d = 1 := by omega
  rcases hcases with hzero | hone
  · rw [hzero] at hineq
    omega
  · rw [hone] at hineq
    omega

end

end HC4.Valuation
