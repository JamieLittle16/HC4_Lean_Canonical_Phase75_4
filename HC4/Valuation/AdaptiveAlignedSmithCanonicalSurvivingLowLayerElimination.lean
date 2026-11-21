import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalResidualConstructorRefinement
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesLowLayerOrder
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionParity
import Mathlib.Tactic

/-!
# A19.28: a surviving positive low layer is genuinely earlier in the parameter

A19.25 used the symmetric separator sign to exclude the three strict-low
patterns on a canonical surviving special fibre.  The surviving-wall record
contains one further fact which was not needed there: `noWLinear` on the
attained wall level.

For the canonical surviving wall the affine base, transverse weight, and level
are all zero.  Hence every projected special-fibre exponent lies on that wall
level, and the fourth A19.17 low pattern (`w`-linear) is excluded as well.

Combining this with A19.27 removes the order-zero half of the positive low
layer completely.  Any surviving positive Rees low layer therefore produces a
genuine first positive actual source layer strictly before the determinant
clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- No `w`-linear exponent occurs on the actual raw special fibre of a
canonical surviving endpoint. -/
theorem AdaptiveAlignedSmithSurvivingWallEndpoint.noWLinear_on_rawSpecialFiber
    {degreeCap : ℕ}
    (W : AdaptiveAlignedSmithSurvivingWallEndpoint (K := K) degreeCap)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      W.aligned.endpoint.rawSpecialFiber) :
    ¬ IsWLinearSmithPattern e := by
  have hreal := W.wall.realization.realizes e he
  have hlevel : W.wall.base e = W.wall.level := by
    rw [W.wall_transverseWeight_eq_zero, W.wall_offset_eq_zero] at hreal
    simp at hreal
    rw [W.wall_level_eq_zero]
    exact hreal
  exact W.wall.noWLinear e he hlevel

/-- A represented surviving terminal excludes all four concrete A19 low-layer
patterns on its special fibre. -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.noPositiveReesLowPattern_on_specialFiber
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family)) :
    ¬ IsPureLongitudinalSmithPattern e ∧
      ¬ IsLowNegativeFirstSmithPattern e ∧
      ¬ IsLowNegativeSecondSmithPattern e ∧
      ¬ IsWLinearSmithPattern e := by
  rcases D.noStrictLow_on_specialFiber e he with
    ⟨hpure, hfirst, hsecond⟩
  have he' : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      D.wall.aligned.endpoint.rawSpecialFiber := by
    simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq] using he
  exact ⟨hpure, hfirst, hsecond,
    D.wall.noWLinear_on_rawSpecialFiber e he'⟩

/-- A positive Rees low layer on a represented surviving terminal cannot be a
special-fibre monomial.  Its first genuine positive actual parameter layer is
strictly earlier than the represented determinant clock. -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.positiveReesLowLayer_firstActual_lt
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (L : CanonicalPositiveTransverseReesLowLayer
      D.presented.rawDefect D.presented.family) :
    ∃ h : HasPositiveActualParameterLayer D.presented.family,
      firstPositiveActualParameterOrder D.presented.family h <
        D.presented.rawDefect := by
  rcases L.specialFiber_or_firstPositiveActual_lt with hspecial | hearly
  · exfalso
    have heProjected :
        smithSupportExponentOf (1 : Fin 4) 2 3 L.exponent ∈
          smithProjectedSupport (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber D.presented.family) := by
      unfold smithProjectedSupport
      exact Finset.mem_image.mpr ⟨L.exponent, hspecial, rfl⟩
    rcases D.noPositiveReesLowPattern_on_specialFiber
        (smithSupportExponentOf (1 : Fin 4) 2 3 L.exponent) heProjected with
      ⟨hnotPure, hnotFirst, hnotSecond, hnotW⟩
    rcases L.pattern with hpure | hfirst | hsecond | hw
    · exact hnotPure hpure
    · exact hnotFirst hfirst
    · exact hnotSecond hsecond
    · exact hnotW hw
  · exact hearly

end

end HC4.Valuation
