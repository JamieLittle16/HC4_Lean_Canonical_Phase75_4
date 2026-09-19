import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
import HC4.Valuation.AdaptiveAlignedSmithExactExponentMixedBlocker
import Mathlib.Tactic

/-!
# A19.50: exact mixedness at the zero strict-low blocker

A19.48 replaces the classifier-selected blocker exponent by the actual
strict-low exponent occurring on the represented terminal special fibre.
A19.49 exposes the corresponding two-endpoint residual normal form.

The older canonical blocker rigidity is stronger still: every blocker has
exact same-Smith-exponent mixed ordinary-degree support after longitudinal
right recentering.  Applying that theorem to the A19.48 strict-low blocker
shows that the final zero-clock residual is not merely a univariate
factorisation.  It already carries the same exact-exponent mixedness and first
longitudinal departure used by the stationary source pipeline.

No terminal cocharacter, JC2 input, or progress claim occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- The actual represented strict-low exponent has exact same-exponent mixed
ordinary-degree support after honest longitudinal recentering. -/
theorem zeroStrictLow_exactExponentMixedDegree
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    ExactSmithExponentMixedDegreeData
      (longitudinalRightRecenterHom
        (K := K) (polynomialFamilySpecialFiber D.presented.family)) e := by
  let B := D.strictLowBlocker e he hpattern
  have h := B.exactExponentMixedDegree
  rw [D.strictLowBlocker_rawSpecialFiber e he hpattern] at h
  exact h

/-- Consolidated source-facing datum for the final zero strict-low seam.
The residual normal form, exact same-exponent mixedness, and canonical first
longitudinal departure all belong to the *same actual strict-low exponent* on
the same represented special fibre. -/
theorem zeroStrictLow_stationarySeed
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
        (polynomialFamilySpecialFiber D.presented.family) e ∧
      ExactSmithExponentMixedDegreeData
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber D.presented.family)) e ∧
      HasFirstExactSmithExponentLongitudinalDeparture
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber D.presented.family)) e := by
  exact ⟨
    D.zeroStrictLow_residualNormalForm e he hpattern,
    D.zeroStrictLow_exactExponentMixedDegree e he hpattern,
    D.strictLowBlocker_firstLongitudinalDeparture e he hpattern
  ⟩

end AdaptiveAlignedSmithCanonicalPresentedBlocker

end

end HC4.Valuation
