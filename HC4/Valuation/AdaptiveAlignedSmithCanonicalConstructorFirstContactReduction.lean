import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesConstructorReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalFirstContactPlanarEquivalence
import Mathlib.Tactic

/-!
# A19.40: constructor-refined honest first-contact producers

A19.36 deliberately stated the zero-clock producer against an arbitrary
presented rank-three terminal.  A19.36a subsequently proved that this is more
general than necessary: a canonical surviving terminal has no strict-low Smith
exponent, so the zero residual is blocker-only, and the presented blocker
retains its canonical first positive longitudinal departure.

This file propagates that stronger provenance into the honest first-contact
producer interface.  The positive residuals remain on the actual trace family,
unchanged from A19.35; only the zero branch is strengthened.

No endpoint is manufactured here.  The effect is to delete one impossible
constructor case and expose exactly the blocker/source geometry available to
the remaining zero first-contact construction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Constructor-refined source-to-first-contact checklist.  The zero branch is
now an actual canonical blocker with its complete rank-three geometry and its
first represented longitudinal departure. -/
structure AdaptiveAlignedSmithCanonicalConstructorFirstContactResidualProducer where
  blockerZeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) state)
      (_geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking D 0)
      (_hzero : state.rawDefect = 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber D.presented.family))
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e)
      (_hdeparture :
        HasFirstExactSmithExponentLongitudinalDeparture
          (longitudinalRightRecenterHom
            (K := K) (polynomialFamilySpecialFiber D.presented.family))
          D.blocker.exponent),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

  positiveSpecialFiberLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (_hspecial :
        L.exponent ∈ (polynomialFamilySpecialFiber state.family).support),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

  positiveEarlierActualLayer :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (hactual : HasPositiveActualParameterLayer state.family)
      (_hearly :
        firstPositiveActualParameterOrder state.family hactual <
          state.rawDefect),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

/-- Forget only the extra zero-constructor provenance.  The surviving zero
case is impossible by its already-green strict-low exclusion, while the blocker
case receives A18.5.88's first-departure certificate. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalConstructorFirstContactResidualProducer.toFirstContactResidualProducer
    (P : AdaptiveAlignedSmithCanonicalConstructorFirstContactResidualProducer (K := K)) :
    AdaptiveAlignedSmithCanonicalFirstContactResidualProducer (K := K) where
  zeroStrictLow := by
    intro state hrepair T hzero e he hpattern
    cases T with
    | blocker D geometry =>
        have he' :
            e ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
            using he
        exact P.blockerZeroStrictLow
          hrepair D geometry hzero e he' hpattern
          D.firstLongitudinalDeparture_on_presentedSpecialFiber
    | surviving D geometry =>
        have he' :
            e ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
            using he
        rcases D.noStrictLow_on_specialFiber e he' with
          ⟨hnotPure, hnotFirst, hnotSecond⟩
        rcases hpattern with hpure | hfirst | hsecond
        · exact (hnotPure hpure).elim
        · exact (hnotFirst hfirst).elim
        · exact (hnotSecond hsecond).elim

  positiveSpecialFiberLow := by
    intro state hrepair T hpositive L hspecial
    exact P.positiveSpecialFiberLow hrepair T hpositive L hspecial

  positiveEarlierActualLayer := by
    intro state hrepair T hpositive L hactual hearly
    exact P.positiveEarlierActualLayer
      hrepair T hpositive L hactual hearly

/-- An HC4 counterexample under the constructor-refined producer gives a
concrete planar Keller collision. -/
theorem hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_constructorFirstContactResidualProducer
    (P : AdaptiveAlignedSmithCanonicalConstructorFirstContactResidualProducer (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hninj : ¬ Function.Injective (mvGradientMap F)) :
    HC4.HasPlanarKellerCollision K :=
  hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_firstContactResidualProducer
    P.toFirstContactResidualProducer F hdet hninj

/-- Exact final equivalence with the stronger zero-constructor provenance. -/
theorem planarJC2_iff_hessianFour_gradient_injective_of_constructorFirstContactResidualProducer
    (P : AdaptiveAlignedSmithCanonicalConstructorFirstContactResidualProducer (K := K)) :
    HC4.PlanarJC2Injectivity K ↔
      ∀ F : MvPolynomial (Fin 4) K,
        HC4.Polynomial.hessianDeterminant F = 1 →
          Function.Injective (mvGradientMap F) :=
  planarJC2_iff_hessianFour_gradient_injective_of_firstContactResidualProducer
    P.toFirstContactResidualProducer

end

end HC4.Valuation
