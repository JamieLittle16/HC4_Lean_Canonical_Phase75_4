import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesLowLayerOrder
import HC4.Valuation.AdaptiveAlignedSmithCanonicalFirstContactPlanarCollision
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstDeparture
import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalResidualConstructorRefinement
import Mathlib.Tactic

/-!
# A19.41: source-native first-contact producer reduction

A19.35 correctly kept the positive Rees low layer on the actual terminal trace
state, but its resolver then passed only the normalized presented terminal to
the next adapter.  That discards useful provenance: at the reduction site we
still have the complete `AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry`
on exactly the same state as the low-layer witness.

This file stops throwing that information away.

* the zero-clock strict-low branch is constructor-refined to an actual blocker
  with its represented first longitudinal departure; surviving strict-low is
  impossible;
* both positive branches receive the *actual* aligned rank-three geometry on
  `state`, together with the low layer on `state.family`.

The normalized terminal presentation is therefore absent from the positive
producer API.  This removes the final presentation-scale mismatch from the
source-to-first-contact seam.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Strongest source-facing producer checklist currently justified by the
termination trace. -/
structure AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer where
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
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
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
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (hactual : HasPositiveActualParameterLayer state.family)
      (_hearly :
        firstPositiveActualParameterOrder state.family hactual <
          state.rawDefect),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

/-- The Rees-reduced trace is contradictory once the source-native producers
are supplied and every honest endpoint is impossible. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.impossible_of_sourceNativeFirstContactProducer
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (P : AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K))
    (hendpoint :
      ∀ E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K),
        False) :
    False := by
  let reached := T.trace.reachedRankThree
  have hrepair : reached.state.repair = rankOneRepairState 0 := by
    simpa [reached] using T.reachedRankThree_repair_eq hsrepair
  have hreduced :
      reached.state.rawDefect = 0 ∨
        Nonempty
          (CanonicalPositiveTransverseReesLowLayer
            reached.state.rawDefect reached.state.family) := by
    simpa [reached] using T.terminalReduced
  rcases hreduced with hzero | hlow
  · let terminal := reached.geometry.toPresentedTerminal
    by_cases hstrict :
        ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 terminal.specialFiber,
          IsPureLongitudinalSmithPattern e ∨
          IsLowNegativeFirstSmithPattern e ∨
          IsLowNegativeSecondSmithPattern e
    · rcases hstrict with ⟨e, he, hpattern⟩
      cases terminal with
      | blocker D geometry =>
          have he' :
              e ∈ smithProjectedSupport (1 : Fin 4) 2 3
                (polynomialFamilySpecialFiber D.presented.family) := by
            simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
              using he
          rcases P.blockerZeroStrictLow
              hrepair D geometry hzero e he' hpattern
              D.firstLongitudinalDeparture_on_presentedSpecialFiber with ⟨E⟩
          exact hendpoint E
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
    · have hno : terminal.HasNoStrictLowSmithPatterns := by
        intro e he
        constructor
        · intro hpure
          exact hstrict ⟨e, he, Or.inl hpure⟩
        constructor
        · intro hfirst
          exact hstrict ⟨e, he, Or.inr (Or.inl hfirst)⟩
        · intro hsecond
          exact hstrict ⟨e, he, Or.inr (Or.inr hsecond)⟩
      exact terminal.conformalDegreeTwoFace_impossible_of_source_rawDefect_eq_zero
        hzero hno
  · rcases hlow with ⟨L⟩
    have hpositive : 0 < reached.state.rawDefect := by
      have hearly := L.early
      omega
    rcases L.specialFiber_or_earlierActualLayer with hspecial | hearlier
    · rcases P.positiveSpecialFiberLow
          hrepair reached.geometry hpositive L hspecial with ⟨E⟩
      exact hendpoint E
    · rcases hearlier with ⟨hactual, hearly⟩
      rcases P.positiveEarlierActualLayer
          hrepair reached.geometry hpositive L hactual hearly with ⟨E⟩
      exact hendpoint E

/-- HC4 front door with no positive terminal-presentation loss. -/
theorem gradient_injective_of_hessianDeterminant_one_of_sourceNativeFirstContactProducer_of_endpointImpossible
    (P : AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K))
    (hendpoint :
      ∀ E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K),
        False)
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  intro p q hgrad
  by_contra hpq
  have hcoll : HasExactGradientCollision F p q := by
    intro i
    exact congrFun hgrad i
  let E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K) :=
    zeroDefectCollisionEntry_ofExactCollision_autoDegree
      F p q hdet hpq hcoll
  let trace := E.positiveRankOneReesReducedTrace
    canonicalAdaptiveAlignedSmithRepairRanking 0
  exact trace.impossible_of_sourceNativeFirstContactProducer
    (E.positiveReentry_repair 0) P hendpoint

/-- Under the source-native producer, any HC4 counterexample yields a concrete
planar Keller collision. -/
theorem hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_sourceNativeFirstContactProducer
    (P : AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hninj : ¬ Function.Injective (mvGradientMap F)) :
    HC4.HasPlanarKellerCollision K := by
  classical
  by_contra hno
  have hendpoint :
      ∀ E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K),
        False := by
    intro E
    exact hno E.hasPlanarKellerCollision
  exact hninj
    (gradient_injective_of_hessianDeterminant_one_of_sourceNativeFirstContactProducer_of_endpointImpossible
      P hendpoint F hdet)

/-- Planar JC2 plus the source-native producer closes HC4, with JC2 used only
at the honest two-zero endpoint. -/
theorem gradient_injective_of_hessianDeterminant_one_of_JC2_of_sourceNativeFirstContactProducer
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) :=
  gradient_injective_of_hessianDeterminant_one_of_sourceNativeFirstContactProducer_of_endpointImpossible
    P (fun E => E.impossible_of_JC2 hJC2) F hdet

end

end HC4.Valuation
