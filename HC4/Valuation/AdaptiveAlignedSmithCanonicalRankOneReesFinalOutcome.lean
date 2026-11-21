import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSourceNativeFirstContactReduction
import Mathlib.Tactic

/-!
# A19.46: one local first-contact obligation after global rank-three closure

A19.45 removes every positive reached rank-three state from the local terminal
problem: positive raw defect has an honest successor in the already
well-founded global macro order.  Thus the only reached state which can remain
locally terminal has literal raw defect zero.

At zero defect the existing constructor refinement is already sharp.  A
strict-low represented terminal is either

* a surviving endpoint, impossible by the surviving strict-low exclusion; or
* an actual blocker, carrying its represented first longitudinal departure.

If there is no strict-low pattern, the existing conformal zero-clock theorem
is contradictory.  Hence only one genuine source-to-endpoint constructor is
left: zero-defect blocker + strict-low pattern + first longitudinal departure.

This file records exactly that one-field interface and no more.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The sole local geometric adapter remaining after A19.44/A19.45 route every
positive reached rank-three node back to the outer global recursion. -/
structure AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactProducer where
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

/-- **A19.46 final local episode outcome.**

A Rees-reduced canonical rank-one episode either exits by genuine global macro
progress, or reaches the single honest first-contact endpoint.  No positive
low-layer producer appears in this statement. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_or_honestFirstContact
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (P : AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactProducer (K := K)) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) ∨
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) := by
  rcases T.reachedRankThree_zero_or_globalProgress hsrepair with
    hzero | hprogress
  · let reached := T.trace.reachedRankThree
    let terminal := reached.geometry.toPresentedTerminal
    have hrepair : reached.state.repair = rankOneRepairState 0 := by
      simpa [reached] using T.reachedRankThree_repair_eq hsrepair
    have hzero' : reached.state.rawDefect = 0 := by
      simpa [reached] using hzero
    by_cases hstrict :
        ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 terminal.specialFiber,
          IsPureLongitudinalSmithPattern e ∨
          IsLowNegativeFirstSmithPattern e ∨
          IsLowNegativeSecondSmithPattern e
    · rcases hstrict with ⟨e, he, hpattern⟩
      cases hterm : terminal with
      | blocker D geometry =>
          rw [hterm] at he
          have he' :
              e ∈ smithProjectedSupport (1 : Fin 4) 2 3
                (polynomialFamilySpecialFiber D.presented.family) := by
            simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
              AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState]
              using he
          exact Or.inr
            (P.blockerZeroStrictLow
              hrepair D geometry hzero' e he' hpattern
              D.firstLongitudinalDeparture_on_presentedSpecialFiber)
      | surviving D geometry =>
          rw [hterm] at he
          have he' :
              e ∈ smithProjectedSupport (1 : Fin 4) 2 3
                (polynomialFamilySpecialFiber D.presented.family) := by
            simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
              AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState]
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
      exact
        (terminal.conformalDegreeTwoFace_impossible_of_source_rawDefect_eq_zero
          hzero' hno).elim
  · exact Or.inl hprogress

/-- If the reached state is globally terminal, A19.46 therefore produces the
honest first-contact endpoint from the single zero-blocker adapter. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.honestFirstContact_of_no_globalProgress
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (P : AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactProducer (K := K))
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) :
    Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) := by
  rcases T.globalProgress_or_honestFirstContact hsrepair P with
    ⟨target, hprogress⟩ | hendpoint
  · exact (hterminal target hprogress).elim
  · exact hendpoint

end

end HC4.Valuation
