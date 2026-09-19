import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesFinalOutcome
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstContactHessian
import Mathlib.Tactic

/-!
# A19.53: producer-free zero-clock strict-low terminal

A19.46 already proves that every positive reached rank-three state exits by
strict global macro progress, while a zero-clock terminal with no strict-low
Smith support is impossible.  Its only remaining non-constructive seam is the
`AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactProducer` requested in the
zero-clock blocker / strict-low branch.

A19.48--A19.52 have now made that branch concrete.  An actual represented
strict-low exponent can be retained on the actual blocker, together with raw
zero, its exact mixed-degree normal form, its first later longitudinal
departure, and honest Hessian first-contact geometry.

This file therefore removes the producer from the live global/local boundary.
The terminal alternative is data already present in the reached state, not a
promise to manufacture a later endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The actual local object left after global rank-three closure: a literal
zero-clock rank-one reached state, an actual canonical presented blocker on
that state, and an actually represented strict-low Smith exponent. -/
structure AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
    (state : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  repair_eq : state.repair = rankOneRepairState 0
  blocker : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) state
  source_zero : state.rawDefect = 0
  exponent : SmithSupportExponent
  mem :
    exponent ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber blocker.presented.family)
  pattern :
    IsPureLongitudinalSmithPattern exponent ∨
    IsLowNegativeFirstSmithPattern exponent ∨
    IsLowNegativeSecondSmithPattern exponent

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- A19.52 applies directly to the retained blocker/exponent.  Thus packaging
the terminal alternative loses none of the normal-form, departure, or Hessian
first-contact information already proved. -/
theorem zeroClockFirstContactPacket
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    T.blocker.presented.rawDefect = 0 ∧
      T.blocker.blocker.aligned.endpoint.defect = 0 ∧
      AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
        (polynomialFamilySpecialFiber T.blocker.presented.family) T.exponent ∧
      ExactSmithExponentMixedDegreeData
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber T.blocker.presented.family))
        T.exponent ∧
      HasFirstExactSmithExponentLongitudinalDeparture
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber T.blocker.presented.family))
        T.exponent ∧
      AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber T.blocker.presented.family))
        (0 : Fin 4) := by
  exact T.blocker.zeroStrictLow_zeroClockFirstContactPacket
    T.source_zero T.exponent T.mem T.pattern

end AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- **A19.53 producer-free final local episode outcome.**

A Rees-reduced canonical rank-one episode either exits by genuine global macro
progress or retains the concrete zero-clock strict-low blocker which remains to
be discharged locally.  In particular, no first-contact producer or arbitrary
endpoint constructor is assumed. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_or_zeroStrictLowTerminal
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
          (K := K) T.trace.reachedRankThree.state) := by
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
      | blocker D _geometry =>
          rw [hterm] at he
          have he' :
              e ∈ smithProjectedSupport (1 : Fin 4) 2 3
                (polynomialFamilySpecialFiber D.presented.family) := by
            simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
              AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState]
              using he
          exact Or.inr ⟨{
            repair_eq := hrepair
            blocker := D
            source_zero := hzero'
            exponent := e
            mem := he'
            pattern := hpattern
          }⟩
      | surviving D _geometry =>
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

/-- At a globally terminal reached state, A19.53 leaves an actual strict-low
zero-clock blocker, with A19.52 available directly through
`zeroClockFirstContactPacket`. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.zeroStrictLowTerminal_of_no_globalProgress
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
        (K := K) T.trace.reachedRankThree.state) := by
  rcases T.globalProgress_or_zeroStrictLowTerminal hsrepair with
    ⟨target, hprogress⟩ | hterminalData
  · exact (hterminal target hprogress).elim
  · exact hterminalData

end

end HC4.Valuation
