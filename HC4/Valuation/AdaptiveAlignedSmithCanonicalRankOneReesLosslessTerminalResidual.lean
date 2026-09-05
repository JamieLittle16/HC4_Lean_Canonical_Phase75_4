import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRelativeFirstContactReduction
import Mathlib.Tactic

/-!
# A19.54: lossless producer-free Rees terminal residual

The source-native A19.41/A19.42 reduction already identified the correct
positive terminal data, but exposed it through producer fields.  A19.53 then
removed the corresponding producer from the zero-clock strict-low branch.

This file performs the same cleanup simultaneously for all terminal branches.
After the existing raw-defect Rees-reduced trace has exhausted every honest
recursive step, the final actual trace state retains exactly one of:

* the concrete zero-clock strict-low blocker of A19.53;
* a positive low Rees exponent which is literally present on the actual
  special fibre, together with the complete aligned rank-three geometry on
  that same state; or
* the canonical relative first deformation of A19.42, again together with the
  complete aligned rank-three geometry and the low-layer witness which forced
  it.

No endpoint producer, repair-only successor, presentation-scale transport, or
new recursion is introduced.  In particular this theorem deliberately does
not use A19.44's later compact `globalProgress` collapse: the positive geometry
is retained exactly where A19.41 proved it was available.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The three actual residual geometries which may remain at the final state of
the Rees-reduced rank-one trace. -/
inductive AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalResidual
    (state : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1)

  | zeroStrictLow
      (data : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
        (K := K) state)

  | positiveSpecialFiberLow
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (positive : 0 < state.rawDefect)
      (lowLayer : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (special :
        lowLayer.exponent ∈
          (polynomialFamilySpecialFiber state.family).support)

  | positiveEarlierRelative
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (positive : 0 < state.rawDefect)
      (lowLayer : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (relative : AdaptiveAlignedSmithCanonicalEarlierActualRelativeContactData
        (K := K) state)

/-- Complete producer-free terminal packet.  The canonical rank-one repair
identity is kept beside the residual so later consumers never have to recover
it from an erased trace. -/
structure AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalData
    (state : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  repair_eq : state.repair = rankOneRepairState 0
  residual : AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalResidual
    (K := K) state

namespace AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalData

/-- The zero-clock constructor immediately exposes the full A19.51/A19.52
packet without any endpoint producer. -/
theorem zeroStrictLow_firstContactPacket
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalData
      (K := K) state)
    (hzero : ∃ T, D.residual =
      AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalResidual.zeroStrictLow T) :
    ∃ T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData (K := K) state,
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
  rcases hzero with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  exact T.zeroClockFirstContactPacket

end AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalData

/-- **A19.54 lossless terminal extraction.**

This is the producer-free form of the A19.41/A19.42 source-native split.  The
only recursion used to reach this point is the already-certified raw-defect
recursion inside `rankOneReesReducedTrace`. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.losslessTerminalData
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalRankOneReesLosslessTerminalData
        (K := K) T.trace.reachedRankThree.state) := by
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
      cases hterm : terminal with
      | blocker D _geometry =>
          rw [hterm] at he
          have he' :
              e ∈ smithProjectedSupport (1 : Fin 4) 2 3
                (polynomialFamilySpecialFiber D.presented.family) := by
            simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
              AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState]
              using he
          exact ⟨{
            repair_eq := hrepair
            residual := .zeroStrictLow {
              repair_eq := hrepair
              blocker := D
              source_zero := hzero
              exponent := e
              mem := he'
              pattern := hpattern
            }
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
          hzero hno).elim
  · rcases hlow with ⟨L⟩
    have hpositive : 0 < reached.state.rawDefect := by
      have hearly := L.early
      omega
    rcases L.specialFiber_or_earlierActualLayer with hspecial | hearlier
    · exact ⟨{
        repair_eq := hrepair
        residual := .positiveSpecialFiberLow
          reached.geometry hpositive L hspecial
      }⟩
    · rcases hearlier with ⟨hactual, hearly⟩
      let R :=
        AdaptiveAlignedSmithCanonicalEarlierActualRelativeContactData.ofEarlierActual
          reached.state hactual hearly
      exact ⟨{
        repair_eq := hrepair
        residual := .positiveEarlierRelative
          reached.geometry hpositive L R
      }⟩

end

end HC4.Valuation