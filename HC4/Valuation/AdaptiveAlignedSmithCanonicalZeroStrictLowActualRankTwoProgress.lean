import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleAwareHessianChart
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# Presentation-aware actual-rank-two progress for the zero strict-low endgame

The late A19 frontiers increasingly return an
`AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart` on the literal
presented blocker state.  This file gives that geometric object one uniform
global consumer.

The pure presentation from the source to the represented blocker is not itself
progress.  The actual nonzero Hessian minor on that represented family licenses
the canonical rank-one to rank-two promotion there; the resulting target is
then strictly below the honest source in the existing global macro order.

No bare repair relabelling is exported: the progress packet retains the actual
Hessian chart which justified the promotion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A presentation-aware rank-two promotion whose soundness payload is a
literal actual Hessian chart on the represented blocker family. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1) where
  geometry :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart D.presented
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = D.presented.withRepairOnly (rankTwoRepairState complexity)
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target D.presented
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- Attach the finite rank promotion only after the actual represented-state
Hessian chart has been retained. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart D.presented) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress
      RR D complexity := by
  let target := D.presented.withRepairOnly (rankTwoRepairState complexity)

  have hpresentedRepair :
      D.presented.repair = rankOneRepairState complexity := by
    rcases D.sourcePresentation with ⟨hmove⟩
    rw [hmove.repair_eq]
    exact hsrepair

  have hrepair :
      RepairProgress D.presented.repair (rankTwoRepairState complexity) := by
    simpa [hpresentedRepair] using
      rankOne_to_rankTwo_repairProgress complexity

  have hpresented :
      CertifiedSameScaleEpisodeProgress RR target D.presented := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair

  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [show target.repair = rankTwoRepairState complexity by rfl, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)

  exact {
    geometry := C
    target := target
    target_eq := rfl
    presentedProgress := hpresented
    globalProgress := hglobal
  }

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Any actual rank-two chart emitted by the A19 strict-low frontier is already
a certified global successor of the honest reached source state. -/
noncomputable def actualRankTwoGlobalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress
      canonicalAdaptiveAlignedSmithRepairRanking T.terminal.blocker 0 :=
  AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress.ofGeometry
    canonicalAdaptiveAlignedSmithRepairRanking T.terminal.blocker 0
    T.terminal.repair_eq C

/-- Therefore an actual represented-state rank-two chart is impossible at a
genuine no-successor strict-low source. -/
theorem impossible_of_actualRankTwo_of_no_globalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented)
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state) :
    False := by
  let P := T.actualRankTwoGlobalProgress C
  exact hterminal P.target P.globalProgress

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
