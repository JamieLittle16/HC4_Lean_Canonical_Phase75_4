import HC4.Valuation.AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# Geometry-backed actual rank-two to rank-three global progress

A18.4.84 proves that every actual rank-two Hessian chart carries explicit
rank-three geometry.  The final global recursion needs the corresponding
state-level successor, but must not turn the finite repair transition into a
bare bookkeeping edge.

This module supplies exactly that sound bridge.  The actual rank-two chart is
retained, A18.4.84 is run on that chart, and only then is the canonical
rank-two to rank-three repair transition attached.  The target is the same
polynomial family, collision, scale and determinant clock with the repair tag
advanced to rank three.

Thus downstream final assembly receives both:

* the genuine rank-three geometry licensing the finite promotion; and
* strict progress in the existing well-founded global macro relation.

No new algebra, clock, terminal notion or repair relation is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart

/-- An actual Hessian chart is unchanged by a repair-only relabelling of the
ambient scale-aware state.  This is a geometric transport, not a progress
claim. -/
noncomputable def transportRepair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s)
    (repair : RepairState) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      (s.withRepairOnly repair) where
  permutation := C.permutation
  activeDet_coeff_zero_ne_zero := by
    simpa [scaleAwareHessianFourBlock, scaleAwareHessianSeriesMatrix,
      ScaleAwareAdaptiveGeometricRestartState.withRepairOnly] using
      C.activeDet_coeff_zero_ne_zero

end AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart

/-- Sound global rank-two -> rank-three macro.

The finite rank promotion is retained beside the actual rank-three geometry
which licenses it.  In particular this packet cannot be manufactured from a
repair tag alone. -/
structure AdaptiveAlignedSmithCanonicalGlobalActualRankThreeProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart source)
    (complexity : ℕ) : Type (u + 1) where
  geometry :
    AdaptiveAlignedSmithCanonicalActualRankThreeGeometry C complexity
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = source.withRepairOnly (rankThreeRepairState complexity)
  targetChart :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart target
  sameScaleProgress :
    CertifiedSameScaleEpisodeProgress RR target source
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- **Geometry-backed rank-two to rank-three global successor.**

A canonical rank-two state carrying an actual rank-two Hessian chart admits a
strict global macro successor at rank three.  The chart and the complete
A18.4.84 rank-three geometry are retained in the returned packet. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart.toGlobalRankThreeProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankTwoRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalActualRankThreeProgress
      RR C complexity := by
  let target :=
    source.withRepairOnly (rankThreeRepairState complexity)
  have hrepair :
      RepairProgress source.repair (rankThreeRepairState complexity) := by
    simpa [hsrepair] using rankTwo_to_rankThree_repairProgress complexity
  have hsame :
      CertifiedSameScaleEpisodeProgress RR target source := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target,
        ScaleAwareAdaptiveGeometricRestartState.withRepairOnly] using hrepair
  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
    exact
      (certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_repairProgress
        (K := K) (t := target) (s := source) rfl
        (by
          simpa [target,
            ScaleAwareAdaptiveGeometricRestartState.withRepairOnly] using
            hrepair)).progress
  exact {
    geometry := C.rankThreeGeometry complexity
    target := target
    target_eq := rfl
    targetChart := C.transportRepair (rankThreeRepairState complexity)
    sameScaleProgress := hsame
    globalProgress := hglobal
  }

/-- Existential-facing form used by global dispatchers which do not need to
inspect the retained packet immediately. -/
theorem
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart.exists_globalRankThreeProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankTwoRepairState complexity) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
  let P := C.toGlobalRankThreeProgress RR complexity hsrepair
  exact ⟨P.target, P.globalProgress⟩

end

end HC4.Valuation
