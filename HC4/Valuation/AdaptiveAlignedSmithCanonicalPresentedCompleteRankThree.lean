import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedKernelRankThreeClosure
import Mathlib.Tactic

/-!
# A18.4.105: both presented endpoint families are completely rank three

A18.4.103 leaves only the literal zero-clock exception on the blocker side.
A18.4.85 leaves zero clock and the explicit saturated-kernel opening on the
surviving side.  A18.4.104 consumes zero clock geometrically, while A18.4.99
already consumes every retained saturated opening.

Consequently both canonical presented endpoint types now have a single
nonempty output: complete rank-three geometry.  This is the lossless terminal
interface needed by the final boundary/aligned assembly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete rank-three geometry for a presented blocker, including the unit
clock case. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1)
  | zero
      (geometry : AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
        source complexity)
  | positive
      (geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerCompleteRankThreeGeometry
        RR D complexity)

/-- **Every presented blocker carries complete rank-three geometry.** -/
noncomputable def
    AdaptiveAlignedSmithCanonicalPresentedBlocker.allRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
      RR D complexity := by
  cases D.completeRankThreeOutcome RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zero (source.zeroDefect_completeRankThreeGeometry complexity hzero)
  | rankThree hG =>
      exact .positive (Classical.choice hG)

/-- Complete rank-three geometry for a presented surviving wall. -/
inductive AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ) : Type (u + 1)
  | zero
      (geometry : AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
        source complexity)
  | kernel
      (geometry : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
        source complexity)
  | existing
      (geometry : AdaptiveAlignedSmithCanonicalPresentedSurvivingRankThreeGeometry
        RR D complexity)

/-- **Every presented surviving endpoint carries complete rank-three
geometry.** -/
noncomputable def
    AdaptiveAlignedSmithCanonicalPresentedSurviving.allRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
      RR D complexity := by
  cases D.rankThreeClosure RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zero (source.zeroDefect_completeRankThreeGeometry complexity hzero)
  | completeKernel hP =>
      exact .kernel (Classical.choice hP).completeRankThreeGeometry
  | rankThree hG =>
      exact .existing (Classical.choice hG)

end

end HC4.Valuation
