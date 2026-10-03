import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowActualRankTwoProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalActualRankTwoGlobalProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesGlobalDescent
import Mathlib.Tactic

/-!
# Geometry-backed actual rank-two to rank-three assembly for the strict-low endgame

Late A19 strict-low branches increasingly finish by producing an
`AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart` on the literal
represented blocker state.

Two sound global bridges already exist:

* `AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress`
  attaches the canonical rank-one to rank-two promotion only after retaining
  that actual represented-state Hessian chart; and
* `AdaptiveAlignedSmithCanonicalGlobalActualRankThreeProgress` transports
  the chart to the rank-two target, proves complete A18.4.84 rank-three
  geometry there, and only then attaches the rank-two to rank-three promotion.

This file composes those two packets.  The result is a single source-facing
strict global edge to the canonical rank-three repair state, retaining both
geometry-bearing stages.  No repair-only transition is exposed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Complete two-stage geometric promotion from a represented actual rank-two
chart to canonical rank three.

The intermediate rank-two target and its transported chart are retained
explicitly, so the final rank-three target cannot be confused with a naked
`withRepairOnly` relabelling. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankThreeProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1) where
  rankTwoProgress :
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress
      RR D complexity
  rankTwoTargetChart :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      rankTwoProgress.target
  rankThreeProgress :
    AdaptiveAlignedSmithCanonicalGlobalActualRankThreeProgress
      RR rankTwoTargetChart complexity
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      rankThreeProgress.target source

/-- Compose the geometry-backed represented-state `1 -> 2` promotion with
the geometry-backed `2 -> 3` promotion.

Strictness from the final rank-three target back to the honest source is just
transitivity of the already well-founded global macro relation. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankThreeProgress.ofGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart D.presented) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankThreeProgress
      RR D complexity := by
  let P12 :=
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankTwoProgress.ofGeometry
      RR D complexity hsrepair C

  let C2 :
      AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart P12.target := by
    rw [P12.target_eq]
    exact C.transportRepair (rankTwoRepairState complexity)

  have hrepair2 :
      P12.target.repair = rankTwoRepairState complexity := by
    rw [P12.target_eq]
    rfl

  let P23 :=
    C2.toGlobalRankThreeProgress RR complexity hrepair2

  exact {
    rankTwoProgress := P12
    rankTwoTargetChart := C2
    rankThreeProgress := P23
    globalProgress :=
      adaptiveAlignedSmithCanonicalGlobalMacroProgress_trans
        P23.globalProgress P12.globalProgress
  }

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Any actual rank-two chart produced by the strict-low frontier therefore
gives a geometry-backed rank-three successor of the honest reached source,
not merely a rank-two repair target. -/
noncomputable def actualRankThreeGlobalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankThreeProgress
      canonicalAdaptiveAlignedSmithRepairRanking T.terminal.blocker 0 :=
  AdaptiveAlignedSmithCanonicalGlobalPresentedActualRankThreeProgress.ofGeometry
    canonicalAdaptiveAlignedSmithRepairRanking T.terminal.blocker 0
    T.terminal.repair_eq C

/-- Existential-facing form for the final global dispatcher. -/
theorem exists_globalRankThreeProgress_of_actualRankTwo
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state := by
  let P := T.actualRankThreeGlobalProgress C
  exact ⟨P.rankThreeProgress.target, P.globalProgress⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
