import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedKernelRankThreeClosure
import Mathlib.Tactic

/-!
# A18.4.100: every stationary residual already retains an exact rank-two chart

The five A17 residual geometries looked like separate rank-two re-entry cases,
but each constructor still carries the same closing source carrier `C`.
That carrier contains `C.chartData.chart`, an honest right-recentered Hessian
four-block with

* exact determinant `X^Delta`; and
* nonzero constant active `2 x 2` minor.

Consequently the later derivative/wall-face packet is not needed to discover
the next rank.  The retained exact chart itself is exhausted by the same
Schur argument used in A18.4.84:

* a nonzero constant cleared Schur numerator is an actual `3 x 3` minor; or
* all three constants vanish and the exact block is zero-Schur, so A18.4.83
  supplies complete source rank-three geometry.

This closes all five stationary residual constructors simultaneously and uses
no repair-only promotion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Constant `3 x 3` minor geometry on an honest right-recentered chart. -/
inductive AdaptiveAlignedSmithCanonicalRightRecenteredThreeByThreeMinorGeometry
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedRightRecenteredExactHessianChart B) : Prop
  | first (hne : C.block.schurA.coeff 0 ≠ 0)
  | mixed (hne : C.block.schurB.coeff 0 ≠ 0)
  | second (hne : C.block.schurC.coeff 0 ≠ 0)

/-- Complete rank-three geometry on the retained exact right-recentered chart. -/
inductive AdaptiveAlignedSmithCanonicalRightRecenteredChartRankThreeGeometry
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedRightRecenteredExactHessianChart B)
    (complexity : ℕ) : Type (u + 1)
  | constantMinor
      (geometry : AdaptiveAlignedSmithCanonicalRightRecenteredThreeByThreeMinorGeometry C)
  | zeroSchur
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (block_eq : Z.block = C.block)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        Z complexity)

/-- **Any honest exact active right-recentered chart is already completely
rank three.** -/
noncomputable def AdaptiveAlignedRightRecenteredExactHessianChart.rankThreeGeometry
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedRightRecenteredExactHessianChart B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalRightRecenteredChartRankThreeGeometry
      C complexity := by
  refine Classical.choice ?_
  by_cases hzero :
      C.block.schurA.coeff 0 = 0 ∧
        C.block.schurB.coeff 0 = 0 ∧
        C.block.schurC.coeff 0 = 0
  · let Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K) := {
      block := C.block
      defect := B.aligned.endpoint.defect
      fullDet := C.determinantCore
      activeDet_coeff_zero_ne_zero := C.block_activeDet_coeff_zero_ne_zero
      schurA_coeff_zero := hzero.1
      schurB_coeff_zero := hzero.2.1
      schurC_coeff_zero := hzero.2.2
    }
    exact ⟨.zeroSchur Z rfl
      (exactSourceZeroSchur_completeRankThreeGeometry Z complexity)⟩
  · have hsome :
        C.block.schurA.coeff 0 ≠ 0 ∨
          C.block.schurB.coeff 0 ≠ 0 ∨
          C.block.schurC.coeff 0 ≠ 0 := by
      tauto
    rcases hsome with hA | hB | hC
    · exact ⟨.constantMinor (.first hA)⟩
    · exact ⟨.constantMinor (.mixed hB)⟩
    · exact ⟨.constantMinor (.second hC)⟩

/-- Recover the common exact closing chart from any of the five residual
rank-two geometry constructors. -/
noncomputable def AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry.exactChart
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
      (K := K) S complexity) :
    AdaptiveAlignedRightRecenteredExactHessianChart S.blocker := by
  cases G with
  | wallMixed C heq wall face U V repair => exact C.chartData.chart
  | wallBasePlane C heq wall face i j repair => exact C.chartData.chart
  | rawSchurDerivative C repair => exact C.chartData.chart
  | firstKeyTransverse C line assembly hEq repair => exact C.chartData.chart
  | clearedLiftDerivative C preassembly repair => exact C.chartData.chart

/-- Every residual geometry therefore carries complete rank-three geometry on
its original honest chart. -/
structure AdaptiveAlignedSmithCanonicalResidualRankThreeGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (complexity : ℕ) : Type (u + 1) where
  residual : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
    (K := K) S complexity
  chart : AdaptiveAlignedRightRecenteredExactHessianChart S.blocker
  chart_eq : chart = residual.exactChart
  geometry : AdaptiveAlignedSmithCanonicalRightRecenteredChartRankThreeGeometry
    chart complexity

/-- **A18.4.100 complete residual rank-three closure.** -/
noncomputable def AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry.toRankThree
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
      (K := K) S complexity) :
    AdaptiveAlignedSmithCanonicalResidualRankThreeGeometry S complexity := by
  let C := G.exactChart
  exact {
    residual := G
    chart := C
    chart_eq := rfl
    geometry := C.rankThreeGeometry complexity
  }

/-- Blocker frontier after both the saturated-kernel and stationary-residual
seams are closed.  Only the homogeneous packet-reentry branch remains. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerResidualClosedOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | rankThreeExisting
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerKernelClosedRankThreeGeometry
          RR D complexity))
  | rankThreeResidual
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (G : AdaptiveAlignedSmithCanonicalResidualRankThreeGeometry S complexity)
  | packetRankTwo
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerPacketRankTwoRemainder
          RR D complexity))

/-- **Kernel + residual closed blocker frontier.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.residualClosedOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerResidualClosedOutcome
      RR D complexity := by
  cases D.kernelClosedRankThreeOutcome RR complexity hsrepair with
  | zeroDefect hzero => exact .zeroDefect hzero
  | rankThree hG => exact .rankThreeExisting hG
  | packetRankTwo hG => exact .packetRankTwo hG
  | stationaryResidual S P G =>
      exact .rankThreeResidual S G.toRankThree

end

end HC4.Valuation