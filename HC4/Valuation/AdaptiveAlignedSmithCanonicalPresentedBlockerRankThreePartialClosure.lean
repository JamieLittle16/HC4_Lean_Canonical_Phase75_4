import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerLosslessRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThree
import Mathlib.Tactic

/-!
# A18.4.87: consume the blocker Schur exits to rank three

A18.4.76 retains every geometry which historically licensed a blocker-side
rank-one to rank-two repair.  Several of those geometries are already much
stronger than that old interface:

* a preterminal adaptive rank-one Schur clock has the nondegenerate `-b^2`
  first-transverse block of A18.4.86;
* an exact zero-Schur chart, preterminal or closing, is completely exhausted
  to rank-three geometry by A18.4.83.

This file consumes exactly those cases.  It deliberately leaves three kinds
of geometry visible rather than pretending they are already rank three:

* saturated-kernel openings, whose old rank-two promotion still needs the
  all-minors/projective rigidity refinement;
* the planar and `w^2` packet escalations, whose nondegenerate quadratic block
  is the event licensing `1 -> 2` and cannot be reused as the later `2 -> 3`
  event; and
* the five residual A17 geometries, which will be consumed losslessly in the
  next finite pass.

Thus the exported frontier is an exact mathematical to-do list, not a repair
bookkeeping shortcut.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Blocker-side geometry which is already genuinely rank three. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1)
  | schurPreterminal
      (P : AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
        RR D complexity)
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (hpre : chart.clock.firstOrder < D.blocker.aligned.endpoint.defect)
      (geometry : Nonempty
        (AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThreeExit
          chart.clock hpre complexity))
  | zeroSchur
      (P : AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
        RR D complexity)
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        chart.zeroData complexity)
  | stationaryZeroSchur
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (P : AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
        RR D S complexity)
      (G : AdaptiveAlignedSmithCanonicalPresentedZeroSchurRankTwoGeometry D)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        G.chart.zeroData complexity)

/-- The genuinely unresolved packet geometry after the Schur exits have been
consumed. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerPacketRankTwoRemainder
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1)
  | planar
      (P : AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
        RR D complexity)
      (packet : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) D.blocker)
      (escalation : HasRankTwoPacketEscalation
        (0 : Fin 4) 1 2 packet.degree packet.packet)
  | wSquare
      (P : AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
        RR D complexity)
      (packet : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) D.blocker)
      (escalation : HasRankTwoPacketEscalation
        (0 : Fin 4) 3 2 packet.degree packet.packet)

/-- Exact blocker frontier after all immediately-consumable Schur geometry has
been sent to rank three. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerRankThreePartialOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | completeKernel
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
          RR source complexity))
  | rankThree
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerRankThreeGeometry
          RR D complexity))
  | packetRankTwo
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerPacketRankTwoRemainder
          RR D complexity))
  | stationaryResidual
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (P : AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
        RR D S complexity)
      (G : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
        (K := K) S complexity)

/-- **A18.4.87 blocker Schur/rank-three partial closure.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.rankThreePartialClosure
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerRankThreePartialOutcome
      RR D complexity := by
  cases D.losslessRankTwoClosure RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero

  | completeKernel P =>
      exact .completeKernel P

  | blocker hP =>
      rcases hP with ⟨P⟩
      cases P.geometry with
      | schurPreterminal chart hpre =>
          exact .rankThree ⟨.schurPreterminal P chart hpre
            (chart.clock.exists_preterminalRankThreeExit hpre complexity)⟩

      | zeroSchurPreterminal chart residual residual_pos residual_clock hpre =>
          exact .rankThree ⟨.zeroSchur P chart
            (exactSourceZeroSchur_completeRankThreeGeometry
              chart.zeroData complexity)⟩

      | planarPacket packet escalation =>
          exact .packetRankTwo ⟨.planar P packet escalation⟩

      | wSquarePacket packet escalation =>
          exact .packetRankTwo ⟨.wSquare P packet escalation⟩

  | stationary S hP =>
      rcases hP with ⟨P⟩
      cases P.geometry.witness with
      | inl G =>
          exact .stationaryResidual S P G
      | inr G =>
          exact .rankThree ⟨.stationaryZeroSchur S P G
            (exactSourceZeroSchur_completeRankThreeGeometry
              G.chart.zeroData complexity)⟩

end

end HC4.Valuation
