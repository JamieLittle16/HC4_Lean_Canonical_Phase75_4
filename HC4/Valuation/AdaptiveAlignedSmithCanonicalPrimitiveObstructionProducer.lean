import HC4.Valuation.AdaptiveAlignedSmithCanonicalPrimitiveRankThreeTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalObstructionProducer

/-!
# A18.5.91: primitive obstruction producer for the final terminal

A18.5.90 isolates the last semantic terminal obligation into two endpoint
families: presented blockers and presented surviving walls.  Each of those
families still hides several genuinely different retained geometries.

A18.5.3 already gives the lossless nine-way primitive split.  This file moves
the obstruction-producer interface to that exact level.  No new mathematical
claim is made: a producer for the nine concrete retained events is assembled
mechanically into the two-field A18.5.90 producer.

This lets the final proof close and CI-check the primitive cases independently;
no repair tag, presentation wrapper, or synthetic rank promotion is allowed to
hide a missing polynomial obstruction.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Polynomial-obstruction producers for the nine genuine primitive terminal
geometries retained by A18.5.3. -/
structure AdaptiveAlignedSmithCanonicalPrimitiveObstructionProducer
    (RR : RepairRanking) (complexity : ℕ) where
  blockerZeroDefect :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
        source complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  blockerKernel :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
        source complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  blockerSchurPreterminal :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (hpre : chart.clock.firstOrder < D.blocker.aligned.endpoint.defect)
      (geometry : AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThreeExit
        chart.clock hpre complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  blockerZeroSchur :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        chart.zeroData complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  blockerResidual :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker
        D.presented)
      (geometry : AdaptiveAlignedSmithCanonicalResidualRankThreeGeometry
        stationary complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  survivingZeroDefect :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
        source complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  survivingKernel :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
        source complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  survivingRigidExposure :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) D.presented W P)
      (hD : 3 ≤ P.degree)
      (Q : AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
        RR D.presented W P R hD complexity)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteScalarRankThreeGeometry
        Q.geometry.zeroSchur complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  survivingPacketFamily :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (hD : 3 ≤ P.degree)
      (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
        (K := K) D.presented W P complexity)
      (geometry : AdaptiveAlignedSmithCanonicalPacketRankThreeProgress
        D.presented W P complexity R2 hD),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

/-- Nine primitive obstruction producers assemble mechanically into the exact
A18.5.90 blocker/surviving producer. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalPrimitiveObstructionProducer.toTerminalProducer
    {RR : RepairRanking} {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalPrimitiveObstructionProducer
      (K := K) RR complexity) :
    AdaptiveAlignedSmithCanonicalTerminalObstructionProducer
      (K := K) RR complexity where
  blocker := by
    intro source D geometry
    cases geometry with
    | zero G =>
        exact P.blockerZeroDefect D G
    | positive G =>
        cases G with
        | kernel G =>
            exact P.blockerKernel D G
        | schurPreterminal chart hpre G =>
            exact P.blockerSchurPreterminal D chart hpre G
        | zeroSchur chart G =>
            exact P.blockerZeroSchur D chart G
        | residual S G =>
            exact P.blockerResidual D S G
  surviving := by
    intro source D geometry
    cases geometry with
    | zero G =>
        exact P.survivingZeroDefect D G
    | kernel G =>
        exact P.survivingKernel D G
    | existing G =>
        cases G with
        | rigidExposure W Ppacket R hD Q G =>
            exact P.survivingRigidExposure D W Ppacket R hD Q G
        | packetFamily W Ppacket hD R2 G =>
            exact P.survivingPacketFamily D W Ppacket hD R2 G

/-- Primitive-producer-facing terminal contradiction. -/
theorem AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.impossible_of_primitiveObstructionProducer
    [IsAlgClosed K]
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (P : AdaptiveAlignedSmithCanonicalPrimitiveObstructionProducer
      (K := K) RR complexity) : False :=
  T.impossible_of_obstructionProducer P.toTerminalProducer

end

end HC4.Valuation
