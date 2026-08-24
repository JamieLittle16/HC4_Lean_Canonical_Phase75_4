import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostStaircaseReady
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyClosingCarrierExit

/-!
# Final assembly A17.2B: remove every honest closing-carrier residue

A17.2A made the surviving canonical wall provenance exact.  A17.1, together
with the completed first-key/projective-Schur/RS2 chain, now gives a stronger
conclusion: every honest rank-one closing source carrier at the common
stationary frontier exits by either a strict ramified raw-defect spend or the
already-certified rank-two repair macro.

Consequently the staircase-ready canonical constructor and both section-gauge
constructors are all consumed uniformly.  The post-A17.2B local geometry has
only the zero-Schur packet and the two rigid packets left.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A17.2B terminal geometry: every constructor carrying an honest rank-one
closing source carrier has been removed. -/
inductive AdaptiveAlignedSmithCanonicalPostClosingCarrierTerminalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop
  | zeroSchurSourceReady
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)
  | planarRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket (0 : Fin 4) 1 2 P.degree P.packet)
  | wSquareRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket (0 : Fin 4) 3 2 P.degree P.packet)

/-- Local stationary problem after the universal closing-carrier exit has been
consumed. -/
structure AdaptiveAlignedSmithCanonicalPostClosingCarrierTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalPostClosingCarrierTerminalGeometry stationary

/-- A17.2B outcome.  The only local constructors remaining are zero-Schur and
the two rigid packets. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostClosingCarrierOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : s.rawDefect = 0)
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend target s)
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | local (P : AdaptiveAlignedSmithCanonicalPostClosingCarrierTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

private theorem closingCarrierOutcome
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (RR : RepairRanking)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (P : AdaptiveAlignedSmithCanonicalPostStaircaseReadyTerminalLocalProblem s)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostClosingCarrierOutcome
      RR s complexity := by
  rcases P.source.closingCarrier_ramifiedSpend_or_rankTwoMacro
      RR P.clock_eq complexity hsrepair C with hspend | hrepair
  · rcases hspend with ⟨target, h⟩
    exact .ramifiedSpend target h
  · rcases hrepair with ⟨outer, target, hmove, hprogress⟩
    exact .rankTwoMacro outer target hmove hprogress

/-- **A17.2B universal closing-carrier compression.**

The exact staircase-ready canonical packet and both section-gauge packets all
carry an honest rank-one closing source carrier over the same common terminal
source packet.  Each therefore exits by
`closingCarrier_ramifiedSpend_or_rankTwoMacro`.  Only zero-Schur and the two
rigid source packets remain local. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCorePostClosingCarrierFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostClosingCarrierOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCorePostStaircaseReadyFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | «local» P =>
      cases P.geometry with
      | canonicalStaircaseReady C heq data =>
          exact closingCarrierOutcome RR complexity hsrepair P C
      | sectionGaugeKilled C heq G hkilled =>
          exact closingCarrierOutcome RR complexity hsrepair P C
      | sectionGaugeOrderRaised C heq G hnew hstrict =>
          exact closingCarrierOutcome RR complexity hsrepair P C
      | zeroSchurSourceReady C source =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .zeroSchurSourceReady C source
          }
      | planarRigid hall Q hrigid =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .planarRigid hall Q hrigid
          }
      | wSquareRigid hall Q hrigid =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .wSquareRigid hall Q hrigid
          }

end

end HC4.Valuation
