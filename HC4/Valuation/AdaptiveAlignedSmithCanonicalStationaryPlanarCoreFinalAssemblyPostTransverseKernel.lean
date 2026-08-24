import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyTransverseKernelRestart

/-!
# Final assembly A17.1: remove the transverse constant-kernel RS2 residue

The previous A16 frontier had seven local constructors.  The only RS2
constructor now carries a literal constant source-kernel direction with a
nonzero transverse coordinate.  `FinalAssemblyTransverseKernelRestart` turns
that packet into an honest strict ramified raw-defect spend from the incoming
scale-aware state.

This file performs the corresponding frontier compression.  Its local
geometry has exactly the six non-RS2 constructors; in particular there is no
constant-kernel residue left to be handled by later A17 stages.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The post-RS2 A17 terminal geometry.  This is exactly the A16 local
geometry with `rs2TransverseConstantKernel` removed. -/
inductive AdaptiveAlignedSmithCanonicalPostTransverseKernelTerminalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop
  | canonicalLosslessAxis
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data : C.DirectClosingCanonicalSquareLosslessAxisTerminalCoreData heq)
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
  | sectionGaugeKilled
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : C.DirectClosingPositiveSectionGaugeStep)
      (hkilled : G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)
  | sectionGaugeOrderRaised
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : C.DirectClosingPositiveSectionGaugeStep)
      (hnew : G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index) hnew)

/-- Local A17 problem after the RS2 constant-kernel case has been discharged. -/
structure AdaptiveAlignedSmithCanonicalPostTransverseKernelTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalPostTransverseKernelTerminalGeometry stationary

/-- A17.1 outcome.  Compared with A16, the only change is that the local
frontier cannot contain an RS2 constant-kernel residue. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostTransverseKernelOutcome
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
  | local (P : AdaptiveAlignedSmithCanonicalPostTransverseKernelTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.1 RS2 frontier elimination.**

Every A16 branch is transported unchanged except the literal transverse
constant-kernel RS2 branch, which is immediately converted into a strict
ramified raw-defect spend. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCorePostTransverseKernelFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostTransverseKernelOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreConstantKernelTransverseFrontier
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
      | rs2TransverseConstantKernel D =>
          rcases D.exists_ramifiedSpend_absolute P.stationary P.clock_eq with
            ⟨target, hspend⟩
          exact .ramifiedSpend target hspend
      | canonicalLosslessAxis C heq data =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .canonicalLosslessAxis C heq data
          }
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
      | sectionGaugeKilled C heq G hkilled =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .sectionGaugeKilled C heq G hkilled
          }
      | sectionGaugeOrderRaised C heq G hnew hstrict =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .sectionGaugeOrderRaised C heq G hnew hstrict
          }

end

end HC4.Valuation
