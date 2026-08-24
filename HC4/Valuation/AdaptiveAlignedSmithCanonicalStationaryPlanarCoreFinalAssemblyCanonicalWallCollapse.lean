import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyTerminalNormalForm
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingEarlierWallClock
import Mathlib.Tactic

/-!
# Final assembly A7: collapse every canonical equality wall to an earlier source clock

A6 sharpened the stationary binary face to degree zero or to an exact
one-variable nonlinear polynomial after source shear.  At the source level we
can now make a stronger simplification which had deliberately been kept
separate from that face analysis.

Every canonical-wall constructor still carries the literal equality

    firstActualLayerOrder = endpoint.defect.

The already-green direct-closing terminal theorem proves that equality can
never remain terminal: it produces a source-honest canonical *earlier* wall,
retaining whether the wall came from the original longitudinal source or the
marked-axis-preserving transverse source.  Its normal-form theorem then
reduces that wall to one of four exact source-clock alternatives.

Consequently the three A6 canonical constructors can be replaced by one
`canonicalEarlierWall` constructor.  The face-level A4/A6 information is not
needed to justify this replacement; it remains independently proved and can be
used later if desired.  No progress assertion or new hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A7 terminal frontier.  Relative to A6, all three equality-wall face
constructors are replaced by the source-honest strict-earlier-wall normal
form already proved by direct closing. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCanonicalWallCollapsedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | earlySchurRS2Ready
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

  | canonicalEarlierWall
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (wall :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWallNormalForm
          C heq)

  | zeroSchurSourceReady
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)

  | planarRigid
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigid
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | sectionGaugeKilled
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hkilled :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)

  | sectionGaugeOrderRaised
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hnew :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index)
            hnew)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- A7 assembly theorem: every equality-wall face produced by A6 is replaced
by the already-certified source-honest canonical earlier-wall normal form. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreCanonicalWallCollapsedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCanonicalWallCollapsedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreTerminalNormalFormFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R
  | canonicalWallLongitudinal S clock_eq clock_pos C heq _D _face _face_ne_zero
      _base_support _source_collision _face_linear_zero =>
      let P := C.directClosing_equality_forces_provenancedEarlierWall heq
      exact .canonicalEarlierWall S clock_eq clock_pos C heq (P.toNormalForm heq)
  | canonicalWallTransverseDegreeZero S clock_eq clock_pos C heq _data _H
      _H_eq _H_ne_zero _maximal =>
      let P := C.directClosing_equality_forces_provenancedEarlierWall heq
      exact .canonicalEarlierWall S clock_eq clock_pos C heq (P.toNormalForm heq)
  | canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq _data _straight =>
      let P := C.directClosing_equality_forces_provenancedEarlierWall heq
      exact .canonicalEarlierWall S clock_eq clock_pos C heq (P.toNormalForm heq)
  | zeroSchurSourceReady S clock_eq clock_pos C source =>
      exact .zeroSchurSourceReady S clock_eq clock_pos C source
  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .planarRigid S clock_eq clock_pos hall P hrigid
  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .wSquareRigid S clock_eq clock_pos hall P hrigid
  | sectionGaugeKilled S clock_eq clock_pos C heq G hkilled =>
      exact .sectionGaugeKilled S clock_eq clock_pos C heq G hkilled
  | sectionGaugeOrderRaised S clock_eq clock_pos C heq G hnew hstrict =>
      exact .sectionGaugeOrderRaised S clock_eq clock_pos C heq G hnew hstrict
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
