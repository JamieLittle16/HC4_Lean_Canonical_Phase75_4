import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroOrderWall
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssembly
import Mathlib.Tactic

/-!
# Final assembly A9: consume zero-order wall curvature

A8 left one canonical source-wall geometry: a parameter-order-zero family
wall whose selected special-fibre monomial has complementary degree at most
one.  The local wall-face stack already proves much more about such a wall.

This file runs that existing stack all the way through:

* expose the exact zero-order special-fibre face;
* consume every nonzero complementary mixed derivative as rank-two repair;
* consume every nonzero intrinsic base-plane Hessian determinant as rank-two
  repair;
* turn the remaining rank-at-most-one face into the literal planar-affine
  normal form;
* remove the affine tail by the retained zero jet;
* run the complete marked/binary Hesse analysis and curved elimination.

Consequently the A8 `canonicalZeroOrderFamily` constructor disappears.  Its
only outputs are an already-certified rank-two macro or a fully
curved-eliminated zero-order stationary core.  No new geometric hypothesis is
introduced here; this is wiring of green local theorems.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A9 frontier.  The zero-order family wall has been run through all proved
wall-face curvature and stationary planar-core reductions. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroOrderCurvatureOutcome
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

  | canonicalZeroOrderCurvedEliminated
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (core :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareCurvedEliminatedStationaryCoreData
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

/-- Consume one zero-order family wall.  Every surviving curvature source is
immediately turned into the already-green rank-two outer macro.  If no such
curvature survives, the face is pushed through the complete stationary
planar-core chain and ends at the curved-eliminated core. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreZeroOrderCurvatureFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroOrderCurvatureOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreZeroOrderWallFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R
  | canonicalZeroOrderFamily S clock_eq clock_pos C heq wall =>
      let F := wall.toWallFaceData
      rcases F.mixedRepair_or_affineSeparated complexity with hrepair | haffine
      · rcases hrepair with ⟨face, U, V, repair⟩
        rcases S.blocker.aligned.exists_outerRankTwoRepairMacro
            RR s complexity hsrepair clock_eq repair.progress with
          ⟨outer, target, hmove, hprogress⟩
        exact .rankTwoMacro outer target hmove hprogress
      · rcases haffine.basePlaneRepair_or_lowDimensional complexity with
          hrepair | hlow
        · rcases hrepair with ⟨face, i, j, repair⟩
          rcases S.blocker.aligned.exists_outerRankTwoRepairMacro
              RR s complexity hsrepair clock_eq repair.progress with
            ⟨outer, target, hmove, hprogress⟩
          exact .rankTwoMacro outer target hmove hprogress
        · let gradient := hlow.toGradientData
          let planar := gradient.toPlanarAffineData
          let stationary := planar.toStationaryPlanarCore
          let zeroJet := stationary.toZeroJetPlanarCore
          rcases zeroJet.toCurvedEliminatedCore with ⟨core⟩
          exact .canonicalZeroOrderCurvedEliminated
            S clock_eq clock_pos C heq core
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
