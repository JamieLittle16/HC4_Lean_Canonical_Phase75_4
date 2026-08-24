import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssembly
import Mathlib.Tactic

/-!
# Residual compression for the final stationary planar-core assembly

The first final-assembly layer routes every exact-clock stationary wall through
all currently-green planar-core geometry, but intentionally keeps continuation
bookkeeping and the common stationary packet lossless.

This file performs the next assembly-only compression.

* the generic stationary packet is exposed as its five literal residual
  geometries;
* an exact-clock surviving endpoint is recorded as the certified ramified
  zero-cost presentation already proved by the exact-clock dispatcher;
* a genuine section boundary is recorded through the same certified internal
  move interface.

No remaining local geometry is declared to be recursive progress.  In
particular constant-RS2, the canonical curved-eliminated wall, zero-Schur,
rigid packets, and positive section gauge remain explicit obligations.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Source-honest provenance for zero-cost presentations -/

/-- Finite provenance trace for every ramified zero-cost presentation that is
allowed to survive into the final global assembly.

The first two constructors are the two genuine presentation origins of the
A17 stationary-planar-core pipeline.  `legacyRankTwo` is added here so the
A18.4 quarantine can retain the exact old producer while discarding its
potentially bookkeeping-only target as a recursive successor.  `trans`
records composition of presentations without declaring the composite to be
progress.

This trace is deliberately data about *why* a presentation exists; it is not a
termination measure. -/
inductive AdaptiveAlignedSmithCanonicalPresentationTrace
    (RR : RepairRanking) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) →
      ScaleAwareAdaptiveGeometricRestartState (K := K) → Prop

  | survivingExactClock
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) source)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * source.rawDefect) :
      AdaptiveAlignedSmithCanonicalPresentationTrace RR source
        (W.original.aligned.toOuterScaleAwareState source)

  | sectionBoundary
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection) :
      AdaptiveAlignedSmithCanonicalPresentationTrace RR source
        (source.alignedBoundaryScaleAwareReentry B)

  | legacyRankTwo
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer source)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer) :
      AdaptiveAlignedSmithCanonicalPresentationTrace RR source outer

  | trans
      {source middle target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (first : AdaptiveAlignedSmithCanonicalPresentationTrace RR source middle)
      (second : AdaptiveAlignedSmithCanonicalPresentationTrace RR middle target) :
      AdaptiveAlignedSmithCanonicalPresentationTrace RR source target

/-- The exact residual list after the first final-assembly frontier has been
compressed to the bookkeeping interfaces that are already certified.

The first three constructors are genuine exits.  `internalPresentation` is
explicitly *not* a recursive exit: it is a zero-cost ramified re-presentation
which must later be composed with an honest spend/progress certificate. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCompressedAssemblyOutcome
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

  | earlySchurConstantRS2
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : Nonempty C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

  | canonicalWall
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (L : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareCurvedEliminatedStationaryCoreData
        C heq)

  | zeroSchur
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)

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

  | sectionGauge
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A2 residual compression.**

Refine the green stationary-planar-core final assembly without adding any new
mathematical assumption.  The two continuation constructors are converted to
the exact certified zero-cost ramified move interface, and the stationary
packet is exposed constructor-by-constructor for the subsequent closure
lemmas. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreCompressedAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCompressedAssemblyOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreFinalAssemblyFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | stationary P =>
      cases P with
      | earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R =>
          exact .earlySchurConstantRS2
            S clock_eq clock_pos C hlt htangential R
      | canonicalWall S clock_eq clock_pos C heq L =>
          exact .canonicalWall S clock_eq clock_pos C heq L
      | zeroSchur S clock_eq clock_pos C =>
          exact .zeroSchur S clock_eq clock_pos C
      | planarRigid S clock_eq clock_pos hall P hrigid =>
          exact .planarRigid S clock_eq clock_pos hall P hrigid
      | wSquareRigid S clock_eq clock_pos hall P hrigid =>
          exact .wSquareRigid S clock_eq clock_pos hall P hrigid
  | sectionGauge S clock_eq clock_pos C heq G =>
      exact .sectionGauge S clock_eq clock_pos C heq G
  | survivingExactClock W clock_eq =>
      let target := W.original.aligned.toOuterScaleAwareState s
      exact .internalPresentation target
        ⟨W.original.aligned.certifiedOuterInternal_of_defect_eq s clock_eq⟩
        (by
          dsimp [target]
          exact .survivingExactClock W clock_eq)
  | sectionBoundaryInternal B =>
      let target := s.alignedBoundaryScaleAwareReentry B
      exact .internalPresentation target
        ⟨s.alignedBoundaryCertifiedInternalMove B⟩
        (by
          dsimp [target]
          exact .sectionBoundary B)

end

end HC4.Valuation
