import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurPreassemblyClosure
import Mathlib.Tactic

/-!
# Exact-clock assembly frontier after the early-Schur preassembly closure

This file performs the honest assembly step available after B38.

The moving raw-Schur branch and the first-key rank-two branch are consumed by
`earlySchur_rankTwoMacro_or_constantLineRS2Preassembly`.  We then refine the
already-green exact-clock final-local frontier into only three kinds of output:

* literal zero defect;
* certified macro progress;
* one explicitly enumerated residual local geometry.

The residual type is intentionally lossless.  It is the machine-checkable
list of obligations that must be eliminated before an unconditional closed
exact-clock recursion theorem can be stated.  In particular this module does
not relabel an internal boundary move or a stationary local packet as strict
recursive progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The exact residual geometries left after consuming every branch already
known to produce zero defect, a ramified defect spend, or a rank-two macro.

For the early-Schur constructor, B38 has already removed both the moving raw
Schur line and the first-key rank-two alternative.  Thus only the literal
constant raw Schur line with exact B30 provenance and an RS2-ready first key is
retained. -/
inductive AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

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

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- Assembly result after all currently certified strict/macro exits have been
consumed.  The `rankTwoMacro` constructor deliberately stores the propositional
wrapper `HasCertifiedRamifiedEpisodeInternalMove`, because B38's macro theorem
returns exactly that source-honest interface. -/
inductive AdaptiveAlignedSmithCanonicalExactClockAssemblyOutcome
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

  | residual
      (R : AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual s)

/-- **Exact assembly frontier after B38.**

This theorem consumes every already-certified exact-clock exit and, in the
`earlySchurTangential` branch, immediately invokes B38.  Consequently a moving
raw Schur line and a constant-line first-key rank-two packet can no longer
appear among the residuals.

No geometry is discarded: the exact stationary clock and all branch-specific
source data are retained in the residual constructors. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockAssemblyOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalExactClockFinalLocalFrontier
      RR complexity hsrepair with
    hzero |
    ⟨target, hspend⟩ |
    ⟨outer, target, hmove, hprogress⟩ |
    ⟨P⟩ |
    ⟨W, hclock⟩ |
    ⟨Bboundary⟩

  · exact .zeroDefect hzero

  · exact .ramifiedSpend target hspend

  · exact .rankTwoMacro outer target ⟨hmove⟩ hprogress

  · rcases P with ⟨S, hclock, hpos, geometry⟩
    cases geometry with
    | earlySchurTangential C hlt htangential =>
        let P' : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s := {
          stationary := S
          clock_eq := hclock
          clock_pos := hpos
          geometry := .earlySchurTangential C hlt htangential
        }
        rcases P'.earlySchur_rankTwoMacro_or_constantLineRS2Preassembly
            RR complexity hsrepair C hlt with
          hmacro | hconstant
        · rcases hmacro with ⟨outer, target, hmove, hprogress⟩
          exact .rankTwoMacro outer target hmove hprogress
        · exact .residual
            (.earlySchurConstantRS2 S hclock hpos C hlt htangential hconstant)

    | canonicalEarlierWall C heq wall =>
        exact .residual (.canonicalEarlierWall S hclock hpos C heq wall)

    | zeroSchur C =>
        exact .residual (.zeroSchur S hclock hpos C)

    | planarRigid hall P hrigid =>
        exact .residual (.planarRigid S hclock hpos hall P hrigid)

    | wSquareRigid hall P hrigid =>
        exact .residual (.wSquareRigid S hclock hpos hall P hrigid)

  · exact .residual (.survivingExactClock W hclock)

  · exact .residual (.sectionBoundaryInternal Bboundary)

/-- The genuinely recursive/macro-closed exact-clock outcomes.  Keeping this
separate from `AssemblyOutcome` prevents an unresolved local packet from being
mistaken for progress. -/
inductive AdaptiveAlignedSmithCanonicalExactClockClosedOutcome
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

/-- Exact theorem interface still required to close the exact-clock assembly.
It says precisely that every constructor of the lossless residual frontier can
be converted to one of the three certified closed outcomes above. -/
def AdaptiveAlignedSmithCanonicalExactClockResidualElimination
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop :=
  ∀ R : AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual s,
    AdaptiveAlignedSmithCanonicalExactClockClosedOutcome RR s complexity

/-- Once the explicitly enumerated residual frontier is eliminated, the whole
exact-clock dispatcher is closed.  This is pure assembly; all geometry is
isolated in `AdaptiveAlignedSmithCanonicalExactClockResidualElimination`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockClosed_of_residualElimination
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (helim : AdaptiveAlignedSmithCanonicalExactClockResidualElimination
      RR s complexity) :
    AdaptiveAlignedSmithCanonicalExactClockClosedOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalExactClockAssemblyFrontier
      RR complexity hsrepair with
    hzero | ⟨target, hspend⟩ |
    ⟨outer, target, hmove, hprogress⟩ | ⟨R⟩
  · exact .zeroDefect hzero
  · exact .ramifiedSpend target hspend
  · exact .rankTwoMacro outer target hmove hprogress
  · exact helim R

end

end HC4.Valuation
