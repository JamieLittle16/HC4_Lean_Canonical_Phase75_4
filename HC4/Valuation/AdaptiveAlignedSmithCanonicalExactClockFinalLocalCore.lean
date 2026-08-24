import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockStationaryEndgame
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingEarlierWallClock
import Mathlib.Tactic

/-!
# Exact-clock final local core

This file performs the last *proved* reduction before the genuinely open
stationary source-geometry adapter.

The scale-sound exact-clock dispatcher has already consumed:

* every loss below the literal outer `20 * Delta` clock as an absolute-scale
  ramified defect spend;
* every positive saturated rational transverse kernel slope;
* complete transverse freeness;
* every rank-one -> rank-two repair as a sound macro step.

The only blocker-side geometries still visible were rank-one Schur closing,
zero-Schur closing, and the two rigid persistent packets.  The rank-one Schur
closing has substantially more source information than that label suggests:
the JC2-free direct-closing analysis proves that its first actual source layer
is either strictly preclosing and Schur-tangential, or equality has already
been converted into a concrete canonical earlier coefficient/section wall.

We consume that theorem here, retaining the exact outer clock and stationary
source provenance.  Thus all genuinely unresolved blocker geometry is
packaged into one local problem type with five explicit source-facing tags:

* early Schur-tangential actual layer;
* canonical earlier square wall;
* stationary zero-Schur closing;
* stationary planar rigid packet;
* stationary `w^2` rigid packet.

No terminal extraction, arbitrary re-entry, JC2 hypothesis, or unproved
progress assertion is introduced.  In particular this module is intended as
the honest final local theorem boundary for the remaining HC4 argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The exact local geometry still needing a source-honest restart argument.

Every constructor is indexed by the same stationary blocker, so the exact
clock, mixedness, all-transverse rational-zero normal form, and first
longitudinal departure are shared rather than copied into five unrelated
dispatcher branches. -/
inductive AdaptiveAlignedSmithCanonicalExactClockFinalLocalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop

  | earlySchurTangential
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt :
        C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)

  | canonicalEarlierWall
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq :
        C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (wall :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWallNormalForm
          C heq)

  | zeroSchur
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)

  | planarRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- One final stationary local problem, retaining the literal outer clock.

The positivity field is kept explicitly because the zero-defect branch has
already been removed before this object is constructed. -/
structure AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  geometry :
    AdaptiveAlignedSmithCanonicalExactClockFinalLocalGeometry stationary

namespace AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

/-- The final local object retains the canonical first same-Smith-exponent
longitudinal departure on the honest recentered special fibre. -/
theorem firstLongitudinalDeparture
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber
        P.stationary.blocker.aligned.endpoint.rightRecenteredFamily)
      P.stationary.blocker.exponent :=
  P.stationary.firstLongitudinalDeparture

/-- Every final local object is already saturated-rational-zero in all three
transverse source coordinates. -/
theorem allTransverseZero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) :
    AdaptiveRecenteredAllTransverseZeroRationalSlope P.stationary.blocker :=
  P.stationary.allTransverseZero

/-- Hence each transverse coordinate genuinely occurs on the honest
recentered special fibre. -/
theorem specialFiber_witnesses
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) :
    (∃ d ∈
        (polynomialFamilySpecialFiber
          P.stationary.blocker.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (1 : Fin 4)) ∧
    (∃ d ∈
        (polynomialFamilySpecialFiber
          P.stationary.blocker.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (2 : Fin 4)) ∧
    (∃ d ∈
        (polynomialFamilySpecialFiber
          P.stationary.blocker.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (3 : Fin 4)) :=
  P.stationary.specialFiber_witnesses

end AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

/-- Global exact-clock outcome after consuming the *entire proved* rank-one
Schur direct-closing analysis.

The only new constructor is `local`, containing one exact stationary local
problem.  Surviving-wall and section-boundary objects remain outer macro
bookkeeping and are deliberately not declared recursive progress here. -/
inductive AdaptiveAlignedSmithCanonicalExactClockFinalLocalOutcome
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
      (hmove : CertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | local
      (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- **Final proved local reduction.**

At rank-one repair, every blocker-side outcome is now either sound macro
progress or one exact stationary local problem.  In particular the old
`schurClosing` constructor no longer survives: its determinant-closing
source has been reduced JC2-free to an early Schur-tangential layer or an
explicit canonical earlier wall.

This theorem makes no claim that either of those two source-wall objects, or
the stationary zero-Schur/rigid objects, are already recursive progress.
That conversion is exactly the remaining local geometric theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockFinalLocalFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockFinalLocalOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalExactClockDispatcher with
    hzero | ⟨target, hspend⟩ | ⟨S, hclock, hpos⟩ |
    ⟨W, hclock⟩ | ⟨B⟩

  · exact .zeroDefect hzero

  · exact .ramifiedSpend target hspend

  · rcases S.exactClockEndgame RR complexity hsrepair hclock hpos with
      ⟨outer, target, hmove, hprogress⟩ |
      ⟨S, hclockS, hposS, C⟩ | ⟨S, hclockS, hposS, C⟩ |
      ⟨S, hclockS, hposS, hall, P, hrigid⟩ |
      ⟨S, hclockS, hposS, hall, P, hrigid⟩
    · exact .rankTwoMacro outer target hmove hprogress
    · rcases C.firstActualLayer_strict_or_eq_and_provenancedEarlierWall with
        hlt | ⟨heq, hwall⟩
      · exact .local {
          stationary := S
          clock_eq := hclockS
          clock_pos := hposS
          geometry := .earlySchurTangential C hlt
            (C.firstActualLayer_schurTangential_of_lt_defect hlt)
        }
      · exact .local {
          stationary := S
          clock_eq := hclockS
          clock_pos := hposS
          geometry := .canonicalEarlierWall C heq (hwall.toNormalForm heq)
        }
    · exact .local {
        stationary := S
        clock_eq := hclockS
        clock_pos := hposS
        geometry := .zeroSchur C
      }
    · exact .local {
        stationary := S
        clock_eq := hclockS
        clock_pos := hposS
        geometry := .planarRigid hall P hrigid
      }
    · exact .local {
        stationary := S
        clock_eq := hclockS
        clock_pos := hposS
        geometry := .wSquareRigid hall P hrigid
      }

  · exact .survivingExactClock W hclock

  · exact .sectionBoundaryInternal B

end

end HC4.Valuation
