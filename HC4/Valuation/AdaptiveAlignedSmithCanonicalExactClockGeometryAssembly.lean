import HC4.Valuation.AdaptiveAlignedSmithCanonicalEarlySchurRankTwoGeometry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockAssemblyFrontier
import Mathlib.Tactic

/-!
# A18.4.23: exact-clock assembly with no legacy rank-two constructor

A18.4.21 retains every stationary rank-two witness before the historical
repair-only wrapper.  A18.4.22 does the same for the later B38 early-Schur
rank-two exits.

There are only two places in the exact-clock assembly where those wrappers
were introduced:

1. `AdaptiveAlignedSmithCanonicalExactClockFinalLocalCore`, when the stationary
   blocker first enters its Schur/packet endgame;
2. B38, when an early-Schur closing carrier exposes moving raw-Schur or
   first-key transverse rank-two geometry.

This file reruns precisely those two already-green finite reductions with the
new geometry-carrying outputs.  Every other local constructor and every
residual object is reused unchanged.

The resulting exact-clock assembly has no `rankTwoMacro` constructor.  A
rank-two outcome is necessarily one of the two data-bearing global progress
objects whose family geometry justifies its repair promotion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Geometry-preserving final local frontier -/

/-- Final local frontier with the stationary repair-only constructor replaced
by A18.4.21's geometry-carrying progress object. -/
inductive AdaptiveAlignedSmithCanonicalExactClockGeometryFinalLocalOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | stationaryRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress
          RR s complexity))

  | localProblem
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

/-- Re-run the old final-local proof, changing only its stationary rank-two
branch.  The rank-one closing reduction is literally the already-green
`firstActualLayer_strict_or_eq_and_provenancedEarlierWall` split. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockGeometryFinalLocalFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockGeometryFinalLocalOutcome
      RR s complexity := by
  rcases s.alignedSmithCanonicalExactClockDispatcher with
    hzero | ⟨target, hspend⟩ | ⟨S, hclock, hpos⟩ |
    ⟨W, hclock⟩ | ⟨B⟩

  · exact .zeroDefect hzero

  · exact .ramifiedSpend target hspend

  · cases S.geometricExactClockEndgame hclock hpos with
    | rankTwoGeometry S hclock hG =>
        rcases hG with ⟨G⟩
        exact .stationaryRankTwoProgress
          ⟨AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress.ofGeometry
            RR S complexity hsrepair hclock G⟩

    | schurClosing S hclockS hposS C =>
        rcases C.firstActualLayer_strict_or_eq_and_provenancedEarlierWall with
          hlt | ⟨heq, hwall⟩
        · exact .localProblem {
            stationary := S
            clock_eq := hclockS
            clock_pos := hposS
            geometry := .earlySchurTangential C hlt
              (C.firstActualLayer_schurTangential_of_lt_defect hlt)
          }
        · exact .localProblem {
            stationary := S
            clock_eq := hclockS
            clock_pos := hposS
            geometry := .canonicalEarlierWall C heq (hwall.toNormalForm heq)
          }

    | zeroSchurClosing S hclockS hposS C =>
        exact .localProblem {
          stationary := S
          clock_eq := hclockS
          clock_pos := hposS
          geometry := .zeroSchur C
        }

    | planarRigidPacket S hclockS hposS hall P hrigid =>
        exact .localProblem {
          stationary := S
          clock_eq := hclockS
          clock_pos := hposS
          geometry := .planarRigid hall P hrigid
        }

    | wSquareRigidPacket S hclockS hposS hall P hrigid =>
        exact .localProblem {
          stationary := S
          clock_eq := hclockS
          clock_pos := hposS
          geometry := .wSquareRigid hall P hrigid
        }

  · exact .survivingExactClock W hclock
  · exact .sectionBoundaryInternal B

/-! ## Exact-clock assembly with both geometry-carrying rank-two exits -/

/-- The exact residual type from B38 remains completely unchanged.  Only the
rank-two constructors of the outer assembly are strengthened. -/
inductive AdaptiveAlignedSmithCanonicalExactClockGeometryAssemblyOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | stationaryRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress
          RR s complexity))

  | earlySchurRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress
          RR s complexity))

  | residual
      (R : AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual s)

/-- **Geometry-preserving exact-clock assembly.**

Every rank-two event which was previously exported through the historical
`rankTwoMacro` interface is consumed before that interface is formed.
Consequently the output has only honest ramified defect spends,
geometry-carrying rank-two progress, or the same explicitly enumerated local
residual geometry as the already-green assembly theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockGeometryAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockGeometryAssemblyOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalExactClockGeometryFinalLocalFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero

  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend

  | stationaryRankTwoProgress D =>
      exact .stationaryRankTwoProgress D

  | survivingExactClock W hclock =>
      exact .residual (.survivingExactClock W hclock)

  | sectionBoundaryInternal B =>
      exact .residual (.sectionBoundaryInternal B)

  | localProblem P =>
      cases P.geometry with
      | earlySchurTangential C hlt htangential =>
          rcases C.earlySchur_rankTwoGeometry_or_constantLineRS2Preassembly
              P complexity hlt with hG | hR
          · rcases hG with ⟨G⟩
            exact .earlySchurRankTwoProgress
              ⟨AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress.ofGeometry
                RR P complexity hsrepair C hlt G⟩
          · exact .residual
              (.earlySchurConstantRS2
                P.stationary P.clock_eq P.clock_pos
                C hlt htangential hR)

      | canonicalEarlierWall C heq wall =>
          exact .residual
            (.canonicalEarlierWall
              P.stationary P.clock_eq P.clock_pos C heq wall)

      | zeroSchur C =>
          exact .residual
            (.zeroSchur P.stationary P.clock_eq P.clock_pos C)

      | planarRigid hall Q hrigid =>
          exact .residual
            (.planarRigid
              P.stationary P.clock_eq P.clock_pos hall Q hrigid)

      | wSquareRigid hall Q hrigid =>
          exact .residual
            (.wSquareRigid
              P.stationary P.clock_eq P.clock_pos hall Q hrigid)

end

end HC4.Valuation