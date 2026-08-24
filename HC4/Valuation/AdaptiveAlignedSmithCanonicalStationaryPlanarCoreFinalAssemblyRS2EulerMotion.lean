import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRS2ProjectiveFrontier
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurCorrectedRS2Fork
import Mathlib.Tactic

/-!
# Final assembly A13: active projective motion gives a forced nonzero RS2 source

A12 reduced the RS2-ready branch to either an honest constant source-kernel
line or one explicit nonzero full-projective wedge together with an active
source point away from `x₀ L = 0`.

At such an active point there is a canonical nontrivial Euler motion:

    rhoX = L(p),    rhoL = -x₀(p).

The Euler relation is then the tautology

    x₀(p) L(p) - L(p) x₀(p) = 0,

and the motion is nonzero because `L(p) != 0`.  The corrected-RS2 fork already
proves that every such nonzero Euler motion has nonzero denominator-cleared
second-order source.  Thus the moving projective branch is no longer merely a
nonzero wedge: it carries the exact scalar source that the final Schur
correction must cancel.

No correction is identified with repair in this file.  That is the remaining
source-to-Schur coefficient theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- A12's active projective residue, upgraded to an explicit nonzero Euler
motion for the same B30/RS2-ready kernel. -/
structure ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData) where
  moving : C.ConstantSpecialSchurKernelLineRS2ActiveProjectiveData R
  motion :
    R.line.toDenominatorClearedSpecialSchurKernelData.ActiveProjectiveEulerMotionWitness
      R.rs2Ready moving.i moving.j moving.k

/-- Canonical Euler motion at the A12 active point.

The choice `(rhoX,rhoL)=(L(p),-x₀(p))` is source-honest, nonzero, and satisfies
the degree-zero Euler relation identically. -/
noncomputable def ConstantSpecialSchurKernelLineRS2ActiveProjectiveData.toEulerMotionData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData}
    (M : C.ConstantSpecialSchurKernelLineRS2ActiveProjectiveData R) :
    C.ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData R := by
  let ell : K :=
    MvPolynomial.eval (fun r : Fin 3 => M.active.point r.succ)
      R.rs2Ready.normalForm.linearForm
  refine {
    moving := M
    motion := {
      activePoint := M.active
      rhoX := ell
      rhoL := -(M.active.point 0)
      motion_ne_zero := ?_
      euler := ?_
    }
  }
  · left
    simpa [ell] using M.active.linearForm_ne_zero
  · dsimp [ell]
    ring

/-- The active Euler packet carries a genuinely nonzero cleared RS2 source.
This is exactly B31's corrected-RS2 fork applied to the canonical motion above. -/
theorem ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData.clearedRS2Source_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData}
    (M : C.ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData R) :
    xeLmClearedRS2Source
        R.provenance.canonical.sourceExponent
        R.provenance.canonical.transverseDegree
        (M.motion.activePoint.point 0)
        (MvPolynomial.eval
          (fun r : Fin 3 => M.motion.activePoint.point r.succ)
          R.rs2Ready.normalForm.linearForm)
        M.motion.rhoX M.motion.rhoL ≠ 0 := by
  exact M.motion.clearedRS2Source_ne_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- A13 terminal geometry.  The only change from A12 is that a moving RS2
projective kernel now carries an explicit nonzero Euler/cleared-RS2 source. -/
inductive AdaptiveAlignedSmithCanonicalRS2EulerTerminalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop

  | rs2ConstantSourceKernel
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)
      (kernel :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.ConstantSpecialSourceKernelData C)

  | rs2ActiveEulerSource
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)
      (moving :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData R)

  | canonicalAxisCore
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (core :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareAxisTerminalCoreData
          C heq)

  | zeroSchurSourceReady
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)

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
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | sectionGaugeKilled
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hkilled :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)

  | sectionGaugeOrderRaised
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hnew : G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index)
            hnew)

/-- One A13 local problem. -/
structure AdaptiveAlignedSmithCanonicalRS2EulerTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalRS2EulerTerminalGeometry stationary

/-- A13 global frontier. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreRS2EulerOutcome
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

  | local
      (P : AdaptiveAlignedSmithCanonicalRS2EulerTerminalLocalProblem s)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A13 corrected-RS2 source extraction.**

A12's active-projective constructor is upgraded to the canonical active Euler
motion above.  Hence every moving RS2 branch now carries a cleared second-order
source which is already certified nonzero by B31. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreRS2EulerFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreRS2EulerOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreRS2ProjectiveFrontier
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
      | rs2ConstantSourceKernel C hlt htangential R kernel =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .rs2ConstantSourceKernel C hlt htangential R kernel
          }
      | rs2ActiveProjective C hlt htangential R moving =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .rs2ActiveEulerSource C hlt htangential R moving.toEulerMotionData
          }
      | canonicalAxisCore C heq core =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .canonicalAxisCore C heq core
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
