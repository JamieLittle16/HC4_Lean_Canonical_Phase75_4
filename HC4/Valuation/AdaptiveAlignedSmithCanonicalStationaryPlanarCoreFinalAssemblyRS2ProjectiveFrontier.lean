import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyTerminalLocalProblem
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurRS2ProjectiveWitnessReduction
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurProjectiveWedgeConstancy
import Mathlib.Tactic

/-!
# Final assembly A12: exact projective frontier of the RS2-ready branch

A11 packages every remaining stationary source problem behind one common
terminal source packet.  The early-Schur constructor is already much sharper:
it carries a literal constant raw binary Schur line together with the exact
B30 provenance packet and an `x₀^e L^m` RS2-ready first key.

This file consumes the last *purely projective* ambiguity of that packet.
For the full Stage-3 four-component polynomial kernel attached to the same
constant raw line, exactly one of the following occurs:

* every denominator-free projective wedge vanishes.  Stage 4B27 then gives an
  honest nonzero constant source-kernel direction;
* some full projective wedge is nonzero.  We retain explicit indices and the
  B29 active source point at which the wedge, `x₀`, and `L` are all nonzero.

Thus the moving RS2 branch no longer carries an abstract nonconstancy
statement.  The remaining corrected-RS2 theorem only has to manufacture the
Euler/correction motion scalars from this exact active projective wedge.

No progress is asserted in the moving case and no new geometric hypothesis is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Exact nonconstant-projective residue of one RS2-ready preassembly packet.
The active point is produced by the already-green B29 generic-point theorem,
so it simultaneously avoids the two divisors occurring in the sharp RS2
normal form. -/
structure ConstantSpecialSchurKernelLineRS2ActiveProjectiveData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData) where
  i : Fin 4
  j : Fin 4
  k : Fin 4
  wedge_ne_zero :
    (R.line.toDenominatorClearedSpecialSchurKernelData.projectiveWedge i j k) ≠ 0
  active :
    (R.line.toDenominatorClearedSpecialSchurKernelData.ActiveProjectiveWedgePointData
      R.rs2Ready i j k)

/-- Projective dichotomy for an RS2-ready constant raw Schur line.

If the complete Stage-3 polynomial kernel is projectively constant, B27 and
Stage 4A immediately give an honest constant source-kernel direction.  If it
is not, choose an actual nonzero projective wedge and promote it to the active
B29 point required by the corrected-RS2 calculation. -/
theorem ConstantSpecialSchurKernelLineRS2PreassemblyData.constantSourceKernel_or_activeProjective
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData) :
    Nonempty (ConstantSpecialSourceKernelData C) ∨
      Nonempty (C.ConstantSpecialSchurKernelLineRS2ActiveProjectiveData R) := by
  classical
  let E : C.DenominatorClearedSpecialSchurKernelData :=
    R.line.toDenominatorClearedSpecialSchurKernelData
  by_cases hvanish : E.HasVanishingProjectiveWedges
  · left
    exact E.constantSpecialSourceKernel_of_vanishingProjectiveWedges hvanish
  · right
    have hnonvanish :
        ∃ i j k : Fin 4,
          E.fullVector i * MvPolynomial.pderiv k (E.fullVector j) ≠
            E.fullVector j * MvPolynomial.pderiv k (E.fullVector i) := by
      simpa [DenominatorClearedSpecialSchurKernelData.HasVanishingProjectiveWedges] using hvanish
    rcases hnonvanish with ⟨i, j, k, hneq⟩
    have hwedge : E.projectiveWedge i j k ≠ 0 := by
      intro hzero
      exact hneq ((E.projectiveWedge_eq_zero_iff i j k).mp hzero)
    rcases E.exists_activeProjectiveWedgePointData
        R.rs2Ready i j k hwedge with ⟨A⟩
    exact ⟨{
      i := i
      j := j
      k := k
      wedge_ne_zero := by simpa [E] using hwedge
      active := by simpa [E] using A
    }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- A12 terminal geometry.  Only the RS2 constructor changes relative to A11:
it is split into a constant honest source-kernel endpoint or one exact active
full-projective-wedge packet. -/
inductive AdaptiveAlignedSmithCanonicalRS2ProjectiveTerminalGeometry
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

  | rs2ActiveProjective
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)
      (moving :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.ConstantSpecialSchurKernelLineRS2ActiveProjectiveData R)

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

/-- One A12 local problem: the common A11 source packet is unchanged, while
the RS2 geometry has been sharpened to its exact full-projective frontier. -/
structure AdaptiveAlignedSmithCanonicalRS2ProjectiveTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalRS2ProjectiveTerminalGeometry stationary

/-- A12 global frontier.  All nonlocal progress constructors are preserved;
the local constructor now carries the exact full-projective RS2 split. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreRS2ProjectiveOutcome
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
      (P : AdaptiveAlignedSmithCanonicalRS2ProjectiveTerminalLocalProblem s)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A12 RS2 projective reduction.**

Every A11 local problem is preserved verbatim except the RS2-ready case.  That
case is consumed by the exact Stage-3 projective dichotomy above, leaving
only an honest constant source-kernel direction or one concrete active
nonzero full projective wedge. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreRS2ProjectiveFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreRS2ProjectiveOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreTerminalLocalFrontier
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
      | earlySchurRS2Ready C hlt htangential R =>
          rcases R.constantSourceKernel_or_activeProjective with hkernel | hmoving
          · rcases hkernel with ⟨kernel⟩
            exact .local {
              stationary := P.stationary
              clock_eq := P.clock_eq
              clock_pos := P.clock_pos
              source := P.source
              geometry := .rs2ConstantSourceKernel C hlt htangential R kernel
            }
          · rcases hmoving with ⟨moving⟩
            exact .local {
              stationary := P.stationary
              clock_eq := P.clock_eq
              clock_pos := P.clock_pos
              source := P.source
              geometry := .rs2ActiveProjective C hlt htangential R moving
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
