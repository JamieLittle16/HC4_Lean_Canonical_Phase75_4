import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRS2LiftRepair
import Mathlib.Tactic

/-!
# Final assembly A15: restore lossless zero-order wall provenance

A14 eliminates the moving RS2 lift by an honest derivative-Hessian rank-two
repair.  Its remaining canonical constructor, however, carries only the final
axis-normal stationary core.  During the A9 -> A11 compression the exact
zero-order wall face which produced that core was deliberately forgotten.

That erasure is harmless for the binary Hesse classification, but it is not
harmless for the final finite staircase: the staircase profile is an equation
on the exact initial face of the honest aligned-square source.  This file
therefore re-runs the already-green equality-wall reduction on the canonical
local branch and retains the last low-dimensional wall face together with the
axis terminal normal form obtained from it.

If the re-exposed wall has mixed or base-plane curvature it is again consumed
as the existing rank-two macro.  If it is a section wall it is folded back into
the existing killed/order-raised gauge pair.  The only surviving canonical
object is therefore a *lossless* low-dimensional source face plus its proved
axis terminal normal form.

No new geometric assumption is introduced and no residual is called progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Lossless canonical zero-order endpoint.  `lowDimensional` retains the
literal initial-form equation on the honest aligned-square family; `axis`
retains the complete A4/A6 binary terminal classification obtained from that
same low-dimensional packet. -/
structure DirectClosingCanonicalSquareLosslessAxisTerminalCoreData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop where
  lowDimensional : DirectClosingCanonicalSquareLowDimensionalWallFaceData C heq
  axis : DirectClosingCanonicalSquareAxisTerminalCoreData C heq

/-- Re-run the already-green low-dimensional -> planar-affine -> zero-jet ->
binary-Hesse chain without forgetting the input low-dimensional face. -/
theorem DirectClosingCanonicalSquareLowDimensionalWallFaceData.toLosslessAxisTerminalCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareLowDimensionalWallFaceData C heq) :
    Nonempty (DirectClosingCanonicalSquareLosslessAxisTerminalCoreData C heq) := by
  let gradient := L.toGradientData
  let planar := gradient.toPlanarAffineData
  let stationary := planar.toStationaryPlanarCore
  let zeroJet := stationary.toZeroJetPlanarCore
  rcases zeroJet.toCurvedEliminatedCore with ⟨curved⟩
  exact ⟨{
    lowDimensional := L
    axis := curved.toAxisTerminalCore
  }⟩

/-- Exact lossless outcome of one zero-order family wall.  Every actual
curvature source is retained until it is routed to rank-two repair; otherwise
we keep the low-dimensional initial face needed by the final staircase. -/
inductive DirectClosingCanonicalSquareZeroOrderLosslessOutcome
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (complexity : ℕ) : Prop
  | mixedRepair
      (face : MvPolynomial (Fin 4) K)
      (U V : Fin 4)
      (repair : DirectClosingWallFaceMixedRepairData complexity face U V)
  | basePlaneRepair
      (face : MvPolynomial (Fin 4) K)
      (i j : Fin 4)
      (repair : DirectClosingWallFaceBasePlaneRankTwoRepairData complexity face i j)
  | losslessAxis
      (data : DirectClosingCanonicalSquareLosslessAxisTerminalCoreData C heq)

/-- A zero-order family wall is either immediate honest rank-two curvature or
the lossless axis terminal packet above. -/
theorem DirectClosingCanonicalSquareZeroOrderFamilyWallShape.toLosslessOutcome
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (Z : DirectClosingCanonicalSquareZeroOrderFamilyWallShape C heq)
    (complexity : ℕ) :
    DirectClosingCanonicalSquareZeroOrderLosslessOutcome C heq complexity := by
  let F := Z.toWallFaceData
  rcases F.mixedRepair_or_affineSeparated complexity with hrepair | haffine
  · rcases hrepair with ⟨face, U, V, repair⟩
    exact .mixedRepair face U V repair
  · rcases haffine.basePlaneRepair_or_lowDimensional complexity with
      hrepair | hlow
    · rcases hrepair with ⟨face, i, j, repair⟩
      exact .basePlaneRepair face i j repair
    · rcases hlow.toLosslessAxisTerminalCore with ⟨data⟩
      exact .losslessAxis data

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Global A15 frontier -/

/-- A15 local geometry.  Relative to A14 the lossy `canonicalAxisCore`
constructor is replaced by `canonicalLosslessAxis`, whose low-dimensional
source face still carries its exact initial-form equation. -/
inductive AdaptiveAlignedSmithCanonicalLosslessAxisTerminalGeometry
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

  | canonicalLosslessAxis
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareLosslessAxisTerminalCoreData
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

structure AdaptiveAlignedSmithCanonicalLosslessAxisTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalLosslessAxisTerminalGeometry stationary

inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreLosslessAxisOutcome
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
      (P : AdaptiveAlignedSmithCanonicalLosslessAxisTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A15 lossless canonical-wall restoration.**

The A14 moving-RS2 repair remains consumed.  On the sole canonical branch we
re-run the deterministic earlier-wall classifier.  Section walls return to the
finite gauge pair; zero-order family walls either expose rank-two curvature or
retain the exact low-dimensional source face together with the final axis
normal form. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreLosslessAxisFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreLosslessAxisOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreRS2LiftRepairFrontier
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
      | canonicalAxisCore C heq _oldCore =>
          let earlier := C.directClosing_equality_forces_provenancedEarlierWall heq
          let normal := earlier.toNormalForm heq
          cases normal.toReducedFrontier with
          | sectionGauge G =>
              rcases G.killed_or_order_strict with hkilled | ⟨hnew, hstrict⟩
              · exact .local {
                  stationary := P.stationary
                  clock_eq := P.clock_eq
                  clock_pos := P.clock_pos
                  source := P.source
                  geometry := .sectionGaugeKilled C heq G hkilled
                }
              · exact .local {
                  stationary := P.stationary
                  clock_eq := P.clock_eq
                  clock_pos := P.clock_pos
                  source := P.source
                  geometry := .sectionGaugeOrderRaised C heq G hnew hstrict
                }
          | zeroOrderFamily Z =>
              cases Z.toLosslessOutcome complexity with
              | mixedRepair face U V repair =>
                  rcases P.stationary.blocker.aligned.exists_outerRankTwoRepairMacro
                      RR s complexity hsrepair P.clock_eq repair.progress with
                    ⟨outer, target, hmove, hprogress⟩
                  exact .rankTwoMacro outer target hmove hprogress
              | basePlaneRepair face i j repair =>
                  rcases P.stationary.blocker.aligned.exists_outerRankTwoRepairMacro
                      RR s complexity hsrepair P.clock_eq repair.progress with
                    ⟨outer, target, hmove, hprogress⟩
                  exact .rankTwoMacro outer target hmove hprogress
              | losslessAxis data =>
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
