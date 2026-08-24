import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyLosslessAxis
import Mathlib.Tactic

/-!
# Final assembly A16: coherent zero-jet axis provenance

A15 restores the exact low-dimensional zero-order source face alongside the
axis-normal terminal core.  For the final staircase adapter we need one more
piece of *typed coherence*: the axis normal form must be known to arise from
the exact `m = 0` zero-jet stationary core produced by that same source face.

This file retains that intermediate zero-jet core explicitly.  Thus the
canonical residual now carries, in one packet,

* the honest low-dimensional initial-form source face,
* the exact zero-jet `m = 0` stationary core obtained from it, and
* the final A4/A6 axis normal form obtained from that zero-jet core.

No geometry is added.  The construction simply re-runs already-green maps and
records their outputs without erasing the intermediate object.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Fully coherent canonical source packet for the final staircase adapter.
The `zeroJet` field is the exact `m = 0` stationary core obtained from
`lowDimensional`, and `axis` is reconstructed from that same `zeroJet` core. -/
structure DirectClosingCanonicalSquareCoherentZeroJetAxisTerminalCoreData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop where
  lowDimensional : DirectClosingCanonicalSquareLowDimensionalWallFaceData C heq
  zeroJet : DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData C heq
  axis : DirectClosingCanonicalSquareAxisTerminalCoreData C heq

/-- Re-run the already-green deterministic chain while retaining the exact
zero-jet stationary core.  In particular this removes the only provenance
looseness in the A15 pair `lowDimensional + axis`. -/
theorem DirectClosingCanonicalSquareLowDimensionalWallFaceData.toCoherentZeroJetAxisTerminalCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareLowDimensionalWallFaceData C heq) :
    Nonempty (DirectClosingCanonicalSquareCoherentZeroJetAxisTerminalCoreData C heq) := by
  let gradient := L.toGradientData
  let planar := gradient.toPlanarAffineData
  let stationary := planar.toStationaryPlanarCore
  let zeroJet := stationary.toZeroJetPlanarCore
  rcases zeroJet.toCurvedEliminatedCore with ⟨curved⟩
  exact ⟨{
    lowDimensional := L
    zeroJet := zeroJet
    axis := curved.toAxisTerminalCore
  }⟩

/-- A15's lossless packet canonically refines to the coherent packet by
recomputing both downstream objects from its retained source face.  We do not
trust the separately stored A15 `axis` field for this refinement. -/
theorem DirectClosingCanonicalSquareLosslessAxisTerminalCoreData.toCoherentZeroJetAxisTerminalCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareLosslessAxisTerminalCoreData C heq) :
    Nonempty (DirectClosingCanonicalSquareCoherentZeroJetAxisTerminalCoreData C heq) := by
  exact L.lowDimensional.toCoherentZeroJetAxisTerminalCore

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Global coherent A16 frontier -/

/-- The final local geometry after replacing A15's merely paired canonical
packet by a coherent source -> zero-jet -> axis packet. -/
inductive AdaptiveAlignedSmithCanonicalCoherentZeroJetAxisTerminalGeometry
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

  | canonicalCoherentZeroJetAxis
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareCoherentZeroJetAxisTerminalCoreData
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

structure AdaptiveAlignedSmithCanonicalCoherentZeroJetAxisTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalCoherentZeroJetAxisTerminalGeometry stationary

inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCoherentZeroJetAxisOutcome
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
      (P : AdaptiveAlignedSmithCanonicalCoherentZeroJetAxisTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A16 coherent zero-jet refinement.**

Every A15 branch is preserved verbatim except the canonical lossless-axis
residual.  There we discard the untyped pairing and deterministically rebuild
the zero-jet core and axis normal form from the retained exact source face.
The resulting local problem is the lossless input required by the final
staircase/profile theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreCoherentZeroJetAxisFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCoherentZeroJetAxisOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreLosslessAxisFrontier
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
      | canonicalLosslessAxis C heq data =>
          rcases data.toCoherentZeroJetAxisTerminalCore with ⟨coherent⟩
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .canonicalCoherentZeroJetAxis C heq coherent
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
