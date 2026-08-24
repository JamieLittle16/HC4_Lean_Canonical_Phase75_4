import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCurvedElimination
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockAssemblyFrontier
import Mathlib.Tactic

/-!
# Final scale-sound assembly frontier for the stationary planar core

This file is the first literal final-assembly layer for the unconditional HC4
programme.

The exact-clock assembly frontier already consumes every certified zero-defect,
ramified-spend and rank-two macro exit.  Its residual local geometry is then
run through the green low-dimensional chain

    stationary convergence
      -> planar-affine normal form
      -> genuine zero-jet stationary core.

For the canonical equality wall we continue through the newly completed
binary Hesse analysis:

    marked collision/zero jet
      -> binary planarisation
      -> maximal homogeneous layer
      -> curved-eliminated singular-Hessian frontier.

Thus this module performs only wiring.  It does not relabel any remaining
local geometry as recursive progress.  In particular the longitudinal wall,
the curved-free binary alternatives, the constant-RS2 packet, zero-Schur,
rigid packets, section gauge and continuation bookkeeping remain explicit.
This is intentional: the resulting frontier is the exact list which the final
closure theorem must consume.

`AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity`
is imported as a second independently-green terminal rigidity theorem.  It is
not silently substituted for the curved-elimination theorem; a future use of
that route must provide the honest binary-to-profile straightening adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Canonical equality-wall core after every currently proved binary Hesse
reduction has been assembled.

The longitudinal branch is retained losslessly.  The transverse branch now
carries the exact binary polynomial together with the curved-eliminated
frontier proved in `StationaryPlanarCoreCurvedElimination`. -/
inductive DirectClosingCanonicalSquareCurvedEliminatedStationaryCoreData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
      (face_ne_zero : face ≠ 0)
      (base_support : IsLongitudinalBaseSupport face)
      (source_collision :
        HasExactGradientCollision
          (polynomialFamilySpecialFiber D.family)
          (fun _ : Fin 4 => (0 : K))
          (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i))
      (face_linear_zero :
        ∀ i : Fin 4,
          MvPolynomial.coeff (Finsupp.single i 1) face = 0)

  | transverse
      (data : DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (frontier : BinarySingularHessianCurvedEliminatedFrontier data.binaryFace)

/-- Assemble the complete proved binary Hesse chain on a genuine zero-jet
canonical wall core. -/
theorem DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData.toCurvedEliminatedCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData C heq) :
    Nonempty (DirectClosingCanonicalSquareCurvedEliminatedStationaryCoreData C heq) := by
  have M := L.toMarkedCore
  cases M.toBinaryStationaryCoreFrontier with
  | longitudinal D face face_ne_zero base_support source_collision face_linear_zero =>
      exact ⟨.longitudinal D face face_ne_zero base_support
        source_collision face_linear_zero⟩
  | transverse data =>
      rcases binarySingularHessian_curvedEliminatedFrontier
          data.binaryFace data.binaryFace_ne_zero data.binary_det_zero
          data.binaryFace_linear_zero with ⟨frontier⟩
      exact ⟨.transverse data frontier⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Stationary packet with the canonical wall fully routed to the
curved-eliminated binary frontier -/

/-- Common stationary packet after the complete currently-green canonical
wall analysis has been assembled. -/
inductive AdaptiveAlignedSmithCanonicalCurvedEliminatedStationaryPacket
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

/-- Refine the zero-jet common packet by actually running the complete binary
Hesse chain on its canonical-wall constructor. -/
theorem AdaptiveAlignedSmithCanonicalZeroJetStationaryPlanarCorePacket.toCurvedEliminatedPacket
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalZeroJetStationaryPlanarCorePacket s) :
    AdaptiveAlignedSmithCanonicalCurvedEliminatedStationaryPacket s := by
  cases P with
  | earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R
  | canonicalWall S clock_eq clock_pos C heq L =>
      rcases L.toCurvedEliminatedCore with ⟨F⟩
      exact .canonicalWall S clock_eq clock_pos C heq F
  | zeroSchur S clock_eq clock_pos C =>
      exact .zeroSchur S clock_eq clock_pos C
  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .planarRigid S clock_eq clock_pos hall P hrigid
  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .wSquareRigid S clock_eq clock_pos hall P hrigid

/-! ## One global scale-sound frontier after all current stationary-core work -/

/-- Global exact-clock frontier after assembling every currently-green local
stationary-core theorem.

The first three constructors are already terminal/progress outcomes.  The
remaining constructors are the exact residual closure obligations; none is
silently treated as progress. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyOutcome
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

  | stationary
      (P : AdaptiveAlignedSmithCanonicalCurvedEliminatedStationaryPacket s)

  | sectionGauge
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- **Final stationary-planar-core assembly frontier.**

Starting from the scale-sound exact-clock dispatcher, consume all already
certified global exits and route every residual canonical wall through the
complete green stationary planar-core chain, ending at the curved-eliminated
binary frontier. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreFinalAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyOutcome
      RR s complexity := by
  rcases s.alignedSmithCanonicalExactClockAssemblyFrontier
      RR complexity hsrepair with
    hzero | ⟨target, hspend⟩ |
    ⟨outer, target, hmove, hprogress⟩ | ⟨R⟩

  · exact .zeroDefect hzero
  · exact .ramifiedSpend target hspend
  · exact .rankTwoMacro outer target hmove hprogress
  · have O₀ := R.toStationaryConvergenceOutcome RR complexity hsrepair
    have O₁ := O₀.toPlanarAffineOutcome
    have O₂ := O₁.toZeroJetPlanarCoreOutcome
    cases O₂ with
    | rankTwoMacro outer target hmove hprogress =>
        exact .rankTwoMacro outer target hmove hprogress
    | stationary P =>
        exact .stationary P.toCurvedEliminatedPacket
    | sectionGauge S clock_eq clock_pos C heq G =>
        exact .sectionGauge S clock_eq clock_pos C heq G
    | survivingExactClock W clock_eq =>
        exact .survivingExactClock W clock_eq
    | sectionBoundaryInternal B =>
        exact .sectionBoundaryInternal B

end

end HC4.Valuation
