import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCurrentScaleConstantKernel
import HC4.Valuation.AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
import Mathlib.Tactic

/-!
# A18.4.35: close a boundary-produced presented blocker

A18.4.32 retains every local rank-two witness before changing the finite
repair coordinate.  A18.4.33 normalises rational kernel slopes at the actual
presented scale.  A18.4.34 makes the final literal constant-kernel exit of the
deep A17 planar-core argument available at that same scale.

This file composes those ingredients.  On the all-transverse-zero stationary
side:

* complete transverse freeness is impossible;
* either rigid packet follows the already-green A17 top-layer -> top-kernel ->
  mixed-layer-cross -> literal constant-kernel chain and spends;
* zero-Schur closing already contains a nonzero active `2 x 2` Hessian minor
  and therefore licenses a geometry-carrying rank promotion directly;
* rank-one Schur closing runs the B38 projective split.  Moving projective
  data gives retained rank-two geometry; the constant-source-kernel subcase
  is converted to the blocker-native literal kernel and spent by A18.4.34.

The final outcome has no blocker or presentation constructor: it is either
zero determinant defect on the original source or a genuine ramified strict
macro.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Current-scale closing-carrier split -/

/-- The B38 closing-carrier argument with only its final spend adapter changed
to the current presented scale.  All projective/first-key geometry is exactly
the already-green A18.4.24 geometry. -/
theorem AdaptiveAlignedSmithCanonicalTerminalSourcePacket.closingCarrier_ramifiedSpend_or_rankTwoGeometry_currentScale
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s) ∨
      Nonempty (AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
        (K := K) S complexity) := by
  have hpos :
      (positiveTransverseSourceSupport
        (polynomialFamilySpecialFiber C.family)).Nonempty := by
    rcases S.specialFiber_witnesses.1 with ⟨d, hd, hd1⟩
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family] using hd
    · unfold pureLongitudinalTransverseDegree
      omega
  have hkey : C.HasFirstTransverseSourceKey :=
    C.hasFirstTransverseSourceKey_of_positiveSupport hpos

  rcases C.rawSpecialSchurProjectiveWedge_or_constantLine with hmoving | hconstant
  · rcases hmoving with ⟨k, hk⟩
    rcases C.rawSpecialSchurDerivativeRankTwoRepairData_of_wedge
        complexity k hk with ⟨R⟩
    exact Or.inr ⟨.rawSchurDerivative C R⟩

  · rcases hconstant with ⟨L⟩
    rcases hkey.exists_constantLineCanonicalProvenance L with ⟨A, hAE⟩
    rcases A.rankTwoRepair_or_rs2Ready complexity with hrepair | hrs2
    · rcases hrepair with ⟨R⟩
      exact Or.inr ⟨.firstKeyTransverse C L A hAE R⟩
    · rcases hrs2 with ⟨N⟩
      let R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData := {
        line := L
        provenance := A
        provenance_schurKernel := hAE
        rs2Ready := N
      }
      rcases R.constantSourceKernel_or_activeProjective with hkernel | hactive
      · rcases hkernel with ⟨K0⟩
        let literal := K0.toLiteralConstantSpecialSourceKernelData
        have htrans := P.exists_transverse_of_literalConstantKernel literal
        let Dker : AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData S := {
          direction := literal.direction
          direction_ne_zero := literal.direction_ne_zero
          transverse := htrans
          kernel := by
            simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family] using
              literal.kernel
        }
        exact Or.inl (Dker.exists_ramifiedSpend_currentScale S clock_eq)
      · rcases hactive with ⟨M⟩
        let E := M.toEulerMotionData
        rcases E.exists_liftDerivativeRankTwoRepairData complexity with ⟨R2⟩
        exact Or.inr ⟨.clearedLiftDerivative C R R2⟩

/-! ## Current-scale rigid spend -/

/-- Reuse the entire A17 rigid algebra and change only its final literal
constant-kernel spend to A18.4.34's current-scale adapter. -/
theorem AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction.exists_directRamifiedSpend_currentScale
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rcases R.toRigidTopLayerData with ⟨top⟩
  rcases top.toRigidTopKernelData with ⟨kernel⟩
  rcases kernel.toRigidMixedLayerCrossData with ⟨mixed⟩
  exact mixed.exists_ramifiedSpend_currentScale S clock_eq

/-! ## Equality-safe packet transport -/

/-- Transport a planar rigid packet and its dependent rigidity certificate
across literal blocker equality in one equality elimination. -/
noncomputable def transportPlanarRigidPacket
    {degreeCap : ℕ}
    {B₁ B₂ : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (h : B₁ = B₂)
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B₂)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 P.degree P.packet) :
    Σ P' : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B₁,
      HasRigidRankOnePacket (0 : Fin 4) 1 2 P'.degree P'.packet := by
  cases h
  exact ⟨P, hrigid⟩

/-- Transport a `w²` rigid packet and its dependent rigidity certificate
across literal blocker equality in one equality elimination. -/
noncomputable def transportWSquareRigidPacket
    {degreeCap : ℕ}
    {B₁ B₂ : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (h : B₁ = B₂)
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B₂)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 3 2 P.degree P.packet) :
    Σ P' : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B₁,
      HasRigidRankOnePacket (0 : Fin 4) 3 2 P'.degree P'.packet := by
  cases h
  exact ⟨P, hrigid⟩

/-! ## Geometry retained by current-scale rank promotion -/

/-- A zero-Schur blocker already retains the exact honest chart together with
its nonzero active minor and three zero-Schur certificates.  No duplicate
proof fields are needed here: they are fields of `chart.zeroData` itself. -/
structure AdaptiveAlignedSmithCanonicalPresentedZeroSchurRankTwoGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    Type (u + 1) where
  chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker

/-- The final stationary rank-two witness is either B38 residual geometry or
the literal zero-Schur active minor.  `blocker_eq` ties either stationary
witness back to the actual presented family. -/
structure AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
    (complexity : ℕ) : Type (u + 1) where
  blocker_eq : S.blocker = D.blocker
  witness :
    (AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry (K := K) S complexity) ⊕
      AdaptiveAlignedSmithCanonicalPresentedZeroSchurRankTwoGeometry D

/-- Geometry-carrying rank promotion for the final stationary presented
blocker. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
    (complexity : ℕ) : Type (u + 1) where
  geometry : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry D S complexity
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq : target = D.presented.withRepairOnly (rankTwoRepairState complexity)
  presentedProgress : CertifiedSameScaleEpisodeProgress RR target D.presented
  globalProgress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

noncomputable def AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (G : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry D S complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
      RR D S complexity := by
  let target := D.presented.withRepairOnly (rankTwoRepairState complexity)
  have hpresentedRepair : D.presented.repair = rankOneRepairState complexity := by
    rcases D.sourcePresentation with ⟨hmove⟩
    rw [hmove.repair_eq]
    exact hsrepair
  have hrepair :
      RepairProgress D.presented.repair (rankTwoRepairState complexity) := by
    simpa [hpresentedRepair] using rankOne_to_rankTwo_repairProgress complexity
  have hprogress : CertifiedSameScaleEpisodeProgress RR target D.presented := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [show target.repair = rankTwoRepairState complexity by rfl, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    geometry := G
    target := target
    target_eq := rfl
    presentedProgress := hprogress
    globalProgress := hglobal
  }

/-- Promote the retained current-scale witness to the source-honest strict
macro. -/
theorem AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.toRamifiedStrictMacro
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
      RR D S complexity) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source :=
  .mk D.presented P.target D.sourcePresentation P.presentedProgress

/-! ## Final presented-blocker closure -/

inductive AdaptiveAlignedSmithCanonicalPresentedBlockerClosedOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | zeroDefect (hzero : source.rawDefect = 0)
  | ramifiedStrictMacro
      (P : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)

/-- **A18.4.35 presented blocker closure.**  No blocker-side residue survives. -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.soundClosure
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerClosedOutcome RR source := by
  rcases D.rationalNormalizationOutcome RR with hstrict | ⟨Z, S, hblock⟩
  · exact .ramifiedStrictMacro hstrict

  have hclock : S.blocker.aligned.endpoint.defect = D.presented.rawDefect := by
    rw [hblock]
    exact D.defect_eq

  cases D.geometricOutcome with
  | zeroDefect hzero =>
      have hpzero : D.presented.rawDefect = 0 := by
        rw [← D.defect_eq]
        exact hzero
      exact .zeroDefect
        (D.sourcePresentation.source_rawDefect_eq_zero_of_target hpzero)

  | rankTwoGeometry hG =>
      rcases hG with ⟨G⟩
      let P := AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress.ofGeometry
        RR D complexity hsrepair G
      exact .ramifiedStrictMacro (P.toRamifiedStrictMacro RR)

  | schurClosing chart closing transverse =>
      let C0 : AdaptiveAlignedSmithRankOneClosingSourceCarrier D.blocker := {
        source := D.blocker.recenteredSourceData
        chartData := chart
        closing := ⟨closing, transverse⟩
      }
      let C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker := by
        rw [hblock]
        exact C0
      rcases S.toTerminalSourcePacket.closingCarrier_ramifiedSpend_or_rankTwoGeometry_currentScale
          hclock complexity C with hspend | hgeometry
      · rcases hspend with ⟨target, h⟩
        exact .ramifiedStrictMacro
          ((h.toGlobalStrictMacro RR).prepend_internal RR D.sourcePresentation)
      · rcases hgeometry with ⟨G⟩
        let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
            D S complexity := {
          blocker_eq := hblock
          witness := Sum.inl G
        }
        let P := AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
          RR D S complexity hsrepair GG
        exact .ramifiedStrictMacro (P.toRamifiedStrictMacro RR)

  | zeroSchurClosing chart closing =>
      let G0 : AdaptiveAlignedSmithCanonicalPresentedZeroSchurRankTwoGeometry D := {
        chart := chart
      }
      let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
          D S complexity := {
        blocker_eq := hblock
        witness := Sum.inr G0
      }
      let P := AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
        RR D S complexity hsrepair GG
      exact .ramifiedStrictMacro (P.toRamifiedStrictMacro RR)

  | transverseFree hall hfree =>
      have hfreeS :
          ∀ d ∈ S.blocker.aligned.endpoint.rawSpecialFiber.support,
            d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0 := by
        simpa [hblock] using hfree
      exact (S.not_rawSpecialFiber_transverseFree hfreeS).elim

  | planarRigid hall P hrigid =>
      rcases transportPlanarRigidPacket (K := K) hblock P hrigid with
        ⟨P', hrigid'⟩
      have hall' :
          ∀ rho : Equiv.Perm (Fin 4),
            (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
              rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
        simpa [hblock] using hall
      let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
        source := S.toTerminalSourcePacket
        hall := hall'
        packet := .planar P' hrigid'
      }
      rcases R.exists_directRamifiedSpend_currentScale hclock with ⟨target, h⟩
      exact .ramifiedStrictMacro
        ((h.toGlobalStrictMacro RR).prepend_internal RR D.sourcePresentation)

  | wSquareRigid hall P hrigid =>
      rcases transportWSquareRigidPacket (K := K) hblock P hrigid with
        ⟨P', hrigid'⟩
      have hall' :
          ∀ rho : Equiv.Perm (Fin 4),
            (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
              rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
        simpa [hblock] using hall
      let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
        source := S.toTerminalSourcePacket
        hall := hall'
        packet := .wSquare P' hrigid'
      }
      rcases R.exists_directRamifiedSpend_currentScale hclock with ⟨target, h⟩
      exact .ramifiedStrictMacro
        ((h.toGlobalStrictMacro RR).prepend_internal RR D.sourcePresentation)

end

end HC4.Valuation
