import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedFirstContactNormalization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerClosure
import Mathlib.Tactic

/-!
# A18.4.51: presented blocker closes without a rational recursive edge

A18.4.35 closed every local blocker branch, but two of its final adapters still
forgot first-contact geometry and returned a `GlobalRamifiedStrictMacro`:
positive rational normalisation, and the literal constant-kernel leaf of the
deep rigid/closing algebra.

A18.4.48 and A18.4.50 remove both losses.  This file reruns the final presented
blocker splice with those stronger interfaces.  Every output is now one of:

* zero determinant defect on the original source;
* a strict fixed-scale successor of the already-presented state, with the
  source presentation retained beside it; or
* a geometry-carrying rank-two promotion which is globally strict from the
  original source by the finite repair measure.

There is no ramified raw-defect spend and no anonymous ramified strict macro in
the resulting frontier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Same-scale progress reached after a pure source presentation.  The
presentation is retained explicitly rather than collapsing the target to a
cross-scale comparison with the original source. -/
structure AdaptiveAlignedSmithCanonicalPresentedSameScaleProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove presented source
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  progress : CertifiedSameScaleEpisodeProgress RR target presented

/-- Generic wrapper for a geometry-backed nonlinear first-contact rank
promotion reached after an arbitrary pure presentation of the original source.
The local first-contact packet itself is retained. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedFactorOneKernelRankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove presented source
  local :
    AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
      RR presented complexity
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress local.openingProgress.target source

/-- Any local geometry-backed rank promotion remains globally strict from an
older pure presentation source, because only the finite repair coordinate is
used for the recursive comparison. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPresentedFactorOneKernelRankTwoProgress.ofLocal
    (RR : RepairRanking)
    {source presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hsource : HasCertifiedRamifiedEpisodeInternalMove presented source)
    (P : AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
      RR presented complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedFactorOneKernelRankTwoProgress
      RR source complexity := by
  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress P.openingProgress.target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [P.openingProgress.target_eq]
    change RepairState.measure (rankTwoRepairState complexity) <
      RepairState.measure source.repair
    rw [hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    presented := presented
    sourcePresentation := hsource
    local := P
    globalProgress := hglobal
  }

/-! ## First-contact-aware closing-carrier split -/

/-- The B38 closing-carrier split with the literal constant-source-kernel leaf
routed through A18.4.48 instead of a ramified spend. -/
inductive AdaptiveAlignedSmithCanonicalClosingCarrierFirstContactOutcome
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (complexity : ℕ) : Prop
  | sameScale
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : CertifiedSameScaleEpisodeProgress RR target s)
  | kernelRankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
          RR s complexity))
  | residualRankTwo
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry (K := K) S complexity))

/-- Geometry-preserving B38 closing-carrier termination at the current scale. -/
theorem AdaptiveAlignedSmithCanonicalTerminalSourcePacket.closingCarrier_firstContactOutcome_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker) :
    AdaptiveAlignedSmithCanonicalClosingCarrierFirstContactOutcome RR S complexity := by
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
    exact .residualRankTwo ⟨.rawSchurDerivative C R⟩

  · rcases hconstant with ⟨L⟩
    rcases hkey.exists_constantLineCanonicalProvenance L with ⟨A, hAE⟩
    rcases A.rankTwoRepair_or_rs2Ready complexity with hrepair | hrs2
    · rcases hrepair with ⟨R⟩
      exact .residualRankTwo ⟨.firstKeyTransverse C L A hAE R⟩
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
        rcases Dker.sameScale_or_rankTwoProgress_currentScale
            RR S clock_eq complexity hsrepair with hstrict | hRankTwo
        · rcases hstrict with ⟨target, ht⟩
          exact .sameScale target ht
        · exact .kernelRankTwo hRankTwo
      · rcases hactive with ⟨M⟩
        let E := M.toEulerMotionData
        rcases E.exists_liftDerivativeRankTwoRepairData complexity with ⟨R2⟩
        exact .residualRankTwo ⟨.clearedLiftDerivative C R R2⟩

/-! ## First-contact-aware rigid endpoint -/

/-- Reuse the entire A17 rigid top-layer/top-kernel/mixed-cross chain, but keep
A18.4.48's same-scale-or-rank-two endpoint. -/
theorem AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction.firstContactOutcome_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
          RR s complexity) := by
  rcases R.toRigidTopLayerData with ⟨top⟩
  rcases top.toRigidTopKernelData with ⟨kernel⟩
  rcases kernel.toRigidMixedLayerCrossData with ⟨mixed⟩
  exact mixed.sameScale_or_rankTwoProgress_currentScale
    RR S clock_eq complexity hsrepair

/-! ## Final no-spend presented-blocker closure -/

/-- Lossless closed frontier for one presented blocker.  Every rank-promotion
constructor retains its geometric payload. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosedOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : source.rawDefect = 0)
  | presentedSameScale
      (P : AdaptiveAlignedSmithCanonicalPresentedSameScaleProgress RR source)
  | positiveKernelRankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankTwoProgress
          RR D complexity))
  | factorOneKernelRankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedFactorOneKernelRankTwoProgress
          RR source complexity))
  | blockerRankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
          RR D complexity))
  | stationaryRankTwo
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
          RR D S complexity))

/-- **A18.4.51 presented blocker first-contact closure.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.firstContactSoundClosure
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosedOutcome
      RR D complexity := by
  cases D.firstContactRationalNormalizationOutcome RR complexity hsrepair with
  | presentedSameScale target h =>
      exact .presentedSameScale {
        presented := D.presented
        sourcePresentation := D.sourcePresentation
        target := target
        progress := h
      }
  | rankTwo P =>
      exact .positiveKernelRankTwo P
  | stationary Z S hblock =>
      have hclock : S.blocker.aligned.endpoint.defect = D.presented.rawDefect := by
        rw [hblock]
        exact D.defect_eq
      have hpresentedRepair : D.presented.repair = rankOneRepairState complexity := by
        rcases D.sourcePresentation with ⟨hmove⟩
        rw [hmove.repair_eq]
        exact hsrepair

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
          exact .blockerRankTwo ⟨P⟩

      | schurClosing chart closing transverse =>
          let C0 : AdaptiveAlignedSmithRankOneClosingSourceCarrier D.blocker := {
            source := D.blocker.recenteredSourceData
            chartData := chart
            closing := ⟨closing, transverse⟩
          }
          let C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker := by
            rw [hblock]
            exact C0
          cases S.toTerminalSourcePacket.closingCarrier_firstContactOutcome_currentScale
              RR hclock complexity hpresentedRepair C with
          | sameScale target h =>
              exact .presentedSameScale {
                presented := D.presented
                sourcePresentation := D.sourcePresentation
                target := target
                progress := h
              }
          | kernelRankTwo P =>
              rcases P with ⟨P⟩
              exact .factorOneKernelRankTwo ⟨
                AdaptiveAlignedSmithCanonicalGlobalPresentedFactorOneKernelRankTwoProgress.ofLocal
                  RR complexity hsrepair D.sourcePresentation P
              ⟩
          | residualRankTwo hgeometry =>
              rcases hgeometry with ⟨G⟩
              let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
                  D S complexity := {
                blocker_eq := hblock
                witness := Sum.inl G
              }
              let P := AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
                RR D S complexity hsrepair GG
              exact .stationaryRankTwo S ⟨P⟩

      | zeroSchurClosing chart closing =>
          let G0 : AdaptiveAlignedSmithCanonicalPresentedZeroSchurRankTwoGeometry D := {
            chart := chart
            activeDet_coeff_zero_ne_zero := chart.zeroData.activeDet_coeff_zero_ne_zero
            schurA_coeff_zero := chart.zeroData.schurA_coeff_zero
            schurB_coeff_zero := chart.zeroData.schurB_coeff_zero
            schurC_coeff_zero := chart.zeroData.schurC_coeff_zero
          }
          let GG : AdaptiveAlignedSmithCanonicalPresentedStationaryRankTwoGeometry
              D S complexity := {
            blocker_eq := hblock
            witness := Sum.inr G0
          }
          let P := AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress.ofGeometry
            RR D S complexity hsrepair GG
          exact .stationaryRankTwo S ⟨P⟩

      | transverseFree hall hfree =>
          have hfreeS :
              ∀ d ∈ S.blocker.aligned.endpoint.rawSpecialFiber.support,
                d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0 := by
            simpa [hblock] using hfree
          exact (S.not_rawSpecialFiber_transverseFree hfreeS).elim

      | planarRigid hall P hrigid =>
          let P' : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
              (K := K) S.blocker := by
            rw [hblock]
            exact P
          have hall' :
              ∀ rho : Equiv.Perm (Fin 4),
                (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
                  rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
            simpa [hblock] using hall
          have hrigid' : HasRigidRankOnePacket
              (0 : Fin 4) 1 2 P'.degree P'.packet := by
            simpa [P'] using hrigid
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
            source := S.toTerminalSourcePacket
            hall := hall'
            packet := .planar P' hrigid'
          }
          rcases R.firstContactOutcome_currentScale
              RR hclock complexity hpresentedRepair with hstrict | hRankTwo
          · rcases hstrict with ⟨target, h⟩
            exact .presentedSameScale {
              presented := D.presented
              sourcePresentation := D.sourcePresentation
              target := target
              progress := h
            }
          · rcases hRankTwo with ⟨P⟩
            exact .factorOneKernelRankTwo ⟨
              AdaptiveAlignedSmithCanonicalGlobalPresentedFactorOneKernelRankTwoProgress.ofLocal
                RR complexity hsrepair D.sourcePresentation P
            ⟩

      | wSquareRigid hall P hrigid =>
          let P' : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) S.blocker := by
            rw [hblock]
            exact P
          have hall' :
              ∀ rho : Equiv.Perm (Fin 4),
                (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
                  rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero := by
            simpa [hblock] using hall
          have hrigid' : HasRigidRankOnePacket
              (0 : Fin 4) 3 2 P'.degree P'.packet := by
            simpa [P'] using hrigid
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
            source := S.toTerminalSourcePacket
            hall := hall'
            packet := .wSquare P' hrigid'
          }
          rcases R.firstContactOutcome_currentScale
              RR hclock complexity hpresentedRepair with hstrict | hRankTwo
          · rcases hstrict with ⟨target, h⟩
            exact .presentedSameScale {
              presented := D.presented
              sourcePresentation := D.sourcePresentation
              target := target
              progress := h
            }
          · rcases hRankTwo with ⟨P⟩
            exact .factorOneKernelRankTwo ⟨
              AdaptiveAlignedSmithCanonicalGlobalPresentedFactorOneKernelRankTwoProgress.ofLocal
                RR complexity hsrepair D.sourcePresentation P
            ⟩

end

end HC4.Valuation
