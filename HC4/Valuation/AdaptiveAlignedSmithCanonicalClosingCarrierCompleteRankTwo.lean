import HC4.Valuation.AdaptiveAlignedSmithCanonicalConstantKernelCompleteRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosure
import Mathlib.Tactic

/-!
# A18.4.72: closing-carrier and rigid endpoints are rank-two only

The B38 closing-carrier split already had geometry on every branch except the
literal constant-source-kernel leaf.  A18.4.71 now supplies complete
post-opening Hessian geometry on that leaf as well.  Consequently the entire
closing-carrier endpoint has only rank-two geometric outcomes.

The same replacement propagates through the A17 rigid top-layer/top-kernel/
mixed-cross chain: its endpoint is the same literal constant-kernel geometry,
so the rigid obstruction also terminates directly in a geometry-backed
rank-two target.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete B38 closing-carrier outcome: every branch now carries rank-two
geometry. -/
inductive AdaptiveAlignedSmithCanonicalClosingCarrierCompleteRankTwoOutcome
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (complexity : ℕ) : Prop
  | kernelRankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
          RR s complexity))
  | residualRankTwo
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry (K := K) S complexity))

/-- **Complete geometry-preserving B38 closing-carrier termination.** -/
theorem AdaptiveAlignedSmithCanonicalTerminalSourcePacket.closingCarrier_completeRankTwoOutcome_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker) :
    AdaptiveAlignedSmithCanonicalClosingCarrierCompleteRankTwoOutcome RR S complexity := by
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
        exact .kernelRankTwo
          (Dker.completeRankTwoProgress_currentScale
            RR S clock_eq complexity hsrepair)
      · rcases hactive with ⟨M⟩
        let E := M.toEulerMotionData
        rcases E.exists_liftDerivativeRankTwoRepairData complexity with ⟨R2⟩
        exact .residualRankTwo ⟨.clearedLiftDerivative C R R2⟩

/-- The entire A17 rigid obstruction now ends in complete geometry-backed
rank-two progress. -/
theorem AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction.completeRankTwoOutcome_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
        RR s complexity) := by
  rcases R.toRigidTopLayerData with ⟨top⟩
  rcases top.toRigidTopKernelData with ⟨kernel⟩
  rcases kernel.toRigidMixedLayerCrossData with ⟨mixed⟩
  exact mixed.completeRankTwoProgress_currentScale
    RR S clock_eq complexity hsrepair

end

end HC4.Valuation
