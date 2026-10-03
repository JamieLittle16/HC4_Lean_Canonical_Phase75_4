import HC4.Valuation.AdaptiveAlignedSmithAllMinorsRigidClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerGeometry
import Mathlib.Tactic

/-!
# A18.4.102: presented-blocker geometry with rigid packet provenance

A18.4.101 removes the spurious packet escalation from the all-minors producer.
This file reruns the small presented-blocker Hessian dispatcher with that
stronger producer.

The only rank-two geometries that remain are genuine Schur first-departure
events.  The all-minors side contains only transverse freeness or a rigid
planar/`w^2` packet.  In particular there is no constructor corresponding to
an abstract nondegenerate packet.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Schur geometry which genuinely supplies a first `1 -> 2` event on the
presented blocker. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerSchurRankTwoGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    Type (u + 1)
  | schurPreterminal
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (preterminal : chart.clock.firstOrder < D.blocker.aligned.endpoint.defect)
  | zeroSchurPreterminal
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (residual : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (residual_pos : 0 < chart.zeroData.toClock.residualDefect)
      (residual_clock : residual.defect = chart.zeroData.toClock.residualDefect)
      (preterminal : residual.firstOrder < residual.defect)

/-- Lossless local blocker outcome after packet escalation has been removed at
its producer. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerRigidPacketOutcome
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) : Prop
  | zeroDefect
      (hzero : D.blocker.aligned.endpoint.defect = 0)
  | schurRankTwo
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerSchurRankTwoGeometry D))
  | schurClosing
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (closing : chart.clock.firstOrder = D.blocker.aligned.endpoint.defect)
      (transverse :
        chart.clock.series.offDiag.coeff D.blocker.aligned.endpoint.defect ≠ 0 ∨
        chart.clock.series.kernel.coeff D.blocker.aligned.endpoint.defect ≠ 0)
  | zeroSchurClosing
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (closing : HasAdaptiveAlignedZeroSchurClosing chart.zeroData)
  | transverseFree
      (allMinors :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho D.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (free :
        ∀ d ∈ D.blocker.aligned.endpoint.rawSpecialFiber.support,
          d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0)
  | planarRigid
      (allMinors :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho D.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) D.blocker)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)
  | wSquareRigid
      (allMinors :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho D.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) D.blocker)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- **Packet-rigid presented blocker dispatcher.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.rigidPacketGeometricOutcome
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerRigidPacketOutcome D := by
  by_cases hz : D.blocker.aligned.endpoint.defect = 0
  · exact .zeroDefect hz
  have hpos : 0 < D.blocker.aligned.endpoint.defect := Nat.pos_of_ne_zero hz

  rcases D.blocker.exists_exactRightRecenteredHessianChart_or_allMinors with
    hchart | hall

  · let H := Classical.choice hchart
    rcases D.blocker.schur_or_zeroSchur_of_exactChart H hpos with
      hschur | hzero

    · let C := Classical.choice hschur
      rcases C.clock.firstOrder_preterminal_or_closing with hpre | hclose
      · exact .schurRankTwo ⟨.schurPreterminal C hpre⟩
      · exact .schurClosing C hclose
          (C.clock.closing_transverse_nonzero hclose)

    · let Z := Classical.choice hzero
      let E := Z.zeroData.toClock
      by_cases hres0 : E.residualDefect = 0
      · exact .zeroSchurClosing Z
          (Or.inl ⟨hres0,
            E.tail_constant_det_ne_zero_of_residual_zero hres0⟩)
      · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
        rcases E.tail_pivot_of_residual_pos hres with hleft | hright
        · let R := E.toRankOneClockLeft hres hleft
          rcases lt_or_eq_of_le R.firstOrder_le_defect with hpre | hclose
          · exact .schurRankTwo
              ⟨.zeroSchurPreterminal Z R hres rfl hpre⟩
          · have htrans := R.series.transverse_nonzero_at_first R.hasTransverse
            have hfirst :
                R.series.firstPositiveTransverseOrder R.hasTransverse =
                  R.defect := by
              simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
            rw [hfirst] at htrans
            exact .zeroSchurClosing Z
              (Or.inr ⟨R, hres, rfl, hclose, htrans⟩)
        · let R := E.toRankOneClockRight hres hright
          rcases lt_or_eq_of_le R.firstOrder_le_defect with hpre | hclose
          · exact .schurRankTwo
              ⟨.zeroSchurPreterminal Z R hres rfl hpre⟩
          · have htrans := R.series.transverse_nonzero_at_first R.hasTransverse
            have hfirst :
                R.series.firstPositiveTransverseOrder R.hasTransverse =
                  R.defect := by
              simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
            rw [hfirst] at htrans
            exact .zeroSchurClosing Z
              (Or.inr ⟨R, hres, rfl, hclose, htrans⟩)

  · cases D.blocker.allMinorsRigidOutcome hall with
    | transverseFree hfree =>
        exact .transverseFree hall hfree
    | planarRigid P =>
        exact .planarRigid hall P.packet P.rigid
    | wSquareRigid P hrigid =>
        exact .wSquareRigid hall P hrigid

end

end HC4.Valuation
