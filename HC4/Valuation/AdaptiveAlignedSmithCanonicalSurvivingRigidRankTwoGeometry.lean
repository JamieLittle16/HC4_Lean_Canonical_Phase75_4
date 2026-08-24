import HC4.Valuation.AdaptiveAlignedSmithCanonicalDirectResidualClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCanonicalExposureNeutrality
import HC4.Valuation.AdaptiveAlignedSmithRigidPacketExposureClosing
import Mathlib.Tactic

/-!
# A18.4.26: retain the surviving rigid rank-two geometry

The old surviving-rigid reduction constructs an honest coefficientwise Smith
exposure and then an exact zero-Schur four-block on that exposed family.  In
the preterminal branch it historically returned only the generic
`RepairProgress rankOne rankTwo`, discarding both the exposure and the exact
Schur clock which forced that promotion.

This file reruns only that finite two-stage clock while retaining the actual
objects.  A surviving rigid packet now yields exactly one of:

* literal zero aligned defect;
* a genuine marked-point boundary on the honest exposure;
* a canonical exposure carrying an exact zero-Schur four-block and a
  preterminal residual rank-one clock with a nonzero mixed coefficient; or
* source-honest zero-Schur closing data on a canonical exposure.

No successor state is manufactured here.  In particular no `withRepairOnly`
state and no bare repair-progress constructor is exported.  The next global
layer may attach the finite repair promotion only after it has retained this
geometry and the actual exposed family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Geometry which genuinely justifies a rank-two promotion in the surviving
rigid-packet branch.

`zeroSchur_from_packet` records that the exact four-block is literally one of
the two packet-isolated Hessian charts.  `residualClock_from_zeroSchur` records
that the preterminal rank-one clock is literally one of the two canonical
alignments of the first nonzero zero-Schur tail. -/
structure AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree) : Type (u + 1) where
  exposure : AdaptiveSurvivingWallExposureData
    (W.original.aligned.toAdaptiveState s) W.wall
  canonicalSpecial :
    polynomialSectionSpecialPoint exposure.rightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  zeroSchur : ExactZeroSchurFourBlockData K
  zeroSchur_from_packet :
    (∃ hleft :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 P.degree P.packet).LeftPivot,
      zeroSchur = R.leftZeroSchurData s W P exposure hD hleft) ∨
    (∃ hright :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 P.degree P.packet).RightAxisPivot,
      zeroSchur = R.rightZeroSchurData s W P exposure hD hright)
  residualClock : ExactRankOneSchurClockAt K
  residual_pos : 0 < zeroSchur.toClock.residualDefect
  residualClock_from_zeroSchur :
    (∃ hleft : zeroSchur.toClock.tailSeries.LeftPivot,
      residualClock =
        zeroSchur.toClock.toRankOneClockLeft residual_pos hleft) ∨
    (∃ hright : zeroSchur.toClock.tailSeries.RightAxisPivot,
      residualClock =
        zeroSchur.toClock.toRankOneClockRight residual_pos hright)
  preterminal : residualClock.firstOrder < residualClock.defect
  offDiag_ne_zero :
    residualClock.series.offDiag.coeff residualClock.firstOrder ≠ 0

/-- Complete geometry-preserving local outcome for one surviving rigid packet.
The `canonicalClosing` constructor stores the canonical-special equation
explicitly, because it is exactly the input needed by the already-green
coordinate-3-free closing theorem. -/
inductive AdaptiveAlignedSmithCanonicalSurvivingRigidGeometricOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree) : Prop

  | zeroDefect
      (hzero : (W.original.aligned.toAdaptiveState s).defect = 0)

  | exposureBoundary
      (d : AdaptiveSurvivingWallExposureData
        (W.original.aligned.toAdaptiveState s) W.wall)
      (boundary : Nonempty (AdaptiveSmithExposureSectionBoundary d))

  | rankTwoGeometry
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
          s W P R hD))

  | canonicalClosing
      (d : AdaptiveSurvivingWallExposureData
        (W.original.aligned.toAdaptiveState s) W.wall)
      (canonicalSpecial :
        polynomialSectionSpecialPoint d.rightSection =
          coordinateAxisPoint (K := K) (0 : Fin 4))
      (C : Nonempty
        (AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
          (K := K) s W P R))

namespace AdaptiveAlignedSmithRigidPacketEndpoint

/-- Build the closing endpoint when the zero-Schur residual clock is already
zero. -/
private theorem closing_of_residual_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (Z : ExactZeroSchurFourBlockData K)
    (hres0 : Z.toClock.residualDefect = 0) :
    Nonempty
      (AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
        (K := K) s W P R) := by
  exact ⟨{
    exposure := d
    zeroSchur := Z
    closing := Or.inl
      ⟨hres0, Z.toClock.tail_constant_det_ne_zero_of_residual_zero hres0⟩
  }⟩

/-- Build the closing endpoint when the residual rank-one clock reaches its
first transverse layer exactly at determinant closure. -/
private theorem closing_of_rankOne_closure
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (Z : ExactZeroSchurFourBlockData K)
    (S : ExactRankOneSchurClockAt K)
    (hres : 0 < Z.toClock.residualDefect)
    (hclock : S.defect = Z.toClock.residualDefect)
    (hclose : S.firstOrder = S.defect) :
    Nonempty
      (AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
        (K := K) s W P R) := by
  have htrans := S.series.transverse_nonzero_at_first S.hasTransverse
  have hfirst :
      S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
    simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
  rw [hfirst] at htrans
  exact ⟨{
    exposure := d
    zeroSchur := Z
    closing := Or.inr ⟨S, hres, hclock, hclose, htrans⟩
  }⟩

/-- **Geometry-preserving surviving-rigid reduction.**

This expands the two places hidden by
`ExactZeroSchurFourBlockData.rankTwoProgress_or_closing`.  In a preterminal
branch the exact packet chart, the exact aligned residual clock, and its
nonzero mixed coefficient all survive as data. -/
theorem geometricOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree) :
    AdaptiveAlignedSmithCanonicalSurvivingRigidGeometricOutcome
      s W P R hD := by
  rcases W.zeroDefect_or_exposure s with hzero | hexposure
  · exact .zeroDefect hzero

  · let d : AdaptiveSurvivingWallExposureData
        (W.original.aligned.toAdaptiveState s) W.wall :=
      Classical.choice hexposure
    rcases d.canonicalSpecial_or_boundary with hspecial | hboundary
    · rcases R.pivot s W P with hpacketLeft | hpacketRight

      · let Z : ExactZeroSchurFourBlockData K :=
          R.leftZeroSchurData s W P d hD hpacketLeft
        let E := Z.toClock
        by_cases hres0 : E.residualDefect = 0
        · exact .canonicalClosing d hspecial
            (R.closing_of_residual_zero s W P d Z hres0)
        · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
          rcases E.tail_pivot_of_residual_pos hres with htailLeft | htailRight
          · let S := E.toRankOneClockLeft hres htailLeft
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · have hoff : S.series.offDiag.coeff S.firstOrder ≠ 0 :=
                S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
              exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                zeroSchur_from_packet := Or.inl ⟨hpacketLeft, rfl⟩
                residualClock := S
                residual_pos := hres
                residualClock_from_zeroSchur := Or.inl ⟨htailLeft, rfl⟩
                preterminal := hpre
                offDiag_ne_zero := hoff
              }⟩
            · exact .canonicalClosing d hspecial
                (R.closing_of_rankOne_closure
                  s W P d Z S hres rfl hclose)
          · let S := E.toRankOneClockRight hres htailRight
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · have hoff : S.series.offDiag.coeff S.firstOrder ≠ 0 :=
                S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
              exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                zeroSchur_from_packet := Or.inl ⟨hpacketLeft, rfl⟩
                residualClock := S
                residual_pos := hres
                residualClock_from_zeroSchur := Or.inr ⟨htailRight, rfl⟩
                preterminal := hpre
                offDiag_ne_zero := hoff
              }⟩
            · exact .canonicalClosing d hspecial
                (R.closing_of_rankOne_closure
                  s W P d Z S hres rfl hclose)

      · let Z : ExactZeroSchurFourBlockData K :=
          R.rightZeroSchurData s W P d hD hpacketRight
        let E := Z.toClock
        by_cases hres0 : E.residualDefect = 0
        · exact .canonicalClosing d hspecial
            (R.closing_of_residual_zero s W P d Z hres0)
        · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
          rcases E.tail_pivot_of_residual_pos hres with htailLeft | htailRight
          · let S := E.toRankOneClockLeft hres htailLeft
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · have hoff : S.series.offDiag.coeff S.firstOrder ≠ 0 :=
                S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
              exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                zeroSchur_from_packet := Or.inr ⟨hpacketRight, rfl⟩
                residualClock := S
                residual_pos := hres
                residualClock_from_zeroSchur := Or.inl ⟨htailLeft, rfl⟩
                preterminal := hpre
                offDiag_ne_zero := hoff
              }⟩
            · exact .canonicalClosing d hspecial
                (R.closing_of_rankOne_closure
                  s W P d Z S hres rfl hclose)
          · let S := E.toRankOneClockRight hres htailRight
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · have hoff : S.series.offDiag.coeff S.firstOrder ≠ 0 :=
                S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
              exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                zeroSchur_from_packet := Or.inr ⟨hpacketRight, rfl⟩
                residualClock := S
                residual_pos := hres
                residualClock_from_zeroSchur := Or.inr ⟨htailRight, rfl⟩
                preterminal := hpre
                offDiag_ne_zero := hoff
              }⟩
            · exact .canonicalClosing d hspecial
                (R.closing_of_rankOne_closure
                  s W P d Z S hres rfl hclose)

    · exact .exposureBoundary d hboundary

end AdaptiveAlignedSmithRigidPacketEndpoint

end

end HC4.Valuation
