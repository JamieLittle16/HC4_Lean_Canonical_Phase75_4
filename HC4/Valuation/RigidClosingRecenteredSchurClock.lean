import HC4.Valuation.RigidClosingRecenteredSource
import HC4.Valuation.RigidPacketZeroSchurBridge
import Mathlib.Tactic

/-!
# Rebuilding the rigid Schur clock after moving-section recentering

The original rigid closing clock is attached to the defect-preserving Smith
exposure before the affine translation which sends the left moving collision
section to zero.  A parameter-dependent translation need not preserve higher
Schur coefficients, so later source-lattice arguments must not mix that old
clock with the recentered family.

This file removes that ambiguity.  Translation by a section reducing to zero
leaves the special fibre unchanged.  Hence the same rigid packet chart can be
applied to the recentered family itself.  Its Hessian determinant still has the
same exact pure parameter order, so we obtain a fresh exact zero-Schur clock on
exactly the family consumed by the global kernel blow-ups.

Running the already-green two-stage clock on this refreshed block gives either
immediate rank-two repair progress or a closing certificate genuinely attached
to the recentered source family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

namespace CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData

variable [CharZero K]
variable {D complexity : ℕ}
variable {f : CanonicalSmithDepartureFrontier (K := K) D complexity}

/-- Affine recentering does not alter the rigid packet special fibre because
its translation section reduces to the origin. -/
theorem recenteredSpecialFiber_eq_packet
    (S : f.RigidClosingExactCollisionSourceData) :
    polynomialFamilySpecialFiber S.recenteredFamily =
      f.lossless.packet := by
  rw [recenteredFamily]
  rw [polynomialFamilySpecialFiber_translation_eq_of_specialPoint_zero
    (K := K) f.defectSmithExposureLeftSection S.leftSpecial]
  exact S.specialFiberPacket

/-- Left-pivot exact zero-Schur block rebuilt on the recentered family. -/
noncomputable def recenteredLeftZeroSchurData
    (S : f.RigidClosingExactCollisionSourceData)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 D f.lossless.packet)
    (hleft :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).LeftPivot)
    (hD : 3 ≤ D) :
    ExactZeroSchurFourBlockData K := by
  have hchart :=
    rigidPacket_left_zeroSchurChart
      f.lossless.persistentPacket hrigid hleft hD
  refine {
    block := rigidExposureLeftFourBlock S.recenteredFamily
    defect := alignedSmithRamificationIndex * f.defect
    fullDet := ?_
    activeDet_coeff_zero_ne_zero := ?_
    schurA_coeff_zero := ?_
    schurB_coeff_zero := ?_
    schurC_coeff_zero := ?_
  }
  · exact evaluatedFamilyHessianFourBlock_determinantCore_eq_X_pow
      (Equiv.refl (Fin 4)) S.recenteredFamily rigidLeftChartPoint
      S.recenteredHessianDefect
  · rw [rigidExposureLeftFourBlock_activeDet_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.1
  · rw [rigidExposureLeftFourBlock_schurA_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.2.1
  · rw [rigidExposureLeftFourBlock_schurB_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.2.2.1
  · rw [rigidExposureLeftFourBlock_schurC_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.2.2.2

/-- Right-axis exact zero-Schur block rebuilt on the recentered family. -/
noncomputable def recenteredRightZeroSchurData
    (S : f.RigidClosingExactCollisionSourceData)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 D f.lossless.packet)
    (hright :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).RightAxisPivot)
    (hD : 3 ≤ D) :
    ExactZeroSchurFourBlockData K := by
  have hchart :=
    rigidPacket_right_zeroSchurChart
      f.lossless.persistentPacket hright hD
  refine {
    block := rigidExposureRightFourBlock S.recenteredFamily
    defect := alignedSmithRamificationIndex * f.defect
    fullDet := ?_
    activeDet_coeff_zero_ne_zero := ?_
    schurA_coeff_zero := ?_
    schurB_coeff_zero := ?_
    schurC_coeff_zero := ?_
  }
  · exact evaluatedFamilyHessianFourBlock_determinantCore_eq_X_pow
      rigidRightChartPerm S.recenteredFamily rigidRightChartPoint
      S.recenteredHessianDefect
  · rw [rigidExposureRightFourBlock_activeDet_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.1
  · rw [rigidExposureRightFourBlock_schurA_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.2.1
  · rw [rigidExposureRightFourBlock_schurB_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.2.2.1
  · rw [rigidExposureRightFourBlock_schurC_coeff_zero (D := D)]
    rw [S.recenteredSpecialFiber_eq_packet]
    exact hchart.2.2.2

/-- Provenance-preserving closing certificate for a Schur clock rebuilt on
`S.recenteredFamily` itself. -/
inductive RecenteredRigidClosingCertificate
    (S : f.RigidClosingExactCollisionSourceData) : Prop
  | left
      (hD : 3 ≤ D)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D f.lossless.packet)
      (hpivot :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 D f.lossless.packet).LeftPivot)
      (hclosing :
        ExactZeroSchurClosingOutcome
          (S.recenteredLeftZeroSchurData hrigid hpivot hD)) :
      RecenteredRigidClosingCertificate S
  | right
      (hD : 3 ≤ D)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D f.lossless.packet)
      (hpivot :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 D f.lossless.packet).RightAxisPivot)
      (hclosing :
        ExactZeroSchurClosingOutcome
          (S.recenteredRightZeroSchurData hrigid hpivot hD)) :
      RecenteredRigidClosingCertificate S

/-- Refresh the old pre-translation rigid clock on the recentered source.
The refreshed clock may expose rank-two progress even when the old chart was
closing; otherwise its new closing data belongs to exactly the family used by
the source-lattice endgame. -/
theorem rankTwoProgress_or_recenteredClosing
    (S : f.RigidClosingExactCollisionSourceData) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      RecenteredRigidClosingCertificate S := by
  cases S.closing with
  | left hD hrigid hpivot _holdClosing =>
      let B := S.recenteredLeftZeroSchurData hrigid hpivot hD
      rcases B.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inl hprogress
      · exact Or.inr (.left hD hrigid hpivot (by
          simpa [ExactZeroSchurClosingOutcome] using hclosing))
  | right hD hrigid hpivot _holdClosing =>
      let B := S.recenteredRightZeroSchurData hrigid hpivot hD
      rcases B.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inl hprogress
      · exact Or.inr (.right hD hrigid hpivot (by
          simpa [ExactZeroSchurClosingOutcome] using hclosing))

end CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData

end

end HC4.Valuation
