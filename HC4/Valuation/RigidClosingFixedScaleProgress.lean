import HC4.Valuation.CertifiedFixedScaleRestartEpisodeProgress
import HC4.Valuation.RigidClosingFirstKernelStage
import Mathlib.Tactic

/-!
# Rigid closing restart -> fixed-scale defect progress

The rigid closing machinery already produces a genuine polynomial-family
kernel restart.  Its legacy arithmetic is expressed on the common aligned
Smith ramification scale

    R = alignedSmithRamificationIndex,

with source clock

    R * Δ

and target clock

    R * Δ - 2*q,

where `q > 0`.

For the new global architecture we do not compare quotients across changing
scales.  We instead extract the stronger fact needed inside one frozen
episode:

    R * Δ - 2*q < R * Δ.

This is strict descent of an actual natural-number clock at one literal
parameter scale.

The second theorem is the progress adapter: whenever two actual scale-aware
geometric states are recorded at that same scale and carry those exact raw
clocks, the target is a strict successor in every certified fixed-scale
episode order.

No representation of the internal kernel-restart certificate is duplicated
here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A concrete rigid closing restart spends a strictly positive amount of
the raw determinant clock at the frozen aligned-Smith scale.

The upper bound needed for natural subtraction comes from the actual
`positiveDefectDrop` certificate stored by the rigid restart.
-/
theorem HasRigidClosingStrictKernelRestart.fixedScaleRawDefect_lt
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData)
    (h : S.HasRigidClosingStrictKernelRestart) :
    ∃ q : ℕ,
      0 < q ∧
      alignedSmithRamificationIndex * f.defect - 2 * q <
        alignedSmithRamificationIndex * f.defect := by
  rcases h with ⟨q, _hdiv, hq, hcert⟩
  have hdrop := hcert.positiveDefectDrop
  rcases hdrop with ⟨_hq, hle, _hdefect⟩
  refine ⟨q, hq, ?_⟩
  have hcost : 0 < 2 * q := by omega
  have hsourcePos :
      0 < alignedSmithRamificationIndex * f.defect := by
    by_contra hnot
    have hzero :
        alignedSmithRamificationIndex * f.defect = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hbad : 2 * q ≤ 0 := by
      simpa [hzero] using hle
    omega
  omega

/-- Same-scale geometric clock adapter.

This is deliberately independent of the rigid certificate itself.  Once a
geometric restart adapter constructs source and target states with a common
scale and proves the strict raw-clock inequality, the global well-founded
relation follows immediately.
-/
theorem certifiedFixedScaleEpisodeProgress_of_exactClocks
    (R : RepairRanking)
    {source target :
      ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {scale sourceClock targetClock : ℕ}
    (hsourceScale : source.scale = scale)
    (htargetScale : target.scale = scale)
    (hsourceClock : source.rawDefect = sourceClock)
    (htargetClock : target.rawDefect = targetClock)
    (hclock : targetClock < sourceClock) :
    CertifiedFixedScaleEpisodeProgress R target source := by
  have hsame : SameEpisodeScale target source := by
    unfold SameEpisodeScale
    rw [htargetScale, hsourceScale]
  apply
    certifiedFixedScaleEpisodeProgress_of_rawDefect_lt
      (K := K) R hsame
  rw [htargetClock, hsourceClock]
  exact hclock

/-- Rigid-clock specialization of the generic geometric adapter.

The next geometry module can use this theorem after destructing its rigid
restart certificate and constructing the actual target family/section.
-/
theorem certifiedFixedScaleEpisodeProgress_of_rigidClock
    (R : RepairRanking)
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    {source target :
      ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (q : ℕ)
    (hsourceScale :
      source.scale = alignedSmithRamificationIndex)
    (htargetScale :
      target.scale = alignedSmithRamificationIndex)
    (hsourceClock :
      source.rawDefect =
        alignedSmithRamificationIndex * f.defect)
    (htargetClock :
      target.rawDefect =
        alignedSmithRamificationIndex * f.defect - 2 * q)
    (hclock :
      alignedSmithRamificationIndex * f.defect - 2 * q <
        alignedSmithRamificationIndex * f.defect) :
    CertifiedFixedScaleEpisodeProgress R target source := by
  exact
    certifiedFixedScaleEpisodeProgress_of_exactClocks
      (K := K) R
      hsourceScale htargetScale
      hsourceClock htargetClock hclock

end

end HC4.Valuation
