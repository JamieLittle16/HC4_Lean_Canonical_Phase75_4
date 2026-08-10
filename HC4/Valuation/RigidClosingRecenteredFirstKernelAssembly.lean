import HC4.Valuation.RigidClosingRecenteredSchurClock
import HC4.Valuation.RigidClosingFirstKernelAssembly

/-!
# Refreshed recentered Schur clock -> first global kernel endgame

Phase 75.17 split global coefficient integrality using a closing block retained
from before affine recentering.  The split itself is valid for any supplied
clock, but the next residual-orientation argument requires the Schur clock and
the coefficientwise source blow-up to live on the *same polynomial family*.

`RigidClosingRecenteredSchurClock` rebuilds the exact zero-Schur block on the
recentered family.  This file feeds that refreshed block through the existing
finite-support first-kernel machinery and returns the same strong endgame
alternatives as Phase 75.17, now with exact source/clock provenance.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

namespace CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData

variable [CharZero K]
variable {D complexity : ℕ}
variable {f : CanonicalSmithDepartureFrontier (K := K) D complexity}

/-- A refreshed recentered closing certificate gives the strengthened
first-kernel endgame resolution, with its exact block belonging to the same
recentered family as the coefficientwise kernel blow-up. -/
theorem RecenteredRigidClosingCertificate.toFirstKernelEndgameResolution
    {S : f.RigidClosingExactCollisionSourceData}
    (hclose : RecenteredRigidClosingCertificate S) :
    HasRigidClosingFirstKernelEndgameResolution f := by
  let R := S.recenteredSourceData
  cases hclose with
  | left hD hrigid hpivot hclosing =>
      let B := S.recenteredLeftZeroSchurData hrigid hpivot hD
      have hBdef :
          B.defect = alignedSmithRamificationIndex * f.defect := by
        rfl
      have hout :=
        R.firstClosingKernelStage_terminal_or_residual_or_offender_forBlock
          B hBdef hclosing
      rcases hout with hdirect | hresidual | hoffender
      · exact ⟨R, B, hBdef, Or.inl hdirect⟩
      · exact ⟨R, B, hBdef, Or.inr (Or.inl hresidual)⟩
      · rcases R.firstKernelOffender_zeroSlope_or_strictRestart B hoffender with
          hzero | hrestart
        · exact ⟨R, B, hBdef, Or.inr (Or.inr (Or.inl hzero))⟩
        · exact ⟨R, B, hBdef, Or.inr (Or.inr (Or.inr hrestart))⟩
  | right hD hrigid hpivot hclosing =>
      let B := S.recenteredRightZeroSchurData hrigid hpivot hD
      have hBdef :
          B.defect = alignedSmithRamificationIndex * f.defect := by
        rfl
      have hout :=
        R.firstClosingKernelStage_terminal_or_residual_or_offender_forBlock
          B hBdef hclosing
      rcases hout with hdirect | hresidual | hoffender
      · exact ⟨R, B, hBdef, Or.inl hdirect⟩
      · exact ⟨R, B, hBdef, Or.inr (Or.inl hresidual)⟩
      · rcases R.firstKernelOffender_zeroSlope_or_strictRestart B hoffender with
          hzero | hrestart
        · exact ⟨R, B, hBdef, Or.inr (Or.inr (Or.inl hzero))⟩
        · exact ⟨R, B, hBdef, Or.inr (Or.inr (Or.inr hrestart))⟩

end CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData

/-- **Canonical first-kernel endgame with the Schur clock refreshed after
recentring.**

Every rigid branch now either gives rank-two progress immediately after the
affine change of source coordinates, or enters the Phase 75.17 source-level
endgame with a zero-Schur block computed from that exact recentered family.
No pre-translation/post-translation clock identification remains. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_recenteredFirstKernelEndgameResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      HasRigidClosingFirstKernelEndgameResolution f := by
  rcases f.rankTwoProgress_or_rigidClosingCertificate hD with
    hprogress | hclosing
  · exact Or.inl hprogress
  · let S := f.rigidClosingExactCollisionSourceData hclosing
    rcases S.rankTwoProgress_or_recenteredClosing with
      hprogress | hrefreshed
    · exact Or.inl hprogress
    · exact Or.inr hrefreshed.toFirstKernelEndgameResolution

/-- The genuinely irreducible rigid-closing source alternatives after the
Phase 75.19 restart collapse.  Successful integral first stages no longer
appear here: they have already become strict polynomial-family restarts. -/
def HasRigidClosingRestartOrZeroSlopeResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Prop :=
  ∃ S : f.RigidClosingRecenteredSourceData,
    S.HasRigidClosingZeroCommonKernelSlopeObstruction ∨
      S.HasRigidClosingStrictKernelRestart

/-- Collapse the strengthened first-kernel endgame to its two genuine
source-level alternatives.  Both integral branches use the same positive
first Schur order, hence both are strict restarts by
`integralFirstKernelStage_to_strictRestart`. -/
theorem HasRigidClosingFirstKernelEndgameResolution.toRestartOrZeroSlopeResolution
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (h : HasRigidClosingFirstKernelEndgameResolution f) :
    HasRigidClosingRestartOrZeroSlopeResolution f := by
  rcases h with ⟨S, B, _hBdef, hzero | hresidual | hzeroSlope | hrestart⟩
  · exact ⟨S, Or.inr (S.integralFirstKernelStage_to_strictRestart B hzero.2)⟩
  · exact ⟨S, Or.inr (S.integralFirstKernelStage_to_strictRestart B hresidual.2)⟩
  · exact ⟨S, Or.inl hzeroSlope⟩
  · exact ⟨S, Or.inr hrestart⟩

/-- **Phase 75.19 canonical rigid endgame.**

After refreshing the Schur clock on the recentered source, the rigid branch
has only three live outcomes:

* strict rank-one to rank-two repair progress;
* the anisotropic zero-maximal-slope obstruction in the common kernel; or
* a concrete strict polynomial-family restart.

In particular, neither a zero-residual nor a positive-residual integral
first-kernel branch survives as a separate case. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_recenteredRestartOrZeroSlopeResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      HasRigidClosingRestartOrZeroSlopeResolution f := by
  rcases f.rankTwoProgress_or_recenteredFirstKernelEndgameResolution hD with
    hprogress | hendgame
  · exact Or.inl hprogress
  · exact Or.inr hendgame.toRestartOrZeroSlopeResolution

end

end HC4.Valuation
