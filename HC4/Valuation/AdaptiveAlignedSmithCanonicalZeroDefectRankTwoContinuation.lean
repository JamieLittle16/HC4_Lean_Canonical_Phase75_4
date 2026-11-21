import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesGlobalDescent
import Mathlib.Tactic

/-!
# Geometry-retaining continuation of the zero-defect rank-two promotion

A18.4.40 and A19.53 now give the final zero-clock strict-low branch an honest
rank-two successor backed by a literal nonzero transverse Hessian minor.  The
finite repair engine already contains the certified rank-two to rank-three
step, but using that step naked would erase the geometric reason why rank two
was reached.

This module keeps the A18.4.40 witness as data while performing the existing
rank-two to rank-three repair step.  It therefore supplies the missing
geometry-bearing adapter needed by the outer finite-repair/global recursion;
no new termination measure and no repair-only contradiction are introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The zero-defect source, its literal rank-two Hessian witness, the certified
rank-two state, and one certified rank-three continuation, all retained in one
package. -/
structure AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankThreeProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  rankTwo : AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankTwoProgress
    RR source complexity
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = rankTwo.target.withRepairOnly (rankThreeRepairState complexity)
  rankTwoToRankThree :
    CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress
      target rankTwo.target
  globalProgress_from_source :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- Advance the geometry-backed zero-defect rank-two state through the
existing finite-rank ladder without discarding the Hessian witness. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankTwoProgress.toRankThreeProgress
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankTwoProgress
      RR source complexity) :
    AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankThreeProgress
      RR source complexity := by
  have hrepair : P.target.repair = rankTwoRepairState complexity := by
    rw [P.target_eq]
    rfl
  rcases P.target.exists_rankTwoToRankThreeGlobalMacroProgress
      complexity hrepair with
    ⟨target, htarget, hprogress⟩
  refine {
    rankTwo := P
    target := target
    target_eq := htarget
    rankTwoToRankThree := hprogress
    globalProgress_from_source := ?_
  }
  exact adaptiveAlignedSmithCanonicalGlobalMacroProgress_trans
    hprogress.progress P.globalProgress

/-- Direct zero-defect source-facing form.  The returned rank-three package
still contains the literal transverse Hessian minor through `rankTwo.geometry`.
-/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.zeroDefect_globalRankThreeProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hzero : source.rawDefect = 0) :
    AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankThreeProgress
      RR source complexity :=
  (source.zeroDefect_globalRankTwoProgress RR complexity hsrepair hzero).toRankThreeProgress

end

end HC4.Valuation
