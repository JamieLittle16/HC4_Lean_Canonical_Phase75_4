import HC4.Valuation.AdaptiveAlignedSmithCanonicalAlignedRankThreeOrProgress
import Mathlib.Tactic

/-!
# A18.4.109: well-founded rank-one termination trace

A18.4.108 strengthens the one-episode theorem so that its only recursive
constructor is an honest canonical rank-one restart:

* the natural raw Hessian defect strictly decreases; and
* the repair state is unchanged.

Therefore no global rational clock and no semantic repair promotion are needed
for the final rank-one recursion.  Ordinary well-founded recursion on
`rawDefect : ℕ` suffices.

The object below deliberately retains the whole finite restart trace.  Every
recursive edge stores its actual target and strict global-macro certificate;
the final node stores the complete rank-three geometry on the terminal state.
This is stronger than a bare existence theorem and leaves enough provenance
for the final collision/classification splice.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A finite, fully certified chain from a canonical rank-one state to complete
rank-three geometry. -/
inductive AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
    (RR : RepairRanking)
    (complexity : ℕ) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) → Type (u + 1)
  | terminal
      {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        RR source complexity) :
      AdaptiveAlignedSmithCanonicalRankOneTerminationTrace RR complexity source
  | restart
      {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (progress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source)
      (rawDefect_lt : target.rawDefect < source.rawDefect)
      (repair_eq : target.repair = source.repair)
      (tail : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
        RR complexity target) :
      AdaptiveAlignedSmithCanonicalRankOneTerminationTrace RR complexity source

/-- **Global rank-one termination.**

Every canonical rank-one collision state reaches complete rank-three geometry
after finitely many honest raw-defect descents.  The recursive call is made
only after the local theorem has proved both strict natural defect decrease and
preservation of the canonical rank-one repair state. -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.rankOneTerminationTrace
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source := by
  cases source.alignedSmithCanonicalRankThreeOrProgress
      RR complexity hsrepair with
  | rankThree geometry =>
      exact .terminal geometry
  | globalProgress target progress rawDefect_lt repair_eq =>
      have htargetRepair : target.repair = rankOneRepairState complexity :=
        repair_eq.trans hsrepair
      exact .restart progress rawDefect_lt repair_eq
        (target.rankOneTerminationTrace RR complexity htargetRepair)
termination_by source.rawDefect

decreasing_by
  exact rawDefect_lt

/-- Terminal state and complete rank-three geometry extracted from the finite
trace. -/
structure AdaptiveAlignedSmithCanonicalReachedRankThree
    (RR : RepairRanking)
    (complexity : ℕ) : Type (u + 1) where
  state : ScaleAwareAdaptiveGeometricRestartState (K := K)
  geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
    RR state complexity

/-- Forget only the intermediate nodes and retain the actual terminal state
with its geometry. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedRankThree
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    AdaptiveAlignedSmithCanonicalReachedRankThree
      (K := K) RR complexity := by
  induction T with
  | terminal geometry =>
      exact ⟨_, geometry⟩
  | restart progress rawDefect_lt repair_eq tail ih =>
      exact ih

/-- Existential-facing corollary of the lossless trace theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_reachedRankThree
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    Nonempty (AdaptiveAlignedSmithCanonicalReachedRankThree
      (K := K) RR complexity) := by
  exact ⟨(source.rankOneTerminationTrace RR complexity hsrepair).reachedRankThree⟩

end

end HC4.Valuation
