import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectReentry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamificationTermination
import Mathlib.Tactic

/-!
# A17.9: global macro termination for zero-defect re-entry

A17.8 gives the honest way to leave the determinant-one endpoint: a transverse
Rees presentation at the same literal scale whose raw Hessian clock is six.
The presentation itself is not progress for the old fixed-scale key because it
raises the raw clock from zero to six.

For the global macro, however, it is immediately followed by the already
certified finite-repair promotion from rank one to rank two.  This file records
the correct well-founded order for that *composite* move.  Its priority is

    (repair measure, raw defect, source complexity).

Thus an intrinsic repair promotion dominates any temporary raw-clock change
inside the presentation macro.  The relation is a pullback of a finite
lexicographic order on naturals and is therefore genuinely well-founded.

No scale change is admitted.  In particular the theorem below packages the
entire zero-defect Rees re-entry and rank promotion as one same-scale strict
macro from the original state.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Canonical repair ranking exported for final assembly. -/
def canonicalAdaptiveAlignedSmithRepairRanking : RepairRanking where
  rank := RepairState.measure
  progress_lt := by
    intro old new hprogress
    exact repairState_measure_lt_of_progress hprogress

/-- Discrete key used by the final global macro recursion.

Repair measure is outermost because zero-defect Rees re-entry may temporarily
raise the raw determinant clock before the finite repair stage is promoted. -/
abbrev AdaptiveAlignedSmithCanonicalGlobalMacroKey := ℕ × (ℕ × ℕ)

/-- Strict lexicographic order on the final macro key. -/
def AdaptiveAlignedSmithCanonicalGlobalMacroKey.Lt :
    AdaptiveAlignedSmithCanonicalGlobalMacroKey →
      AdaptiveAlignedSmithCanonicalGlobalMacroKey → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)

/-- The final macro-key order is well-founded. -/
theorem AdaptiveAlignedSmithCanonicalGlobalMacroKey.lt_wellFounded :
    WellFounded AdaptiveAlignedSmithCanonicalGlobalMacroKey.Lt := by
  exact
    (Nat.lt_wfRel.wf).prod_lex
      ((Nat.lt_wfRel.wf).prod_lex Nat.lt_wfRel.wf)

/-- Pull the final macro key back to scale-aware restart states. -/
def ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    AdaptiveAlignedSmithCanonicalGlobalMacroKey :=
  (s.repair.measure, (s.rawDefect, s.sourceComplexity))

/-- Strict global macro progress.  Literal scale preservation is kept as a
separate certificate below, exactly as for the fixed-scale episode order. -/
def AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  AdaptiveAlignedSmithCanonicalGlobalMacroKey.Lt
    t.globalMacroKey s.globalMacroKey

/-- Global macro progress is genuinely well-founded. -/
theorem adaptiveAlignedSmithCanonicalGlobalMacroProgress_wellFounded :
    WellFounded
      (AdaptiveAlignedSmithCanonicalGlobalMacroProgress (K := K)) := by
  simpa [AdaptiveAlignedSmithCanonicalGlobalMacroProgress] using
    (AdaptiveAlignedSmithCanonicalGlobalMacroKey.lt_wellFounded.onFun
      (f := ScaleAwareAdaptiveGeometricRestartState.globalMacroKey (K := K)))

/-- Same-scale certificate for one final-assembly macro step. -/
structure CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop where
  sameScale : SameEpisodeScale t s
  progress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress t s

/-- Any intrinsic repair progress gives global macro progress at unchanged
scale, independently of what happened to the raw clock inside the absorbed
presentation macro. -/
theorem certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_repairProgress
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hrepair : RepairProgress s.repair t.repair) :
    CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress t s := by
  refine ⟨hsame, ?_⟩
  unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
  unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
  apply Prod.Lex.left
  exact repairState_measure_lt_of_progress hrepair

/-- With repair metadata unchanged, a strict raw-defect decrease is also a
strict global macro step. -/
theorem certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_rawDefect_lt
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hrepair : t.repair = s.repair)
    (hdefect : t.rawDefect < s.rawDefect) :
    CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress t s := by
  refine ⟨hsame, ?_⟩
  unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
  unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
  rw [hrepair]
  apply Prod.Lex.right
  apply Prod.Lex.left
  exact hdefect

/-- At unchanged repair state and raw defect, source-complexity decrease is
also a strict global macro step. -/
theorem certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_source_lt
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hrepair : t.repair = s.repair)
    (hdefect : t.rawDefect = s.rawDefect)
    (hsource : t.sourceComplexity < s.sourceComplexity) :
    CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress t s := by
  refine ⟨hsame, ?_⟩
  unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
  unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
  rw [hrepair, hdefect]
  apply Prod.Lex.right
  apply Prod.Lex.right
  exact hsource

/-- Rank-one to rank-two promotion is a strict final macro step on any
scale-aware state, with no geometric field changed. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_rankOneToRankTwoGlobalMacroProgress
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      target = s.withRepairOnly (rankTwoRepairState complexity) ∧
      CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
  let target := s.withRepairOnly (rankTwoRepairState complexity)
  refine ⟨target, rfl, ?_⟩
  apply certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_repairProgress
  · rfl
  · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
      hsrepair] using rankOne_to_rankTwo_repairProgress complexity

/-- Rank-two to rank-three promotion is likewise a strict final macro step. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_rankTwoToRankThreeGlobalMacroProgress
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankTwoRepairState complexity) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      target = s.withRepairOnly (rankThreeRepairState complexity) ∧
      CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
  let target := s.withRepairOnly (rankThreeRepairState complexity)
  refine ⟨target, rfl, ?_⟩
  apply certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_repairProgress
  · rfl
  · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
      hsrepair] using rankTwo_to_rankThree_repairProgress complexity

/-- At rank three, dropping positive complexity and resetting to canonical
rank one is still intrinsic repair progress.  This is the discrete restart
edge used after finite-rank exhaustion. -/
theorem rankThreeSucc_to_rankOne_repairProgress
    (complexity : ℕ) :
    RepairProgress
      (rankThreeRepairState (complexity + 1))
      (rankOneRepairState complexity) := by
  left
  change complexity < complexity + 1
  omega

/-- State-level form of the rank-three complexity drop. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_rankThreeSuccToRankOneGlobalMacroProgress
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankThreeRepairState (complexity + 1)) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      target = s.withRepairOnly (rankOneRepairState complexity) ∧
      CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
  let target := s.withRepairOnly (rankOneRepairState complexity)
  refine ⟨target, rfl, ?_⟩
  apply certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_repairProgress
  · rfl
  · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
      hsrepair] using rankThreeSucc_to_rankOne_repairProgress complexity

/-- **A17.9 zero-reentry macro termination.**

Absorb the canonical A17.8 transverse Rees presentation into an immediate
rank-one-to-rank-two promotion.  Although the intermediate state has raw
defect six while the source has raw defect zero, the composite target is
strictly smaller in the global macro order because the certified repair
measure decreases first.

The theorem retains the intermediate state explicitly so final assembly may
recover the exact A17.8 geometric presentation if needed, while recursion is
allowed only on the strict `target`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_zeroDefectReentryThenRankTwoGlobalMacroProgress
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hzero : s.rawDefect = 0) :
    ∃ reentry target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      reentry.rawDefect = 6 ∧
      reentry.scale = s.scale ∧
      reentry.degreeCap = s.degreeCap ∧
      reentry.sourceComplexity = s.sourceComplexity ∧
      reentry.repair = rankOneRepairState complexity ∧
      target = reentry.withRepairOnly (rankTwoRepairState complexity) ∧
      CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
  rcases s.exists_zeroDefectTransverseReentry hzero with
    ⟨reentry, hraw, hscale, hdegreeCap, hsourceComplexity, hrepair, _hpositive⟩
  let target := reentry.withRepairOnly (rankTwoRepairState complexity)
  refine ⟨reentry, target, hraw, hscale, hdegreeCap, hsourceComplexity, ?_, rfl, ?_⟩
  · exact hrepair.trans hsrepair
  · apply certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_repairProgress
    · simpa [SameEpisodeScale, target] using hscale
    · simpa [target, hsrepair] using
        rankOne_to_rankTwo_repairProgress complexity

/-- Global-facing A17.9 frontier.  The former `zeroDefect` / `positiveReentry`
case no longer survives as a recursive alternative: both zero and nonzero
rank-one inputs admit one certified strict macro successor at the incoming
literal scale. -/
inductive AdaptiveAlignedSmithCanonicalGlobalMacroOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | strictProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hprogress :
        CertifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress target s)

/-- **Penultimate global frontier.**

At canonical rank one, inspect the A17.7 terminal condition only to preserve
the honest zero-defect Rees construction.  The zero branch is absorbed into
the A17.9 composite macro; every other branch uses the direct certified
rank-one-to-rank-two step.  Hence the exported interface has one constructor:
well-founded same-scale global macro progress. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalMacroFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalMacroOutcome s complexity := by
  cases s.alignedSmithCanonicalRamificationTerminatedFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      rcases s.exists_zeroDefectReentryThenRankTwoGlobalMacroProgress
          complexity hsrepair hzero with
        ⟨reentry, target, hraw, hscale, hdegreeCap, hsourceComplexity,
          hrepair, htarget, hprogress⟩
      exact .strictProgress target hprogress
  | strictProgress target hprogress =>
      rcases s.exists_rankOneToRankTwoGlobalMacroProgress complexity hsrepair with
        ⟨target', htarget', hprogress'⟩
      exact .strictProgress target' hprogress'

/-- Concrete final-assembly form using the canonical numerical repair measure. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalMacroFrontier_concrete
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalMacroOutcome s complexity := by
  exact s.alignedSmithCanonicalGlobalMacroFrontier
    canonicalAdaptiveAlignedSmithRepairRanking complexity hsrepair

end

end HC4.Valuation
