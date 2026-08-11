import HC4.Valuation.AdaptiveAlignedSmithPacketExpandedDispatcher
import Mathlib.Order.RelClasses
import Mathlib.Tactic

/-!
# Fixed-scale restart episode order

The quotient clock `rawDefect / scale` is not compositional under arbitrary
successive ramifications.  The safe outer architecture is therefore to
separate:

* **internal episode moves**, which keep one parameter scale fixed; from
* **outer recursive exits**, which occur only after a genuinely discrete
  coordinate has decreased.

At a fixed scale the determinant clock is an actual natural number:
`rawDefect`.  Positive kernel/Smith spends strictly lower that integer.
Rank promotion can lower a finite repair coordinate without changing the
family clock, and residual/blocker descent can lower a finite source
complexity coordinate.

This file defines the lexicographic well-founded skeleton

    (rawDefect, repairRank, sourceComplexity)

for scale-aware adaptive states.

`repairRank` is deliberately supplied as a parameter.  The local code already
carries `RepairProgress`; a later adapter will instantiate this function with
the repository's concrete repair measure.  Keeping that interface abstract
here prevents the global order from depending on an accidental encoding of
`RepairState`.

No claim is made that an arbitrary transition between scale-aware states is
an episode step.  In particular, changing `scale` is *not* silently admitted
as progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Three discrete coordinates used inside one fixed-ramification episode.

The nesting is chosen so that ordinary `Prod.Lex` gives priority

1. raw determinant defect;
2. repair rank;
3. source/residual complexity.
-/
abbrev FixedScaleEpisodeKey := ℕ × (ℕ × ℕ)

/-- Strict lexicographic order on fixed-scale episode keys. -/
def FixedScaleEpisodeKey.Lt :
    FixedScaleEpisodeKey → FixedScaleEpisodeKey → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)

/-- The fixed-scale episode key order is genuinely well-founded. -/
theorem FixedScaleEpisodeKey.lt_wellFounded :
    WellFounded FixedScaleEpisodeKey.Lt := by
  exact
    (Nat.lt_wfRel.wf).prod_lex
      ((Nat.lt_wfRel.wf).prod_lex Nat.lt_wfRel.wf)

/-- Strict raw-defect drop dominates all lower coordinates. -/
theorem FixedScaleEpisodeKey.lt_of_defect_lt
    {d₁ d₂ r₁ r₂ c₁ c₂ : ℕ}
    (h : d₁ < d₂) :
    FixedScaleEpisodeKey.Lt
      (d₁, (r₁, c₁)) (d₂, (r₂, c₂)) := by
  exact Prod.Lex.left _ _ h

/-- At equal raw defect, strict repair-rank drop is progress regardless of
source complexity. -/
theorem FixedScaleEpisodeKey.lt_of_repair_lt
    {d r₁ r₂ c₁ c₂ : ℕ}
    (h : r₁ < r₂) :
    FixedScaleEpisodeKey.Lt
      (d, (r₁, c₁)) (d, (r₂, c₂)) := by
  apply Prod.Lex.right d
  exact Prod.Lex.left _ _ h

/-- At equal raw defect and equal repair rank, strict source-complexity drop
is progress. -/
theorem FixedScaleEpisodeKey.lt_of_source_lt
    {d r c₁ c₂ : ℕ}
    (h : c₁ < c₂) :
    FixedScaleEpisodeKey.Lt
      (d, (r, c₁)) (d, (r, c₂)) := by
  apply Prod.Lex.right d
  apply Prod.Lex.right r
  exact h

/-! ## Pullback to scale-aware adaptive states -/

/-- Episode key of a scale-aware adaptive state for a chosen numerical
ranking of the finite repair bookkeeping. -/
def ScaleAwareAdaptiveGeometricRestartState.fixedScaleEpisodeKey
    (repairRank : RepairState → ℕ)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    FixedScaleEpisodeKey :=
  (s.rawDefect, (repairRank s.repair, s.sourceComplexity))

/-- Strict episode progress between scale-aware adaptive states.

Crucially, this relation itself compares only the three discrete episode
coordinates.  The separate `SameEpisodeScale` hypothesis below is what
certifies that a concrete geometric transition is allowed to use it.
-/
def FixedScaleEpisodeProgress
    (repairRank : RepairState → ℕ)
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  FixedScaleEpisodeKey.Lt
    (t.fixedScaleEpisodeKey repairRank)
    (s.fixedScaleEpisodeKey repairRank)

/-- For any numerical repair ranking, the pulled-back episode progress
relation is well-founded. -/
theorem fixedScaleEpisodeProgress_wellFounded
    (repairRank : RepairState → ℕ) :
    WellFounded
      (FixedScaleEpisodeProgress (K := K) repairRank) := by
  simpa [FixedScaleEpisodeProgress] using
    (FixedScaleEpisodeKey.lt_wellFounded.onFun
      (f :=
        ScaleAwareAdaptiveGeometricRestartState.fixedScaleEpisodeKey
          (K := K) repairRank))

/-- Two states lie in the same fixed-ramification episode only when their
parameter scale is literally unchanged. -/
def SameEpisodeScale
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  t.scale = s.scale

/-- A strict raw integer defect drop at the same scale is a certified episode
successor. -/
theorem fixedScaleEpisodeProgress_of_rawDefect_lt
    (repairRank : RepairState → ℕ)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (_hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect < s.rawDefect) :
    FixedScaleEpisodeProgress repairRank t s := by
  apply FixedScaleEpisodeKey.lt_of_defect_lt
  exact hdef

/-- At the same scale and raw defect, strict repair-rank decrease is a
certified episode successor. -/
theorem fixedScaleEpisodeProgress_of_repair_lt
    (repairRank : RepairState → ℕ)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (_hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair : repairRank t.repair < repairRank s.repair) :
    FixedScaleEpisodeProgress repairRank t s := by
  unfold FixedScaleEpisodeProgress
  simp only [ScaleAwareAdaptiveGeometricRestartState.fixedScaleEpisodeKey]
  rw [hdef]
  exact FixedScaleEpisodeKey.lt_of_repair_lt hrepair

/-- At the same scale, raw defect and repair rank, strict source-complexity
decrease is a certified episode successor. -/
theorem fixedScaleEpisodeProgress_of_source_lt
    (repairRank : RepairState → ℕ)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (_hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair : repairRank t.repair = repairRank s.repair)
    (hsource : t.sourceComplexity < s.sourceComplexity) :
    FixedScaleEpisodeProgress repairRank t s := by
  unfold FixedScaleEpisodeProgress
  simp only [ScaleAwareAdaptiveGeometricRestartState.fixedScaleEpisodeKey]
  rw [hdef, hrepair]
  exact FixedScaleEpisodeKey.lt_of_source_lt hsource

/-! ## Internal moves versus recursive exits -/

/-- A zero-cost coordinate normalisation inside an episode.  Such a move is
*not* recursive progress; it is intended to be absorbed into a macro-step
before applying the well-founded induction hypothesis. -/
def FixedScaleEpisodeInternalMove
    (repairRank : RepairState → ℕ)
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  SameEpisodeScale t s ∧
    t.fixedScaleEpisodeKey repairRank =
      s.fixedScaleEpisodeKey repairRank

/-- Internal moves preserve every component of the episode key. -/
theorem FixedScaleEpisodeInternalMove.key_eq
    (repairRank : RepairState → ℕ)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : FixedScaleEpisodeInternalMove repairRank t s) :
    t.fixedScaleEpisodeKey repairRank =
      s.fixedScaleEpisodeKey repairRank :=
  h.2

end

end HC4.Valuation
