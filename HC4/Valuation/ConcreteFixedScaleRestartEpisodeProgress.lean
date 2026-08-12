import HC4.Valuation.FixedScaleRestartEpisodeOrder
import HC4.Valuation.AdaptiveGeometricRestartState
import Mathlib.Tactic

/-!
# Concrete fixed-scale episode progress

`FixedScaleRestartEpisodeOrder` deliberately left the numerical ranking of
`RepairState` abstract.  The Newton repair layer already supplies the
canonical natural-valued measure `repairState_measure`, together with the
strictness theorem

    repairState_measure_lt_of_progress :
      RepairProgress old new ->
        repairState_measure new < repairState_measure old.

This file instantiates the abstract episode order with that existing measure.

The second purpose of the file is more important geometrically: an
`AdaptiveRankTwoContinuation` keeps the determinant-clock family unchanged
and changes only the finite repair coordinate.  Its stored `RepairProgress`
therefore gives an actual strict successor for the concrete well-founded
episode relation after passing both states to the unramified scale-aware
view.

This is the first direct bridge from a geometry-carrying adaptive
continuation to the global well-founded relation.

Nothing here treats a change of ramification scale as progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Concrete order -/

/-- The actual fixed-scale episode relation, using the repository's existing
finite repair-state measure. -/
abbrev ConcreteFixedScaleEpisodeProgress
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  FixedScaleEpisodeProgress repairState_measure t s

/-- The concrete relation is well-founded. -/
theorem concreteFixedScaleEpisodeProgress_wellFounded :
    WellFounded
      (ConcreteFixedScaleEpisodeProgress (K := K)) := by
  exact
    fixedScaleEpisodeProgress_wellFounded
      (K := K) repairState_measure

/-- Any intrinsic `RepairProgress` at unchanged scale and unchanged raw
determinant defect is strict concrete episode progress. -/
theorem concreteFixedScaleEpisodeProgress_of_repairProgress
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair : RepairProgress s.repair t.repair) :
    ConcreteFixedScaleEpisodeProgress t s := by
  apply
    fixedScaleEpisodeProgress_of_repair_lt
      (K := K) repairState_measure hsame hdef
  exact repairState_measure_lt_of_progress hrepair

/-- Strict raw integer defect drop at unchanged scale is concrete episode
progress, independently of the lower coordinates. -/
theorem concreteFixedScaleEpisodeProgress_of_rawDefect_lt
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect < s.rawDefect) :
    ConcreteFixedScaleEpisodeProgress t s := by
  exact
    fixedScaleEpisodeProgress_of_rawDefect_lt
      (K := K) repairState_measure hsame hdef

/-- At unchanged scale, defect and repair measure, source-complexity descent
is concrete episode progress. -/
theorem concreteFixedScaleEpisodeProgress_of_source_lt
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair :
      repairState_measure t.repair =
        repairState_measure s.repair)
    (hsource : t.sourceComplexity < s.sourceComplexity) :
    ConcreteFixedScaleEpisodeProgress t s := by
  exact
    fixedScaleEpisodeProgress_of_source_lt
      (K := K) repairState_measure
      hsame hdef hrepair hsource

/-! ## First geometry-carrying strict successor -/

/-- A rank-two adaptive continuation is a strict successor in the concrete
episode order.

Both states are viewed on scale `1`.  The successor keeps the same
determinant-clock family, defect, degree cap, source complexity, moving
collision and pointed section; only the repair coordinate changes.  The
strict inequality is exactly the intrinsic `RepairProgress` stored in the
continuation.
-/
theorem AdaptiveRankTwoContinuation.concreteFixedScaleProgress
    {s : AdaptiveGeometricRestartState (K := K)}
    {D complexity : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (h : AdaptiveRankTwoContinuation s D complexity Q) :
    ConcreteFixedScaleEpisodeProgress
      h.successor.toScaleAware
      s.toScaleAware := by
  apply concreteFixedScaleEpisodeProgress_of_repairProgress
  · rfl
  · rfl
  · simpa [
      AdaptiveRankTwoContinuation.successor,
      AdaptiveGeometricRestartState.toScaleAware,
      AdaptiveGeometricRestartState.withRepair
    ] using h.repairProgress

end

end HC4.Valuation
