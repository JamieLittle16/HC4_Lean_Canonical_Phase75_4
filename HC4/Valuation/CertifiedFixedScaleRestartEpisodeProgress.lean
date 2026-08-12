import HC4.Valuation.FixedScaleRestartEpisodeOrder
import HC4.Valuation.AdaptiveGeometricRestartState
import Mathlib.Tactic

/-!
# Certified fixed-scale restart episode progress

The global fixed-scale order intentionally accepts an arbitrary numerical
ranking of `RepairState`.  We package exactly the property needed from such a
ranking instead of depending on a non-exported implementation detail of the
Newton repair module.

A `RepairRanking` consists of

* a natural-valued rank on `RepairState`;
* a proof that every intrinsic `RepairProgress old new` strictly lowers it.

Once such a ranking is supplied, the pulled-back episode order is
well-founded, and every geometry-carrying `AdaptiveRankTwoContinuation`
becomes a genuine strict successor.

This file therefore completes the geometry -> well-founded-order bridge
without guessing the name or namespace of the Newton module's private repair
measure.  The later integration layer only has to instantiate `RepairRanking`
once from whichever concrete repair measure the canonical tree exports.

No ramification-scale change is counted as progress here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The exact interface the global episode order needs from finite repair
bookkeeping. -/
structure RepairRanking where
  rank : RepairState → ℕ
  progress_lt :
    ∀ {old new : RepairState},
      RepairProgress old new →
        rank new < rank old

/-- Fixed-scale episode progress attached to a certified repair ranking. -/
abbrev CertifiedFixedScaleEpisodeProgress
    (R : RepairRanking)
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  FixedScaleEpisodeProgress R.rank t s

/-- Every certified fixed-scale episode relation is well-founded. -/
theorem certifiedFixedScaleEpisodeProgress_wellFounded
    (R : RepairRanking) :
    WellFounded
      (CertifiedFixedScaleEpisodeProgress (K := K) R) := by
  exact
    fixedScaleEpisodeProgress_wellFounded
      (K := K) R.rank

/-- Intrinsic repair progress at unchanged scale and raw defect gives strict
episode progress for every certified repair ranking. -/
theorem certifiedFixedScaleEpisodeProgress_of_repairProgress
    (R : RepairRanking)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair : RepairProgress s.repair t.repair) :
    CertifiedFixedScaleEpisodeProgress R t s := by
  apply
    fixedScaleEpisodeProgress_of_repair_lt
      (K := K) R.rank hsame hdef
  exact R.progress_lt hrepair

/-- Strict raw integer defect drop at unchanged scale is certified episode
progress, independently of repair and source coordinates. -/
theorem certifiedFixedScaleEpisodeProgress_of_rawDefect_lt
    (R : RepairRanking)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect < s.rawDefect) :
    CertifiedFixedScaleEpisodeProgress R t s := by
  exact
    fixedScaleEpisodeProgress_of_rawDefect_lt
      (K := K) R.rank hsame hdef

/-- At unchanged scale and raw defect, if the certified repair rank is also
unchanged then a strict source-complexity drop gives episode progress. -/
theorem certifiedFixedScaleEpisodeProgress_of_source_lt
    (R : RepairRanking)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair : R.rank t.repair = R.rank s.repair)
    (hsource : t.sourceComplexity < s.sourceComplexity) :
    CertifiedFixedScaleEpisodeProgress R t s := by
  exact
    fixedScaleEpisodeProgress_of_source_lt
      (K := K) R.rank
      hsame hdef hrepair hsource

/-! ## First actual geometry-carrying strict successor -/

/-- A geometry-carrying rank-two continuation is a strict successor in every
certified fixed-scale episode order.

Both states are viewed at scale `1`; the continuation preserves the entire
determinant-clock family and all geometric fields and changes only the finite
repair coordinate. -/
theorem AdaptiveRankTwoContinuation.certifiedFixedScaleProgress
    (R : RepairRanking)
    {s : AdaptiveGeometricRestartState (K := K)}
    {D complexity : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (h : AdaptiveRankTwoContinuation s D complexity Q) :
    CertifiedFixedScaleEpisodeProgress R
      h.successor.toScaleAware
      s.toScaleAware := by
  apply
    certifiedFixedScaleEpisodeProgress_of_repairProgress
      (K := K) R
  · rfl
  · rfl
  · simpa [
      AdaptiveRankTwoContinuation.successor,
      AdaptiveGeometricRestartState.toScaleAware,
      AdaptiveGeometricRestartState.withRepair
    ] using h.repairProgress

end

end HC4.Valuation
