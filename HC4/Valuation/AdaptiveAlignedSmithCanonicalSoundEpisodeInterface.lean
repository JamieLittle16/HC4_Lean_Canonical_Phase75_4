import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryEliminationInterface
import HC4.Valuation.CertifiedFixedScaleRestartEpisodeProgress
import Mathlib.Tactic

/-!
# Sound fixed-scale exit interface for the canonical stationary endgame

The earlier canonical episode layers deliberately kept two kinds of output
separate:

* a strict decrease of the fixed-scale episode key;
* a coordinate/exposure re-entry which still required macro bookkeeping.

For final well-founded recursion we must retain one further datum explicitly:
a strict episode-key decrease is a *fixed-scale* recursive exit only when the
source and target are measured at the same literal parameter scale.

This file therefore packages

    same scale + strict episode-key decrease

as one certificate.  It also proves the basic macro-composition rule needed by
the endgame: a zero-cost internal presentation change followed by a certified
strict exit is a certified strict exit from the original presentation.

No scale-changing re-entry is called recursive progress here.  In particular,
this file intentionally does not use the weak `reentry` constructor of
`AdaptiveAlignedSmithCanonicalResolvedOutcome` as a termination argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- A genuinely certified fixed-scale recursive exit.

Unlike the older proposition `CertifiedFixedScaleEpisodeProgress`, this
structure retains the same-scale proof instead of discarding it after the
raw-defect/repair/source comparison has been established. -/
structure CertifiedSameScaleEpisodeProgress
    (R : RepairRanking)
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop where
  sameScale : SameEpisodeScale t s
  progress : CertifiedFixedScaleEpisodeProgress R t s

/-- Strict raw-defect decrease at unchanged scale gives the strengthened
certificate directly. -/
theorem certifiedSameScaleEpisodeProgress_of_rawDefect_lt
    (R : RepairRanking)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect < s.rawDefect) :
    CertifiedSameScaleEpisodeProgress R t s := by
  exact ⟨hsame,
    certifiedFixedScaleEpisodeProgress_of_rawDefect_lt
      (K := K) R hsame hdef⟩

/-- Intrinsic repair progress at unchanged scale and raw defect gives the
strengthened certificate. -/
theorem certifiedSameScaleEpisodeProgress_of_repairProgress
    (R : RepairRanking)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair : RepairProgress s.repair t.repair) :
    CertifiedSameScaleEpisodeProgress R t s := by
  exact ⟨hsame,
    certifiedFixedScaleEpisodeProgress_of_repairProgress
      (K := K) R hsame hdef hrepair⟩

/-- Source-complexity descent at unchanged higher coordinates gives the
strengthened certificate. -/
theorem certifiedSameScaleEpisodeProgress_of_source_lt
    (R : RepairRanking)
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsame : SameEpisodeScale t s)
    (hdef : t.rawDefect = s.rawDefect)
    (hrepair : R.rank t.repair = R.rank s.repair)
    (hsource : t.sourceComplexity < s.sourceComplexity) :
    CertifiedSameScaleEpisodeProgress R t s := by
  exact ⟨hsame,
    certifiedFixedScaleEpisodeProgress_of_source_lt
      (K := K) R hsame hdef hrepair hsource⟩

/-- **Zero-cost macro composition.**

If `u` is only an internal fixed-scale re-presentation of `s`, then any
same-scale strict exit from `u` is already a same-scale strict exit from `s`.
This is the exact rule needed to absorb harmless coordinate normalisations
before invoking well-founded recursion. -/
theorem FixedScaleEpisodeInternalMove.then_certifiedSameScaleProgress
    (R : RepairRanking)
    {s u t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : FixedScaleEpisodeInternalMove R.rank u s)
    (hprogress : CertifiedSameScaleEpisodeProgress R t u) :
    CertifiedSameScaleEpisodeProgress R t s := by
  refine ⟨?_, ?_⟩
  · exact Eq.trans hprogress.sameScale hmove.1
  · change FixedScaleEpisodeKey.Lt
      (t.fixedScaleEpisodeKey R.rank)
      (s.fixedScaleEpisodeKey R.rank)
    rw [← hmove.2]
    exact hprogress.progress

/-- Internal moves compose transitively. -/
theorem FixedScaleEpisodeInternalMove.trans
    (R : RepairRanking)
    {s u t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (htu : FixedScaleEpisodeInternalMove R.rank t u)
    (hus : FixedScaleEpisodeInternalMove R.rank u s) :
    FixedScaleEpisodeInternalMove R.rank t s := by
  refine ⟨?_, ?_⟩
  · exact Eq.trans htu.1 hus.1
  · exact Eq.trans htu.2 hus.2

/-- Honest local exit target for the stationary theorem.

`strict` is recursive progress *from the actual incoming state*.
`internal` is explicitly not recursive progress; it is a zero-cost
presentation which must be consumed by a later strict exit in the same macro
step.  `zeroDefect` is terminal only on the incoming state itself.

There is deliberately no arbitrary `reentry t` constructor.  A scale-changing
re-entry remains a separate global bookkeeping obligation until it is supplied
with its own certified macro measure. -/
inductive AdaptiveAlignedSmithCanonicalHonestLocalExit
    (R : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | strict
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : CertifiedSameScaleEpisodeProgress R target s)

  | internal
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : FixedScaleEpisodeInternalMove R.rank target s)

  | zeroDefect
      (hzero : s.rawDefect = 0)

/-- The non-vacuous stationary elimination target.

Unlike the earlier architecture-only interface, this cannot be discharged by
returning an unrelated strict transition or an arbitrary adaptive state. -/
def AdaptiveAlignedSmithCanonicalStationarySoundElimination
    (R : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  ∀ P : AdaptiveAlignedSmithCanonicalStationaryLocalProblem s,
    AdaptiveAlignedSmithCanonicalHonestLocalExit R s

/-- A stationary eliminator which returns an internal presentation can be
closed as soon as that presentation admits one certified same-scale strict
exit.  This theorem is the intended local macro rule for the remaining
first-departure geometry. -/
theorem stationarySoundElimination_of_internal_then_strict
    (R : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hlocal :
      ∀ P : AdaptiveAlignedSmithCanonicalStationaryLocalProblem s,
        ∃ u t : ScaleAwareAdaptiveGeometricRestartState (K := K),
          FixedScaleEpisodeInternalMove R.rank u s ∧
          CertifiedSameScaleEpisodeProgress R t u) :
    AdaptiveAlignedSmithCanonicalStationarySoundElimination R s := by
  intro P
  rcases hlocal P with ⟨u, t, hu, ht⟩
  exact .strict t
    (FixedScaleEpisodeInternalMove.then_certifiedSameScaleProgress
      (K := K) R hu ht)

end

end HC4.Valuation
