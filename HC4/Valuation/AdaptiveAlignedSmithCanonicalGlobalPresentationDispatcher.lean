import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentationComposition
import Mathlib.Tactic

/-!
# A18.4.4: consume one global presentation layer without making it recursive

A18.4.3 supplied the composition algebra needed to absorb a pure ramified
presentation into the next genuine exit.  This file applies that algebra to
the actual A18.4 frontier.

There are two small but important changes.

First, the A18.1 zero-defect re-entry payload is strengthened at its source:
it now remembers the proof `s.rawDefect = 0` from which the Rees re-entry was
constructed.  Earlier files only retained the target clock `6`; that was enough
locally, but not enough to reflect a zero result backwards through a later pure
presentation.

Second, when the A18.4.2 frontier returns `internalPresentation presented`, we
immediately rerun the same rank-one classifier on `presented` and absorb the
second result back to the original source:

* zero defect is reflected back to the source and the source Rees re-entry is
  rebuilt there;
* a ramified strict macro is prefixed by the source presentation;
* a pointed rank-two exit becomes a geometry-carrying strict macro from the
  original source;
* a second pure presentation is composed with the first and remains explicitly
  nonrecursive.

Thus a single presentation layer is no longer exposed to downstream code.  If
the classifier produces two consecutive pure presentations, they are returned
as one composed presentation.  No comparison of raw clocks across different
parameter scales is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A18.4 frontier after immediately consuming one pure-presentation layer.

The pointed constructor is phrased using
`AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress`, so both
direct pointed exits and pointed exits reached after a presentation have one
uniform geometry-carrying strict interface.

The only non-strict constructor left is a *composed* presentation obtained when
both the first and second classifier passes are pure presentations. -/
inductive AdaptiveAlignedSmithCanonicalGlobalPresentationDispatchOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | pointedRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
          RR s complexity))

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A18.4.4 one-layer presentation dispatcher.**

Run the A18.4.2 quarantine frontier.  Direct genuine exits are merely repackaged.
For a pure presentation, rerun the rank-one frontier on the presented state and
use A18.4.3 to compose the result back to the original source.

Crucially, the second `internalPresentation` case is not accepted as progress:
the two zero-cost moves are composed and returned as one zero-cost move. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalPresentationDispatchFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentationDispatchOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalLegacyQuarantineFrontier
      RR complexity hsrepair with
  | zeroDefectReentry D =>
      rcases D with ⟨D⟩
      exact .zeroDefectReentry D.source_rawDefect ⟨D⟩
  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D
  | pointedRankTwoProgress D =>
      rcases D with ⟨D⟩
      exact .pointedRankTwoProgress
        ⟨AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress.ofDirect D⟩
  | internalPresentation presented hsource sourceTrace =>
      have hpresentedRepair :
          presented.repair = rankOneRepairState complexity :=
        hsource.rankOne_repair_eq hsrepair
      cases presented.alignedSmithCanonicalGlobalLegacyQuarantineFrontier
          RR complexity hpresentedRepair with
      | zeroDefectReentry D =>
          rcases D with ⟨D⟩
          have hzero : s.rawDefect = 0 :=
            hsource.source_rawDefect_eq_zero_of_target D.source_rawDefect
          exact .zeroDefectReentry hzero
            (s.exists_globalZeroDefectReentryData hzero)
      | ramifiedStrictMacro D =>
          exact .ramifiedStrictMacro
            (AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro.prepend_internal
              RR hsource D)
      | pointedRankTwoProgress D =>
          rcases D with ⟨D⟩
          exact .pointedRankTwoProgress
            ⟨AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress.ofInternal
              hsource D hsrepair⟩
      | internalPresentation target hmove targetTrace =>
          exact .internalPresentation target (hsource.trans hmove)
            (.trans sourceTrace targetTrace)

end

end HC4.Valuation
