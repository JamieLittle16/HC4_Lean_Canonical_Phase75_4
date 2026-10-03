import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentationFreeExactClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamifiedStrictReason
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveSlopeKernelFree
import Mathlib.Tactic

/-!
# A18.4.42: collapse the presentation-free frontier to termination reasons

A18.4.38 leaves seven presentation-free exact-clock constructors.  By A18.4.40,
the zero-clock branch and all four geometry-carrying rank-two branches already
carry honest global macro progress.  A ramified strict macro can likewise be
classified as either scale-insensitive outer-key progress or a genuine
ramified raw-defect spend.

This file performs that lossless collapse.  It deliberately does **not** call a
bare ramified spend recursive progress: arbitrary rational-scale descent is
not well founded.  Consequently the only unresolved constructor is the exact
cross-scale spend whose geometric provenance must be consumed by the
first-contact/rank ladder.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The three logically distinct outputs relevant to the final nested
termination argument.

* `globalProgress` is an already-certified step in the old discrete global
  macro key;
* `outerProgress` decreases the scale-insensitive `(repair, source)` key;
* `ramifiedSpend` is retained without pretending that rational-scale descent
  is itself well founded.
-/
inductive AdaptiveAlignedSmithCanonicalGlobalTerminationFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | globalProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s)
  | outerProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalOuterKey.Lt
        (target.canonicalOuterKey RR) (s.canonicalOuterKey RR))
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

/-- **Presentation-free final termination frontier.**

Every geometry-backed constructor of A18.4.38 is now consumed.  The only case
which is not already discrete well-founded progress is a genuine ramified raw
spend; that case is intentionally retained for the first-contact geometry
rather than being recursively iterated as a rational decrease.
-/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalTerminationFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalTerminationFrontier RR s := by
  cases s.alignedSmithCanonicalPresentationFreeExactClockFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      let D :=
        ScaleAwareAdaptiveGeometricRestartState.zeroDefect_globalRankTwoProgress
          RR s complexity hsrepair hzero
      exact .globalProgress D.target D.globalProgress

  | ramifiedSpend target h =>
      exact .ramifiedSpend target h

  | stationaryRankTwoProgress D =>
      rcases D with ⟨D⟩
      exact .globalProgress D.target D.globalProgress

  | earlySchurRankTwoProgress D =>
      rcases D with ⟨D⟩
      exact .globalProgress D.target D.globalProgress

  | residualRankTwoProgress D =>
      rcases D with ⟨D⟩
      exact .globalProgress D.target D.globalProgress

  | zeroSchurRankTwoProgress D =>
      rcases D with ⟨D⟩
      exact .globalProgress D.target D.globalProgress

  | ramifiedStrictMacro D =>
      cases D.reason RR with
      | outerProgress target h =>
          exact .outerProgress target h
      | rawSpend target h =>
          exact .ramifiedSpend target h

end

end HC4.Valuation
