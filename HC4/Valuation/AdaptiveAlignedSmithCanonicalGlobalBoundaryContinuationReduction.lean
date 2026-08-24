import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalResidualPresentationHeadNormalization
import Mathlib.Tactic

/-!
# A18.4.14: compose the global frontier through one boundary presentation

A18.4.13 leaves two source-honest non-strict residues: genuine boundary
presentations and the quarantined legacy rank-two head.  A boundary is a pure
ramified presentation, not recursive progress, so it must not itself be used
as a well-founded edge.

The correct operation is to continue the already-green global classifier on
the presented state and absorb any genuine exit back through the boundary.
This file performs exactly that one-step composition.

Consequently a boundary presentation can survive this pass only when its next
global outcome is itself another boundary presentation, or when the next
unresolved origin is the legacy rank-two head.  Zero defect, a ramified strict
macro, and pointed rank-two progress are all propagated back to the original
source without recursing on the presentation state.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Prefixing an already-composed pointed exit -/

namespace AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress

/-- Prefix another pure ramified presentation to an already-composed pointed
rank-two exit.

The final target is unchanged.  Strictness is again supplied only by the
geometry-justified rank-one to rank-two promotion carried by the pointed
family, while all preceding presentations are composed as zero-cost
provenance. -/
noncomputable def prepend_internal
    {RR : RepairRanking}
    {source presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (hsource : HasCertifiedRamifiedEpisodeInternalMove presented source)
    (D : AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
      RR presented complexity)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
      RR source complexity := by
  have htargetRepair :
      D.pointedProgress.target.repair = rankTwoRepairState complexity := by
    rw [D.pointedProgress.target_eq]
    rfl

  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress
        D.pointedProgress.target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [htargetRepair, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)

  exact {
    presented := D.presented
    sourcePresentation := hsource.trans D.sourcePresentation
    pointedProgress := D.pointedProgress
    globalProgress := hglobal
  }

end AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress

/-! ## Boundary continuation frontier -/

/-- A18.4.14 outcome after continuing through one genuine boundary
presentation.

The first three constructors are genuine exits.  `repeatedBoundary` is the
only boundary-specific residue: two consecutive global boundary
presentations have occurred with no strict exit between them.

`legacyRankTwoAfterPresentation` uniformly records the historical rank-two
head after zero or more already-certified presentation geometry.  The legacy
same-scale target is still not promoted to recursive progress. -/
inductive AdaptiveAlignedSmithCanonicalGlobalBoundaryContinuationOutcome
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

  | repeatedBoundary
      (firstTarget secondTarget :
        ScaleAwareAdaptiveGeometricRestartState (K := K))
      (first : AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation
        RR s firstTarget)
      (second : AdaptiveAlignedSmithCanonicalGlobalBoundaryPresentation
        RR firstTarget secondTarget)

  | legacyRankTwoAfterPresentation
      (presented target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hsource : HasCertifiedRamifiedEpisodeInternalMove presented s)
      (trace : AdaptiveAlignedSmithCanonicalLegacyRankTwoHeadTrace
        RR presented target)

/-- **Boundary continuation reduction.**

Run A18.4.13 at the source.  If it returns a genuine boundary presentation,
run the same frontier once on the presented state using repair preservation.
Every genuine second-stage exit is then absorbed back to `s`:

* zero raw defect reflects backwards through the positive ramification;
* a strict macro is prefixed by the boundary presentation;
* pointed rank-two progress is prefixed by the boundary presentation while
  keeping the actual pointed-family target.

Thus no boundary presentation is itself made recursive.  The only new
boundary residue is an explicit consecutive boundary pair. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalBoundaryContinuationFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalBoundaryContinuationOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalResidualPresentationHeadFrontier
      RR complexity hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D

  | legacyRankTwoPresentation target trace =>
      exact .legacyRankTwoAfterPresentation s target
        (HasCertifiedRamifiedEpisodeInternalMove.identity s) trace

  | boundaryPresentation presented B =>
      have hsource :
          HasCertifiedRamifiedEpisodeInternalMove presented s :=
        B.toInternalMove
      have hprepair : presented.repair = rankOneRepairState complexity :=
        hsource.rankOne_repair_eq hsrepair

      cases presented.alignedSmithCanonicalGlobalResidualPresentationHeadFrontier
          RR complexity hprepair with
      | zeroDefectReentry hzeroPresented Dpresented =>
          have hzero : s.rawDefect = 0 :=
            hsource.source_rawDefect_eq_zero_of_target hzeroPresented
          exact .zeroDefectReentry hzero
            (s.exists_globalZeroDefectReentryData hzero)

      | ramifiedStrictMacro D =>
          exact .ramifiedStrictMacro
            (AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro.prepend_internal
              RR hsource D)

      | pointedRankTwoProgress D =>
          rcases D with ⟨D⟩
          exact .pointedRankTwoProgress
            ⟨AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress.prepend_internal
              hsource D hsrepair⟩

      | boundaryPresentation target Bnext =>
          exact .repeatedBoundary presented target B Bnext

      | legacyRankTwoPresentation target trace =>
          exact .legacyRankTwoAfterPresentation presented target hsource trace

end

end HC4.Valuation
