import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentationDispatcher
import Mathlib.Tactic

/-!
# A18.4.6: presentation-trace invariants and canonical trace frontier

A18.4.5 records finite provenance for every pure ramified presentation that
survives the final stationary-planar-core assembly.  A18.4.4 still carries a
second, redundant `HasCertifiedRamifiedEpisodeInternalMove` beside that trace.

This file makes the trace itself authoritative.

* every trace canonically reconstructs a certified ramified internal move;
* therefore every trace preserves the represented scaled defect exactly;
* repair state and the zero/nonzero status of the raw clock are preserved;
* the exported frontier keeps only the trace, eliminating the possibility of
  pairing provenance with an unrelated bookkeeping move.

No presentation is declared to be recursive progress.  In particular the
cross-multiplication equality below is used only as an invariant, never as a
well-founded ordering.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## A provenance trace is itself a certified pure presentation -/

/-- Recover the certified ramified internal move represented by a finite
presentation trace.

The three leaf constructors use exactly the certified moves carried by their
original producers.  Transitive provenance is interpreted by the A18.4.3
composition law. -/
theorem AdaptiveAlignedSmithCanonicalPresentationTrace.toInternalMove
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR source target) :
    HasCertifiedRamifiedEpisodeInternalMove target source := by
  induction trace with
  | survivingExactClock W clock_eq =>
      exact
        ⟨W.original.aligned.certifiedOuterInternal_of_defect_eq
          _ clock_eq⟩
  | sectionBoundary B =>
      exact
        ⟨ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryCertifiedInternalMove
          _ B⟩
  | legacyRankTwo outer target hmove hprogress =>
      exact hmove
  | trans first second ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

/-- A presentation trace represents exactly the same normalized Hessian
clock as its source.  This is the semantic quotient invariant for arbitrary
finite chains of factor-changing presentations. -/
theorem AdaptiveAlignedSmithCanonicalPresentationTrace.scaledDefect_equivalent
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR source target) :
    ScaledDefect.Equivalent target.scaledDefect source.scaledDefect := by
  rcases trace.toInternalMove with ⟨hmove⟩
  exact hmove.scaledDefect_equivalent

/-- Presentation provenance cannot alter the finite repair stage. -/
theorem AdaptiveAlignedSmithCanonicalPresentationTrace.repair_eq
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR source target) :
    target.repair = source.repair := by
  exact
    HasCertifiedRamifiedEpisodeInternalMove.repair_eq
      trace.toInternalMove

/-- Presentation provenance preserves whether the raw determinant clock is
zero.  The forward direction is immediate from ramification; the reverse
direction uses positivity of every certified ramification factor. -/
theorem AdaptiveAlignedSmithCanonicalPresentationTrace.rawDefect_eq_zero_iff
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR source target) :
    target.rawDefect = 0 ↔ source.rawDefect = 0 := by
  constructor
  · intro hzero
    exact
      HasCertifiedRamifiedEpisodeInternalMove.source_rawDefect_eq_zero_of_target
        trace.toInternalMove hzero
  · intro hzero
    rcases trace.toInternalMove with ⟨hmove⟩
    rw [hmove.raw_eq, hzero]
    simp

/-- Explicit cross-multiplication form of the scaled-defect invariant.
Keeping this theorem at the state level avoids any temptation for downstream
code to compare absolute raw clocks across different presentation scales. -/
theorem AdaptiveAlignedSmithCanonicalPresentationTrace.rawDefect_mul_scale_eq
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR source target) :
    target.rawDefect * source.scale =
      source.rawDefect * target.scale := by
  simpa [ScaledDefect.Equivalent,
    ScaleAwareAdaptiveGeometricRestartState.scaledDefect] using
    trace.scaledDefect_equivalent

/-! ## Canonical trace-only presentation frontier -/

/-- A18.4 frontier with presentation provenance as the sole certificate for a
zero-cost reparametrisation.

The three genuine exits are unchanged.  The final constructor deliberately
contains no independent `hmove`: it is reconstructible from `trace` by
`AdaptiveAlignedSmithCanonicalPresentationTrace.toInternalMove`. -/
inductive AdaptiveAlignedSmithCanonicalGlobalPresentationTraceOutcome
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
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A18.4.6 canonical trace frontier.**

Erase the redundant certified-move witness from A18.4.4.  Nothing is lost:
`trace.toInternalMove` reconstructs it from source-honest provenance.  This is
a pure soundness refinement and does not introduce a new recursive edge. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalPresentationTraceFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentationTraceOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalPresentationDispatchFrontier
      RR complexity hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D
  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D
  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D
  | internalPresentation target hmove trace =>
      exact .internalPresentation target trace

end

end HC4.Valuation
