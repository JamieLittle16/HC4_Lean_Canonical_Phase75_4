import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
import Mathlib.Tactic

/-!
# A18.5.1: normalize the terminal rank-three provenance

A18.4.109 ends every canonical rank-one collision trace in one of three
wrapper constructors:

* an exact presented blocker;
* an exact presented surviving wall; or
* a section-boundary rank-three exit.

The boundary exit is itself already a presented blocker or presented surviving
wall.  Thus the first step of the terminal splice should not duplicate the
later algebra for a third artificial case.  This file removes exactly that
wrapper distinction while retaining the complete presented endpoint and all
of its certified source-presentation provenance.

No new geometric claim is made here.  In particular, this interface does not
identify a rank-three Hessian/Schur event with a logarithmic exponent line and
does not manufacture a terminal cocharacter.  Those are later mathematical
adapters and must be proved from the retained geometry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A uniform presented terminal reached by the complete aligned rank-three
analysis.  Both constructors retain the actual presented endpoint object, so
its `sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove ...` field
remains available to every later classification adapter. -/
inductive AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | blocker
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        RR D complexity)
  | surviving
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
        RR D complexity)

/-- Forget only whether a presented terminal was reached directly at an exact
aligned endpoint or through a coupled section-boundary head.  The presented
endpoint and its complete rank-three geometry are unchanged. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry.toPresentedTerminal
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
      RR source complexity) :
    AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity := by
  cases G with
  | exactBlocker D geometry =>
      exact .blocker D geometry
  | exactSurviving D geometry =>
      exact .surviving D geometry
  | boundary geometry =>
      cases geometry with
      | blocker D geometry =>
          exact .blocker D geometry
      | surviving D geometry =>
          exact .surviving D geometry

/-- Terminal state together with the normalized presented rank-three object.
The state is the genuine final state of the well-founded raw-defect trace, not
a repair-only relabelling of the initial state. -/
structure AdaptiveAlignedSmithCanonicalReachedPresentedRankThree
    (RR : RepairRanking)
    (complexity : ℕ) : Type (u + 1) where
  state : ScaleAwareAdaptiveGeometricRestartState (K := K)
  terminal : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
    RR state complexity

/-- Normalize the terminal geometry retained by A18.4.109. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalReachedRankThree.toPresentedTerminal
    {RR : RepairRanking}
    {complexity : ℕ}
    (R : AdaptiveAlignedSmithCanonicalReachedRankThree
      (K := K) RR complexity) :
    AdaptiveAlignedSmithCanonicalReachedPresentedRankThree
      (K := K) RR complexity where
  state := R.state
  terminal := R.geometry.toPresentedTerminal

/-- Lossless terminal projection directly from the finite rank-one trace. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedPresentedRankThree
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    AdaptiveAlignedSmithCanonicalReachedPresentedRankThree
      (K := K) RR complexity :=
  T.reachedRankThree.toPresentedTerminal

/-- **Normalized global rank-one termination.**

Every canonical rank-one collision state reaches a genuine terminal state
carrying either a presented blocker or presented surviving endpoint with its
complete rank-three geometry.  The finite raw-defect trace remains available
through A18.4.109; this corollary merely supplies the uniform interface wanted
by the terminal classification splice. -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.reachedPresentedRankThree
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalReachedPresentedRankThree
      (K := K) RR complexity :=
  (source.rankOneTerminationTrace RR source complexity hsrepair).reachedPresentedRankThree

end

end HC4.Valuation
