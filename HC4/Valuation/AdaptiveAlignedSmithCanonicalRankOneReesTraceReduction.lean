import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSourceProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalCollisionAutoDegree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalConformalZeroClockImpossible
import Mathlib.Tactic

/-!
# A19.34b: consume positive Rees success inside the existing rank-one trace

A19.33 proves that a successful positive transverse Rees coefficient bound on
an actual scale-aware state gives exactly the three facts stored by the
A18.4.109 `restart` constructor: global macro progress, strict natural
raw-defect decrease, and unchanged repair metadata.

The normalized rank-three terminal API is allowed to introduce a pure
ramified presentation.  Running A19.33 only after that presentation is too
late for the original raw clock: a strict decrease from a ramified clock need
not be below the unramified trace source.

This file therefore runs the Rees coefficient test on each *actual* rank-one
trace state before accepting rank-three termination.  Success extends the
existing `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace`; failure
retains the concrete low-layer witness on that same actual trace state.

No new progress relation and no new termination measure are introduced.  The
only recursion is still on `rawDefect : ℕ`, and the stored trace is literally
the A18.4.109 trace type.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- An ordinary A18.4.109 rank-one trace whose final actual trace state has
already exhausted every successful positive Rees coefficient bound.

Consequently the final state either has raw defect zero or carries a concrete
A19 low layer on its own family. -/
structure AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
    (RR : RepairRanking)
    (complexity : ℕ)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
    RR complexity source
  terminalReduced :
    trace.reachedRankThree.state.rawDefect = 0 ∨
      Nonempty
        (CanonicalPositiveTransverseReesLowLayer
          trace.reachedRankThree.state.rawDefect
          trace.reachedRankThree.state.family)

/-- **A19.34b Rees-reduced rank-one trace.**

Before accepting a rank-three terminal at a positive actual trace state, test
A19.33 there.  A successful bound is inserted as an ordinary A18 `restart`
edge.  If the bound fails, A19.17 supplies the concrete low layer. -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.rankOneReesReducedTrace
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      RR complexity source := by
  by_cases hpositive : 0 < source.rawDefect
  · by_cases hbound :
      HasCanonicalPositiveTransverseReesCoefficientBound
        source.rawDefect source.family
    · rcases source.exists_canonicalPositiveTransverseRees_progress
        hpositive hbound with
        ⟨target, hprogress, hraw, hrepair⟩
      have htargetRepair : target.repair = rankOneRepairState complexity :=
        hrepair.trans hsrepair
      let tail := target.rankOneReesReducedTrace
        RR complexity htargetRepair
      refine {
        trace := .restart hprogress hraw hrepair tail.trace
        terminalReduced := ?_
      }
      simpa [AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedRankThree]
        using tail.terminalReduced
    · cases source.alignedSmithCanonicalRankThreeOrProgress
        RR complexity hsrepair with
      | globalProgress target hprogress hraw hrepair =>
          have htargetRepair : target.repair = rankOneRepairState complexity :=
            hrepair.trans hsrepair
          let tail := target.rankOneReesReducedTrace
            RR complexity htargetRepair
          refine {
            trace := .restart hprogress hraw hrepair tail.trace
            terminalReduced := ?_
          }
          simpa [AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedRankThree]
            using tail.terminalReduced
      | rankThree geometry =>
          refine {
            trace := .terminal geometry
            terminalReduced := ?_
          }
          right
          simpa [AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedRankThree]
            using
              (canonicalPositiveTransverseReesLowLayer_of_not_bound
                (K := K) hpositive hbound)
  · have hzero : source.rawDefect = 0 := Nat.eq_zero_of_not_pos hpositive
    cases source.alignedSmithCanonicalRankThreeOrProgress
        RR complexity hsrepair with
    | globalProgress target hprogress hraw hrepair =>
        omega
    | rankThree geometry =>
        refine {
          trace := .terminal geometry
          terminalReduced := ?_
        }
        left
        simpa [AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedRankThree]
          using hzero
termination_by source.rawDefect

decreasing_by
  all_goals omega

/-- The Rees-reduced trace preserves the canonical rank-one repair coordinate
because every newly inserted A19.33 edge has unchanged repair metadata. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.reachedRankThree_repair_eq
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      RR complexity source)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    T.trace.reachedRankThree.state.repair = rankOneRepairState complexity := by
  exact T.trace.reachedRankThree_repair_eq hsrepair

/-- At a positive final actual trace state, the only surviving A19 outcome is
a concrete low layer.  The successful coefficient-bound branch has already
been consumed as trace progress. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.lowLayer_of_terminal_positive
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      RR complexity source)
    (hpositive : 0 < T.trace.reachedRankThree.state.rawDefect) :
    Nonempty
      (CanonicalPositiveTransverseReesLowLayer
        T.trace.reachedRankThree.state.rawDefect
        T.trace.reachedRankThree.state.family) := by
  rcases T.terminalReduced with hzero | hlow
  · omega
  · exact hlow

/-- Positive-clock front door using the Rees-reduced version of the existing
rank-one trace. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.positiveRankOneReesReducedTrace
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      RR complexity (E.positiveReentry complexity).state :=
  (E.positiveReentry complexity).state.rankOneReesReducedTrace
    RR complexity (E.positiveReentry_repair complexity)

/-- Exact residual obligations after successful positive Rees frontiers have
been removed from the trace itself.

The zero-clock no-strict-low branch is still discharged internally by the
existing affine one-zero recovery theorem.  Thus A19.34b leaves only:

* an actual zero-clock strict-low exponent on the represented terminal fibre;
* a positive low layer on the *actual terminal trace state*.
-/
structure AdaptiveAlignedSmithCanonicalReesReducedResidualResolver where
  zeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hzero : state.rawDefect = 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e),
      False

  positiveLowLayer :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family),
      False

/-- A Rees-reduced reachable trace is contradictory once the two remaining
low-layer themes are consumed. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.impossible_of_resolver
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (R : AdaptiveAlignedSmithCanonicalReesReducedResidualResolver (K := K)) :
    False := by
  let reached := T.trace.reachedRankThree
  let terminal := reached.geometry.toPresentedTerminal
  have hrepair : reached.state.repair = rankOneRepairState 0 := by
    simpa [reached] using T.reachedRankThree_repair_eq hsrepair
  have hreduced :
      reached.state.rawDefect = 0 ∨
        Nonempty
          (CanonicalPositiveTransverseReesLowLayer
            reached.state.rawDefect reached.state.family) := by
    simpa [reached] using T.terminalReduced
  rcases hreduced with hzero | hlow
  · by_cases hstrict :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 terminal.specialFiber,
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e
    · rcases hstrict with ⟨e, he, hpattern⟩
      exact R.zeroStrictLow hrepair terminal hzero e he hpattern
    · have hno : terminal.HasNoStrictLowSmithPatterns := by
        intro e he
        constructor
        · intro hpure
          exact hstrict ⟨e, he, Or.inl hpure⟩
        constructor
        · intro hfirst
          exact hstrict ⟨e, he, Or.inr (Or.inl hfirst)⟩
        · intro hsecond
          exact hstrict ⟨e, he, Or.inr (Or.inr hsecond)⟩
      exact terminal.conformalDegreeTwoFace_impossible_of_source_rawDefect_eq_zero
        hzero hno
  · rcases hlow with ⟨L⟩
    have hpositive : 0 < reached.state.rawDefect := by
      have hearly := L.early
      omega
    exact R.positiveLowLayer hrepair terminal hpositive L

/-- **A19.34b final reduction with the Rees-success residual deleted.**

Unlike A19.24/A19.26, there is no `positiveReesReentry` or
`survivingPositiveReesReentry` field.  Every successful coefficient bound has
already become an ordinary edge of the existing raw-defect trace. -/
theorem gradient_injective_of_hessianDeterminant_one_of_reesReducedResidualResolver
    (R : AdaptiveAlignedSmithCanonicalReesReducedResidualResolver (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  intro p q hgrad
  by_contra hpq
  have hcoll : HasExactGradientCollision F p q := by
    intro i
    exact congrFun hgrad i
  let E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K) :=
    zeroDefectCollisionEntry_ofExactCollision_autoDegree
      F p q hdet hpq hcoll
  let trace := E.positiveRankOneReesReducedTrace
    canonicalAdaptiveAlignedSmithRepairRanking 0
  exact trace.impossible_of_resolver
    (E.positiveReentry_repair 0) R

end

end HC4.Valuation
