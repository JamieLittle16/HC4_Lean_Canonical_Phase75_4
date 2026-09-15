import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalWallData
import HC4.Newton.MixedDegreeFirstWallCompetition
import Mathlib.Tactic

/-!
# A18.5.21: canonical support frontier on the actual terminal polynomial

A18.5.19--20 show that the represented terminal special fibre still carries
exactly the normalized axis data and attained canonical Smith wall used by the
mixed-degree Newton classifier.

Therefore the existing first-wall theorem can be applied directly to the
terminal polynomial.  No presentation is changed and no rank label is used.
The result is the finite support dichotomy needed by the final contradiction:

* a concrete blocker exponent, retaining its full mixed-degree longitudinal
  residual data; or
* a nonempty canonical balanced subface all of whose exponents are one of the
  three quadratic Smith patterns `(0,2,0)`, `(1,1,0)`, `(2,0,0)`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- **Terminal canonical support frontier.**

The actual represented special fibre is either caught by one of the four
mixed-degree blocker patterns with its honest residual polynomial data, or its
canonical symmetric Smith face is the nonempty quadratic face already used by
the packet machinery. -/
theorem specialFiber_blocker_or_quadraticRefinement
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber,
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome T.specialFiber e) ∨
      ((smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ))).Nonempty ∧
       ∀ e ∈ smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ)),
         (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
         (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
         (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) := by
  have haxis := T.specialFiber_axisData
  have hwall := T.specialFiber_canonicalWallData
  rcases haxis with ⟨hcoll, hgrad, hvalue⟩
  have hmin :
      ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber,
        (0 : ℤ) ≤ (fun _ : SmithSupportExponent => (0 : ℤ)) e := by
    intro e he
    simp
  rcases minimalSmithLevel_blockerOutcome_or_symmetricQuadraticRefinement
      T.specialFiber
      (fun _ : SmithSupportExponent => (0 : ℤ))
      0 hcoll hgrad hvalue hwall.minimal hmin hwall.attained with
    hblock | hquad
  · left
    rcases hblock with ⟨e, he, hlevel, hpattern, houtcome⟩
    exact ⟨e, he, hpattern, houtcome⟩
  · exact Or.inr hquad

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- Trace-facing form of the same finite support frontier. -/
theorem AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reached_blocker_or_quadraticRefinement
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3
          trace.reachedPresentedRankThree.terminal.specialFiber,
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome
          trace.reachedPresentedRankThree.terminal.specialFiber e) ∨
      ((smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3
            trace.reachedPresentedRankThree.terminal.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ))).Nonempty ∧
       ∀ e ∈ smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3
            trace.reachedPresentedRankThree.terminal.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ)),
         (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
         (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
         (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :=
  trace.reachedPresentedRankThree.terminal.specialFiber_blocker_or_quadraticRefinement

end

end HC4.Valuation