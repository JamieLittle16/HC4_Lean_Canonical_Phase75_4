import HC4.Valuation.AdaptiveAlignedSmithCanonicalCollisionAutoDegree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalReachableTerminalClock
import HC4.Newton.TerminalCollision

/-!
# A19.6: unrestricted HC4 only needs the reachable seven-clock terminal frontier

A19.1 stated the final terminal consumer uniformly over every abstract
presented rank-three terminal.  The actual unrestricted determinant-one front
door is much narrower: A17.8 enters the mature rank-one machine at raw defect
exactly six and A18.4.109 thereafter uses only strict raw-defect descents.

A19.5 retains that bound through the finite trace.  This file therefore gives
the sharper unrestricted reduction: it is enough to contradict presented
terminals whose source raw defect is at most six.

No endpoint geometry is asserted here.  The point is to make the remaining
JC2-facing theorem match exactly the terminals reachable from an HC4
counterexample, rather than a larger artificial class.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **A19.6 — reachable-terminal impossibility implies unrestricted HC4.** -/
theorem gradient_injective_of_hessianDeterminant_one_of_reachableTerminal_impossible
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        state.rawDefect ≤ 6 →
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          canonicalAdaptiveAlignedSmithRepairRanking state 0 → False) :
    Function.Injective (mvGradientMap F) := by
  intro p q hgrad
  by_contra hpq
  have hcoll : HasExactGradientCollision F p q := by
    intro i
    exact congrFun hgrad i
  let E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K) :=
    zeroDefectCollisionEntry_ofExactCollision_autoDegree
      F p q hdet hpq hcoll
  exact E.positiveRankOneTerminationTrace_impossible_of_bounded_terminal
    canonicalAdaptiveAlignedSmithRepairRanking 0 hterminal

/-- Collision-facing form of the same reachable-frontier reduction. -/
theorem no_distinct_exactGradientCollision_of_hessianDeterminant_one_of_reachableTerminal_impossible
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        state.rawDefect ≤ 6 →
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          canonicalAdaptiveAlignedSmithRepairRanking state 0 → False) :
    ∀ p q : Fin 4 → K,
      p ≠ q → ¬ HasExactGradientCollision F p q := by
  intro p q hpq hcoll
  exact hpq
    (exactGradientCollision_eq_of_injective
      F p q
      (gradient_injective_of_hessianDeterminant_one_of_reachableTerminal_impossible
        F hdet hterminal)
      hcoll)

end

end HC4.Valuation
