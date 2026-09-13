import HC4.Valuation.AdaptiveAlignedSmithCanonicalHC4Reduction
import Mathlib.Tactic

/-!
# A19.23: retain canonical rank-one provenance in the final HC4 reduction

A18.4.109 already proves that its finite raw-defect trace never changes the
canonical rank-one repair coordinate.  The first A19.1 front door deliberately
asked for impossibility of every presented terminal, even terminals carrying
an arbitrary repair tag.  That is stronger than final assembly needs and hides
precisely the provenance required by the positive Rees re-entry branch.

This file keeps the repair equality through terminal extraction.  The final
HC4 obligation is therefore only the impossibility of a presented terminal
which is actually reachable as the endpoint of the canonical rank-one trace.
No new recursion or progress relation is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A finite A18.4.109 trace is contradictory as soon as its genuinely
reachable presented terminal is contradictory under the inherited canonical
rank-one repair equality. -/
theorem
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.impossible_of_reachablePresentedTerminal_impossible
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        state.repair = rankOneRepairState complexity →
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          RR state complexity → False) :
    False := by
  let R := trace.reachedRankThree
  have hrepair : R.state.repair = rankOneRepairState complexity := by
    simpa [R] using trace.reachedRankThree_repair_eq hsrepair
  exact hterminal hrepair R.geometry.toPresentedTerminal

/-- **Repair-aware unrestricted HC4 reduction.**

To prove determinant-one gradient injectivity it is enough to rule out the
presented terminals that can actually occur at the end of the canonical
rank-one trace.  In particular final assembly may freely use the inherited
`rankOneRepairState 0` equality when consuming an A19 positive Rees spend. -/
theorem gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        state.repair = rankOneRepairState 0 →
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
  let trace := E.positiveRankOneTerminationTrace
    canonicalAdaptiveAlignedSmithRepairRanking 0
  have hsrepair :
      (E.positiveReentry 0).state.repair = rankOneRepairState 0 :=
    E.positiveReentry_repair 0
  exact trace.impossible_of_reachablePresentedTerminal_impossible
    hsrepair hterminal

end

end HC4.Valuation
