import HC4.Valuation.AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalObstructionProducer

/-!
# Final unrestricted HC4 assembly from a terminal obstruction producer

The repair-aware unrestricted reducer already asks only for contradiction of
presented rank-three terminals actually reachable at canonical complexity zero.
A18.5.90 packages the remaining terminal mathematics as one exact
blocker/surviving obstruction producer.

This file composes those two verified interfaces.  It introduces no new
geometry, repair transition, termination measure, or terminal hypothesis.
Once a concrete terminal obstruction producer is constructed, unrestricted
determinant-one gradient injectivity is immediate.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Terminal-obstruction producer implies unrestricted HC4.**

All global collision normalization, positive Rees entry, finite rank-one
termination, and repair provenance are discharged by the existing
repair-aware HC4 reducer.  The producer is used only at the actual reachable
presented terminal. -/
theorem
    gradient_injective_of_hessianDeterminant_one_of_terminalObstructionProducer
    (P : AdaptiveAlignedSmithCanonicalTerminalObstructionProducer
      (K := K) canonicalAdaptiveAlignedSmithRepairRanking 0)
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  apply
    gradient_injective_of_hessianDeterminant_one_of_reachablePresentedTerminal_impossible
      F hdet
  intro state _hrepair T
  exact T.impossible_of_obstructionProducer P

end

end HC4.Valuation
