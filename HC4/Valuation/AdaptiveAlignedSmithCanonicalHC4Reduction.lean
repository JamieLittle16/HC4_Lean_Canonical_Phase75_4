import HC4.Valuation.AdaptiveAlignedSmithCanonicalCollisionAutoDegree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneTraceCollapse
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import HC4.Newton.TerminalCollision

/-!
# A19.1: unrestricted HC4 reduces to the presented-terminal contradiction

All proposition-level front-door bookkeeping is now closed:

* every polynomial has the canonical nonlinear degree cap `totalDegree`;
* an arbitrary distinct exact gradient collision is recentered and sent to
  `0 ~ e₀` by determinant-one source changes;
* the determinant-one entry is routed once through the positive Rees
  presentation;
* A18.4.109 supplies the finite rank-one termination trace; and
* A18.5.75 collapses that trace as soon as its normalized presented terminal is
  impossible.

This file records the resulting final reduction.  No torus grading, JC2
hypothesis, homogeneous source assumption, or pre-normalized collision remains
in the public input.  The sole remaining mathematical obligation is the
hypothesis-free impossibility of the presented rank-three terminal.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **A19.1 — terminal impossibility implies unrestricted determinant-one
gradient injectivity.**

The terminal hypothesis is deliberately stated only at the canonical repair
ranking and complexity `0`; the complexity label is bookkeeping and every
arbitrary collision can enter the A18 machine at that stage. -/
theorem gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
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
  exact trace.impossible_of_presentedTerminal_impossible hterminal

/-- Equivalent no-distinct-collision form of the same unrestricted reduction. -/
theorem no_distinct_exactGradientCollision_of_hessianDeterminant_one_of_presentedTerminal_impossible
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hterminal :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
          canonicalAdaptiveAlignedSmithRepairRanking state 0 → False) :
    ∀ p q : Fin 4 → K,
      p ≠ q → ¬ HasExactGradientCollision F p q := by
  intro p q hpq hcoll
  exact hpq
    (exactGradientCollision_eq_of_injective
      F p q
      (gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
        F hdet hterminal)
      hcoll)

end

end HC4.Valuation
