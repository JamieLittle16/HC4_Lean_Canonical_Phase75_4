import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsRankTwoClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowActualRankTwoProgress
import Mathlib.Tactic

/-!
# `.qs` strict-low terminal contradiction under genuine global terminality

The strengthened `.qs` boundary closure removes the former quadratic-square
and nonlinear-confinement leaves and upgrades every remaining lower-boundary
outcome to an actual rank-two Hessian chart on the represented blocker state.

At a genuinely globally terminal source state, that retained geometry cannot
survive: the existing presentation-aware rank-two consumer produces an honest
global macro successor of the source.

This file deliberately proves only the no-successor contradiction.  It does
not identify a geometry-backed progress step with an unconditional
contradiction and it does not use a repair-only terminal argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A zero strict-low terminal whose exposed singular boundary vertex is
rank-three on `.qs` is impossible at a genuine global no-successor source.

The proof is only the certified chain

```text
strengthened .qs closure
  -> actual represented-state rank-two Hessian chart
  -> geometry-backed global macro progress
  -> contradiction with global terminality.
```
-/
theorem qs_rankThree_impossible_of_no_globalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree :
      MvRankThreeOnFacet .qs
        T.exposedSingularBoundaryVertex.exponent)
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state) :
    False := by
  rcases T.qs_rankThree_actualRankTwo_noSquare hthree with ⟨C⟩
  exact T.impossible_of_actualRankTwo_of_no_globalProgress C hterminal

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
