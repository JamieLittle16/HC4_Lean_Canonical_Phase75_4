import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowNonlinearConfinementHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowActualRankTwoProgress
import Mathlib.Tactic

/-!
# Nonlinear confinement is impossible at a genuine global terminal

The source-honest nonlinear-confinement Hessian theorem now produces an actual
rank-two Hessian chart on the represented blocker family.  The existing
presentation-aware rank-two consumer turns exactly that retained geometry into
strict global macro progress from the honest source.

This module records only the resulting no-successor contradiction.  No repair
tag is promoted without geometry and no new local algebra is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A nonlinear-confined zero strict-low terminal cannot be a genuine global
no-successor state. -/
theorem nonlinearConfined_impossible_of_no_globalProgress
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : HC4.Toric.ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d))
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state) :
    False := by
  rcases T.nonlinearConfined_actualRankTwoHessianChart facet hconfined with ⟨C⟩
  exact T.impossible_of_actualRankTwo_of_no_globalProgress C hterminal

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
