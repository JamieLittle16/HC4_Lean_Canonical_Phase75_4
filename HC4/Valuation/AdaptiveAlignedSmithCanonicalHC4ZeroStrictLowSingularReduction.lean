import HC4.Valuation.AdaptiveAlignedSmithCanonicalHC4ZeroStrictLowReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminal

/-!
# Direct singular-terminal reduction for unrestricted HC4

The determinant-one entry has literal raw Hessian defect zero, so the final
public reduction does not need a second repair-state termination argument.
The existing zero-strict-low reducer already shows that unrestricted HC4 is
reduced to contradiction of the concrete zero-clock strict-low blocker.

This file moves that final hypothesis to the geometry-rich carrier used by
the A19 boundary analysis.  Every zero-strict-low terminal canonically
constructs an
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData` on the same
source state, retaining the actual presented blocker, complete rank-three
geometry, zero presented clock, and genuine singular maximal ordinary face.

Thus the remaining theorem may work entirely with source-honest singular
geometry.  No `GlobalMacroProgress` terminality, repair-only relabelling, or
new well-founded recursion is introduced.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Sound final HC4 splice through the singular strict-low carrier.**

To prove unrestricted determinant-one gradient injectivity it is enough to
rule out the geometry-rich zero-clock strict-low singular terminal.  This is
the preferred final assembly boundary: unlike a no-global-successor
hypothesis, it retains exactly the polynomial geometry needed by the A19
boundary and RationalRigidity consumers. -/
theorem
    gradient_injective_of_hessianDeterminant_one_of_zeroStrictLowSingularTerminal_impossible
    (hsingular :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
          (K := K) state → False)
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  apply
    gradient_injective_of_hessianDeterminant_one_of_zeroStrictLowTerminal_impossible
      (K := K)
  · intro state T
    exact hsingular T.toSingularTerminal
  · exact F
  · exact hdet

end

end HC4.Valuation
