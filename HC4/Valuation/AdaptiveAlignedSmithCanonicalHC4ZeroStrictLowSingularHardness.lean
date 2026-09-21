import HC4.Valuation.AdaptiveAlignedSmithCanonicalHC4ZeroStrictLowSingularReduction
import HC4.PlanarJC2HessianEmbedding

/-!
# Hardness guard for the final zero-strict-low singular endpoint

The current unrestricted HC4 front door reduces the determinant-one problem to
unconditional impossibility of
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData`.

This file records the exact strength of that remaining obligation.  Because
every planar Keller map embeds as the four-dimensional Hessian-gradient
doubling potential, any unconditional proof of the singular-terminal
impossibility theorem already proves the planar Jacobian-conjecture injectivity
interface.

This is a final-assembly soundness guard.  In particular, the remaining
singular endpoint must not be discharged by repair metadata, an abstract
rank-two/rank-three label, or a no-successor hypothesis which is false at the
actual zero-clock rank-one state.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The current final singular-terminal obligation is planar-JC2 hard.**

Any uniform contradiction for the actual zero-clock strict-low singular
terminal closes unrestricted HC4 via the existing A19 reducer; the standard
doubling embedding then gives planar JC2. -/
theorem planarJC2_of_zeroStrictLowSingularTerminal_impossible
    (hsingular :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
          (K := K) state → False) :
    HC4.PlanarJC2Injectivity K := by
  apply HC4.planarJC2_of_hessianFour_gradient_injective
  intro F hdet
  exact
    gradient_injective_of_hessianDeterminant_one_of_zeroStrictLowSingularTerminal_impossible
      hsingular F hdet

end

end HC4.Valuation
