import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalResidualReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalResidualConstructorReduction
import HC4.PlanarJC2HessianEmbedding

/-!
# A19.33: the final unrestricted HC4 resolver is genuinely JC2-hard

The remaining A19 resolver must not be discharged by a bookkeeping shortcut.
The planar cotangent/doubling embedding already proves that unrestricted
four-variable Hessian-gradient injectivity implies planar JC2.  Combining that
hardness theorem with the exact A19.24/A19.26 front doors shows directly that
*any* completed final residual resolver already proves `PlanarJC2Injectivity`.

This is a soundness guard only.  It introduces no axiom, no assumption, and no
new termination relation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Filling the exact three-field A19.24 residual resolver proves planar JC2. -/
theorem planarJC2_of_finalResidualResolver
    (R : AdaptiveAlignedSmithCanonicalFinalResidualResolver (K := K)) :
    HC4.PlanarJC2Injectivity K := by
  apply HC4.planarJC2_of_hessianFour_gradient_injective
  intro F hdet
  exact gradient_injective_of_hessianDeterminant_one_of_finalResidualResolver
    R F hdet

/-- The constructor-refined A19.26 checklist is equally strong: filling its
four concrete endpoint fields already proves planar JC2. -/
theorem planarJC2_of_finalConstructorResidualResolver
    (R : AdaptiveAlignedSmithCanonicalFinalConstructorResidualResolver
      (K := K)) :
    HC4.PlanarJC2Injectivity K := by
  apply HC4.planarJC2_of_hessianFour_gradient_injective
  intro F hdet
  exact
    gradient_injective_of_hessianDeterminant_one_of_finalConstructorResidualResolver
      R F hdet

end

end HC4.Valuation
