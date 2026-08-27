import HC4.Valuation.AdaptiveAlignedSmithCanonicalSourceNativeFirstContactReduction
import HC4.PlanarJC2HessianEmbedding

/-!
# A19.42: exact final planar-JC2 frontier

The source-native A19 reduction now reaches the honest first-contact endpoint
without losing the actual trace state on the positive branches.  At that
boundary every four-dimensional counterexample produces an explicit planar
Keller collision, while the standard two-zero doubling construction embeds
every planar Keller collision back into a determinant-one four-dimensional
Hessian gradient.

This file records the resulting exact logical frontier.  It is deliberately
bidirectional: under the remaining source-native first-contact construction,
planar JC2 is neither a convenience nor a stronger hypothesis than the desired
four-dimensional gradient injectivity statement.  They are equivalent.

No terminal-extraction interface, homogeneity shortcut, divisibility shortcut,
or additional recursion is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Exact A19 final frontier.**  Once the three source-native first-contact
constructors are supplied, planar JC2 is equivalent to injectivity of every
four-variable polynomial gradient with Hessian determinant one. -/
theorem planarJC2_iff_hessianFour_gradient_injective_of_sourceNativeFirstContactProducer
    (P : AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K)) :
    HC4.PlanarJC2Injectivity K ↔
      ∀ F : MvPolynomial (Fin 4) K,
        HC4.Polynomial.hessianDeterminant F = 1 →
          Function.Injective (mvGradientMap F) := by
  constructor
  · intro hJC2 F hdet
    exact
      gradient_injective_of_hessianDeterminant_one_of_JC2_of_sourceNativeFirstContactProducer
        hJC2 P F hdet
  · intro hHC4
    exact HC4.planarJC2_of_hessianFour_gradient_injective hHC4

/-- Counterexample-facing form of the exact frontier: under the source-native
producer, failure of HC4 yields an explicit planar Keller collision. -/
theorem hessianFour_counterexample_hasPlanarKellerCollision_of_sourceNativeFirstContactProducer
    (P : AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K))
    {F : MvPolynomial (Fin 4) K}
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hninj : ¬ Function.Injective (mvGradientMap F)) :
    HC4.HasPlanarKellerCollision K :=
  hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_sourceNativeFirstContactProducer
    P F hdet hninj

end

end HC4.Valuation
