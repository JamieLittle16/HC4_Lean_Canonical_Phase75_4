import HC4.Valuation.AdaptiveAlignedSmithCanonicalRelativeFirstContactReduction
import HC4.PlanarJC2HessianEmbedding

/-!
# A19.43: exact final planar-JC2 frontier with relative first deformation

The source-native A19 reduction reaches the final first-contact seam without
losing the actual trace state.  The positive earlier-actual-layer branch must
be formulated relatively: freeze the complete special fibre and factor

    P = P(0) + X^j Q,

so that `Q(0)` is exactly the first genuine positive coefficient potential.
A19.42 packages this factorisation canonically on the actual trace family.

At an honest first-contact endpoint every four-dimensional counterexample
produces an explicit planar Keller collision, while the standard two-zero
doubling construction embeds every planar Keller collision back into a
determinant-one four-dimensional Hessian gradient.

This file records both the historical source-native statement and the
corrected relative front door.  No terminal-extraction interface,
homogeneity shortcut, divisibility shortcut, or additional recursion is
introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Historical source-native form, retained for compatibility. -/
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

/-- **Corrected A19 final frontier.**  Once the two literal terminal adapters
and the relative first-deformation adapter are supplied, planar JC2 is
exactly equivalent to injectivity of every four-variable polynomial gradient
with Hessian determinant one. -/
theorem planarJC2_iff_hessianFour_gradient_injective_of_relativeFirstContactProducer
    (P : AdaptiveAlignedSmithCanonicalRelativeFirstContactResidualProducer
      (K := K)) :
    HC4.PlanarJC2Injectivity K ↔
      ∀ F : MvPolynomial (Fin 4) K,
        HC4.Polynomial.hessianDeterminant F = 1 →
          Function.Injective (mvGradientMap F) := by
  constructor
  · intro hJC2 F hdet
    exact
      gradient_injective_of_hessianDeterminant_one_of_JC2_of_relativeFirstContactProducer
        hJC2 P F hdet
  · intro hHC4
    exact HC4.planarJC2_of_hessianFour_gradient_injective hHC4

/-- Counterexample-facing historical source-native form. -/
theorem hessianFour_counterexample_hasPlanarKellerCollision_of_sourceNativeFirstContactProducer
    (P : AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K))
    {F : MvPolynomial (Fin 4) K}
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hninj : ¬ Function.Injective (mvGradientMap F)) :
    HC4.HasPlanarKellerCollision K :=
  hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_sourceNativeFirstContactProducer
    P F hdet hninj

/-- Counterexample-facing corrected relative form. -/
theorem hessianFour_counterexample_hasPlanarKellerCollision_of_relativeFirstContactProducer
    (P : AdaptiveAlignedSmithCanonicalRelativeFirstContactResidualProducer
      (K := K))
    {F : MvPolynomial (Fin 4) K}
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hninj : ¬ Function.Injective (mvGradientMap F)) :
    HC4.HasPlanarKellerCollision K :=
  hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_sourceNativeFirstContactProducer
    P.toSourceNative F hdet hninj

end

end HC4.Valuation
