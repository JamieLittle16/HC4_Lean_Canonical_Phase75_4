import HC4.Valuation.AdaptiveAlignedSmithCanonicalFirstContactPlanarCollision
import HC4.PlanarJC2HessianEmbedding
import Mathlib.Tactic

/-!
# A19.39: the final first-contact seam is exactly planar Keller injectivity

A19.36 isolates three source-facing geometric producers.  Once they construct
honest first-contact endpoints, A19.38 sends every such endpoint to a concrete
planar Keller collision, unconditionally.  Conversely A19.4 closes every such
endpoint under planar JC2.

This file records the global consequence at the actual HC4 theorem.  Under the
three honest producer adapters:

* a failure of four-dimensional determinant-one Hessian-gradient injectivity
  produces an explicit planar Keller collision;
* planar JC2 implies four-dimensional determinant-one Hessian-gradient
  injectivity; and
* together with the already-green A19.3 embedding in the reverse direction,
  the two injectivity statements are equivalent.

No new endpoint mathematics is introduced here.  The only remaining geometric
work is therefore the source-to-first-contact producer construction itself.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Under the honest source-to-first-contact producer, an HC4 counterexample
constructs an actual planar Keller counterexample witness. -/
theorem hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_firstContactResidualProducer
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hninj : ¬ Function.Injective (mvGradientMap F)) :
    HC4.HasPlanarKellerCollision K := by
  classical
  by_contra hno
  have hendpoint :
      ∀ E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K),
        False := by
    intro E
    exact hno E.hasPlanarKellerCollision
  have hinj : Function.Injective (mvGradientMap F) :=
    gradient_injective_of_hessianDeterminant_one_of_firstContactResidualProducer_of_endpointImpossible
      P hendpoint F hdet
  exact hninj hinj

/-- Equivalent negated form: under the producer, any HC4 counterexample
certifies failure of the exact planar JC2 injectivity interface. -/
theorem not_planarJC2_of_hessianDeterminant_one_of_not_injective_of_firstContactResidualProducer
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hninj : ¬ Function.Injective (mvGradientMap F)) :
    ¬ HC4.PlanarJC2Injectivity K :=
  (hasPlanarKellerCollision_of_hessianDeterminant_one_of_not_injective_of_firstContactResidualProducer
    P F hdet hninj).not_planarJC2

/-- **A19.39 exact final equivalence.**

Once the three source-facing first-contact producers are constructed, planar
JC2 injectivity is equivalent to unrestricted determinant-one injectivity of
four-dimensional polynomial Hessian gradients.  The reverse implication is
A19.3; the forward implication is the complete A18/A19 termination proof plus
the honest first-contact endpoint. -/
theorem planarJC2_iff_hessianFour_gradient_injective_of_firstContactResidualProducer
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer (K := K)) :
    HC4.PlanarJC2Injectivity K ↔
      ∀ F : MvPolynomial (Fin 4) K,
        HC4.Polynomial.hessianDeterminant F = 1 →
          Function.Injective (mvGradientMap F) := by
  constructor
  · intro hJC2 F hdet
    exact
      gradient_injective_of_hessianDeterminant_one_of_JC2_of_firstContactResidualProducer
        hJC2 P F hdet
  · intro hHC4
    exact HC4.planarJC2_of_hessianFour_gradient_injective hHC4

end

end HC4.Valuation
