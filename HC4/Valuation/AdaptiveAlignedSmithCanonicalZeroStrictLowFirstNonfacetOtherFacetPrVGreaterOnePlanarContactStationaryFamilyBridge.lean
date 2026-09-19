import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryLayerBridge
import HC4.Valuation.ParameterFirstLayerBridge
import Mathlib.Tactic

/-!
# A19 planar-contact family / stationary-profile bridge

The stationary profile is not a recreated polynomial.  Every nonzero exact
layer of the singular planar-contact Rees has already been realised as an
honest affine rank-three line whose omitted-coordinate step is one.  Therefore
rank-three line specialisation recovers its coefficient profile literally.
Moving the family parameter to the outer polynomial variable then packages
all of those honest layer profiles in one polynomial.

Combined with `PlanarContactStationaryLayerBridge`, the coefficient at an
actual contact order is exactly the corresponding coefficient of the source-
honest stationary carrier profile.  No ramification, division, support
reconstruction, or new degree hypothesis is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVParameterAffineLayerData

/-- Rank-three line specialisation of an exact planar-contact layer recovers
its honest one-variable coefficient profile literally. -/
theorem rankThreeLineSpecialisation_layer_eq_coefficientProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order) :
    HC4.Polynomial.rankThreeLineSpecialisation
        (familyParameterLayer D.family order) =
      A.coefficientProfile := by
  rw [← A.affineLineData_polynomial_eq_layer]
  calc
    HC4.Polynomial.rankThreeLineSpecialisation A.affineLineData.polynomial =
        A.coefficientProfile.comp Polynomial.X := by
      rw [Polynomial.comp_eq_sum_left]
      simp only [HC4.Polynomial.RankThreeAffineLineData.polynomial,
        Polynomial.sum_def, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [A.affineLineData.specialisation_term hj]
      simp
    _ = A.coefficientProfile := by simp

end QsOtherFacetPrLeftVParameterAffineLayerData

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The singular contact family with the parameter outermost and the source
variables specialised to the canonical rank-three line. -/
noncomputable def specialisedParameterFirstFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (Polynomial K) :=
  Polynomial.map
    (HC4.Polynomial.rankThreeLineSpecialisation (K := K))
    (parameterFirstEquiv K D.family)

/-- Every nonzero exact contact layer appears in the specialised family with
exactly its honest coefficient profile. -/
theorem specialisedParameterFirstFamily_coeff_eq_coefficientProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order) :
    D.specialisedParameterFirstFamily.coeff order = A.coefficientProfile := by
  unfold specialisedParameterFirstFamily
  rw [Polynomial.coeff_map]
  rw [parameterFirstEquiv_coeff]
  exact A.rankThreeLineSpecialisation_layer_eq_coefficientProfile

/-- **Whole-family stationary coefficient bridge.**  At every actual nonzero
contact order, the specialised source family coefficient is literally the
stationary carrier coefficient indexed by distance from the primitive highest
pair. -/
theorem specialisedParameterFirstFamily_coeff_eq_stationaryCarrierProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.specialisedParameterFirstFamily.coeff order =
      F.stationaryCarrierProfile.coeff (F.highest.n - A.k) := by
  rw [D.specialisedParameterFirstFamily_coeff_eq_coefficientProfile A]
  exact A.coefficientProfile_eq_stationaryCarrierProfile_coeff hthree houtThree

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
