import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactLayerAffineProfile
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileEndpoints

/-!
# A19 exact contact-layer / stationary-profile coefficient bridge

Every nonzero exact layer of the singular planar-contact Rees already carries
an honest affine coefficient profile indexed by source coordinate `0`.  The
stationary carrier profile uses the same literal carrier coefficients, indexed
outside by distance from the primitive highest pair and inside by coordinate
`0`.

This file identifies those two representations on every actual layer monomial.
It is deliberately coefficientwise: no support is recreated and no converse
layer-membership assertion is assumed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVParameterAffineLayerData

/-- **Exact coefficient bridge.**  A supported coefficient of an honest
planar-contact layer is the coefficient of the stationary carrier profile at
outer index `n-k` and the same inner coordinate-`0` index. -/
theorem coeff_coefficientProfile_eq_stationaryCarrierProfile
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
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family order).support) :
    A.coefficientProfile.coeff (e 0) =
      (F.stationaryCarrierProfile.coeff
        (F.highest.n - A.k)).coeff (e 0) := by
  have hprofile := A.coeff_coefficientProfile_of_mem he
  have heP : e ∈ P.carrier.support :=
    (D.parameterLayer_support_source_and_order he).1
  have hstationary :=
    F.coeff_coeff_stationaryCarrierProfile_of_mem hthree houtThree heP
  have hpair : e 0 + e 1 = A.k := (A.coordinates e he).1
  calc
    A.coefficientProfile.coeff (e 0) =
        MvPolynomial.coeff e (familyParameterLayer D.family order) := hprofile
    _ = MvPolynomial.coeff e P.carrier := A.coefficient_eq_carrier e he
    _ = (F.stationaryCarrierProfile.coeff
        (F.highest.n - A.k)).coeff (e 0) := by
      rw [← hpair]
      exact hstationary.symm

end QsOtherFacetPrLeftVParameterAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
