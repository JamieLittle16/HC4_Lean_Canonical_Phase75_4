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
No support is recreated: the converse direction is obtained from the literal
reverse-Rees occurrence of each carrier monomial and the already-proved strict
contact-order interpolation.
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

/-- **Converse layer membership at fixed pair degree.**  If an actual carrier
monomial has the pair degree of `A`, then its literal reverse-Rees order is
exactly `order`, so it belongs to the same exact contact layer.  The proof uses
only the source-honest contact interpolation and cancellation by `n-1 > 0`. -/
theorem layer_mem_of_carrier_mem_of_pair_eq
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
    (he : e ∈ P.carrier.support)
    (hpair : e 0 + e 1 = A.k) :
    e ∈ (familyParameterLayer D.family order).support := by
  classical
  rcases MvPolynomial.support_nonempty.mpr A.layer_ne with ⟨f, hf⟩
  let q := T.topFace.degree -
    Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e
  have heq : e ∈ (familyParameterLayer D.family q).support := by
    simpa [q] using D.parameterLayer_mem_of_carrier_mem he
  have heInterp := D.parameterLayer_contactOrder_interpolation
    hthree houtThree heq
  have hfInterp := D.parameterLayer_contactOrder_interpolation
    hthree houtThree hf
  have hfpair : f 0 + f 1 = A.k := (A.coordinates f hf).1
  change (F.highest.n - 1) * q =
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((e 0 + e 1) - 1) at heInterp
  change (F.highest.n - 1) * order =
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((f 0 + f 1) - 1) at hfInterp
  rw [hpair] at heInterp
  rw [hfpair] at hfInterp
  have hsame :
      (F.highest.n - 1) * q = (F.highest.n - 1) * order :=
    heInterp.trans hfInterp.symm
  have hn1pos : 0 < F.highest.n - 1 := by
    omega
  have hq : q = order := Nat.mul_left_cancel hn1pos hsame
  rw [hq] at heq
  exact heq

end QsOtherFacetPrLeftVParameterAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
