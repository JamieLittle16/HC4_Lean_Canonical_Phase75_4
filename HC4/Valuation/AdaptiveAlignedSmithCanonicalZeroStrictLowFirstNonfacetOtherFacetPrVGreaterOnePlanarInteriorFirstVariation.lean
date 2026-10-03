import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorMomentRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarLockedMomentRealisation
import HC4.Valuation.PlanarContactFirstVariationBridge
import Mathlib.Tactic

/-!
# A19 source-honest first variation of a surviving strict-interior layer

All representation data needed by `PlanarContactFirstVariationBridge` is now
available directly from the live A19 planar-contact Rees family.  If strict
interior support survives, its least positive actual layer therefore satisfies
the affine two-root Euler equation with the literal locked source
coefficients.

This theorem intentionally stops at the first-variation equation.  In
particular it does **not** assert `natDegree <= 1`: higher-degree solutions of
the affine equation exist, and the remaining exclusion must use stronger
source/contact or full Hessian information.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- **Honest A19 first-variation equation.**  Failure of endpoint-only support
produces a source-derived affine layer whose coefficient profile satisfies the
locked-binomial affine two-root Euler equation. -/
theorem exists_firstInteriorAffineLayer_affineTwoRootEulerOperator_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D,
      HC4.Polynomial.affineTwoRootEulerOperator
        (MvPolynomial.coeff C.ray.facetExponent P.carrier *
          ((F.locked.ell : K) + 1))
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
          (F.locked.ell : K))
        (A.k - 1) A.coefficientProfile = 0 := by
  rcases QsOtherFacetPrLeftVFirstInteriorAffineLayerData.exists_of_not_noStrictInterior
      D hthree houtThree hnot with ⟨A⟩
  refine ⟨A, ?_⟩
  let a : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  have ha : a ≠ 0 := by
    dsimp [a]
    exact F.locked.facet_provenance.carrier_coeff_ne
  have hb : b ≠ 0 := by
    dsimp [b]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hzero :=
    D.zeroLayer_specialisedEulerHessian_eq_lockedBinomialMomentHessian
      hthree houtThree
  dsimp only at hzero
  have hfirst := A.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
  have hode := affineTwoRootEulerOperator_eq_zero_of_firstActual_moment_identification
    D.family D.hasPositiveLayer D.hessian_zero
    F.V F.locked.ell A.k A.j
    (by omega) F.locked.ell_pos (by omega)
    a b ha hb A.coefficientProfile hzero hfirst
  simpa [a, b] using hode

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
