import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarInteriorMomentRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarLockedMomentRealisation
import HC4.Valuation.PlanarContactFirstVariationBridge
import Mathlib.Tactic

/-!
# A19 first variation of the unit locked-side contact selector

The zero and first positive layers of the honest unit contact Rees have now
been identified with the same moment Hessians consumed by the generic contact
first-variation bridge.  Thus every selected unit contact affine package obeys
the locked-end affine two-root Euler equation, with literal source coefficients.
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

namespace QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData

/-- Locked-end Euler equation for any honest selected unit contact affine layer. -/
theorem locked_affineTwoRootEulerOperator_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.affineTwoRootEulerOperator
      (MvPolynomial.coeff C.ray.facetExponent P.carrier *
        ((F.locked.ell : K) + 1))
      (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
        (F.locked.ell : K))
      (A.k - 1) A.coefficientProfile = 0 := by
  let a : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  have ha : a ≠ 0 := by
    dsimp [a]
    exact F.locked.facet_provenance.carrier_coeff_ne
  have hb : b ≠ 0 := by
    dsimp [b]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hzero := D.zeroLayer_specialisedEulerHessian_eq_lockedBinomialMomentHessian
    hthree houtThree
  dsimp only at hzero
  have hfirst := A.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
  have hode := affineTwoRootEulerOperator_eq_zero_of_firstActual_moment_identification
    D.family D.hasPositiveLayer D.hessian_zero
    1 F.locked.ell A.k A.j
    (by norm_num : 0 < (1 : ℕ)) F.locked.ell_pos (le_of_lt A.k_gt_one)
    a b ha hb A.coefficientProfile hzero hfirst
  simpa [a, b] using hode

end QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData

namespace QsOtherFacetPrUnitLeftPlanarContactReesData

/-- Failure of endpoint-only support produces an honest selected unit contact
layer satisfying the locked-end Euler equation. -/
theorem exists_firstInteriorAffineLayer_affineTwoRootEulerOperator_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D,
      1 < A.k ∧ A.k < F.highest.n ∧
      0 < A.j ∧ A.j < F.locked.ell ∧
      HC4.Polynomial.affineTwoRootEulerOperator
        (MvPolynomial.coeff C.ray.facetExponent P.carrier *
          ((F.locked.ell : K) + 1))
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
          (F.locked.ell : K))
        (A.k - 1) A.coefficientProfile = 0 := by
  let A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D :=
    Classical.choice
      (QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData.exists_of_not_noStrictInterior
        D hthree houtThree hnot)
  exact ⟨A, A.k_gt_one, A.k_lt_highest, A.j_pos, A.j_lt_locked,
    A.locked_affineTwoRootEulerOperator_eq_zero hthree houtThree⟩

end QsOtherFacetPrUnitLeftPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
