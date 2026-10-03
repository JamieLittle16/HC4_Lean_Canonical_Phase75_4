import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorFirstVariation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesHighestFirstVariation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiber
import Mathlib.Tactic

/-!
# A19 endpoint Euler laws on already-selected affine staircase fibres

The existing first-variation theorems construct an affine package and then
return its endpoint Euler equation.  For the finite-staircase coupling we need
the same equations attached to arbitrary already-selected affine packages, so
that a low package and a high package can subsequently be identified in the
one-fibre case.

No new determinant calculation occurs here: these are direct reusable forms
of the two already-verified first-variation arguments.
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

namespace QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- Locked-end Euler equation for any honest contact-side affine package. -/
theorem locked_affineTwoRootEulerOperator_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
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

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

namespace QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- Highest-end Euler equation for any honest pair-Rees affine package. -/
theorem highest_affineTwoRootEulerOperator_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D) :
    let c := MvPolynomial.coeff F.highest.e0 S.slice
    let d := MvPolynomial.coeff F.highest.e1 S.slice
    HC4.Polynomial.affineTwoRootEulerOperator
      (c * (F.highest.n : K))
      (d * ((F.highest.n - 1 : ℕ) : K))
      A.j A.coefficientProfile = 0 := by
  let c : K := MvPolynomial.coeff F.highest.e0 S.slice
  let d : K := MvPolynomial.coeff F.highest.e1 S.slice
  have he0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have he1S : F.highest.e1 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hc : c ≠ 0 := by
    dsimp [c]
    exact MvPolynomial.mem_support_iff.mp he0S
  have hd : d ≠ 0 := by
    dsimp [d]
    exact MvPolynomial.mem_support_iff.mp he1S
  have hV : 0 < F.V := lt_trans Nat.zero_lt_one F.V_gt_one
  have hzero := D.zeroLayer_specialisedEulerHessian_eq_highestBinomialMomentHessian_left F
  have hfirst := A.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
  have hEuler :=
    affineTwoRootEulerOperator_eq_zero_of_firstActual_highest_moment_identification
      D.family D.positiveLayer D.hessian_zero
      F.V F.highest.n A.k A.j hV F.highest.n_two_le
      c d hc hd A.coefficientProfile
      (by simpa [c, d] using hzero)
      hfirst
  simpa [c, d] using hEuler

end QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- In the one-fibre case, the *same* nonzero source profile satisfies both
endpoint Euler equations. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_commonProfile_dualEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k) :
    Alo.coefficientProfile ≠ 0 ∧
    HC4.Polynomial.affineTwoRootEulerOperator
      (MvPolynomial.coeff C.ray.facetExponent P.carrier *
        ((F.locked.ell : K) + 1))
      (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
        (F.locked.ell : K))
      (Alo.k - 1) Alo.coefficientProfile = 0 ∧
    HC4.Polynomial.affineTwoRootEulerOperator
      (MvPolynomial.coeff F.highest.e0 S.slice * (F.highest.n : K))
      (MvPolynomial.coeff F.highest.e1 S.slice *
        ((F.highest.n - 1 : ℕ) : K))
      Alo.j Alo.coefficientProfile = 0 := by
  have hj := F.selectedInterior_j_eq_of_k_eq
    Alo Ahi hthree houtThree hext
  have hp := F.selectedInteriorProfiles_eq_of_k_eq
    Alo Ahi hthree houtThree hext
  refine ⟨Alo.coefficientProfile_ne_zero,
    Alo.locked_affineTwoRootEulerOperator_eq_zero hthree houtThree, ?_⟩
  have hhi := Ahi.highest_affineTwoRootEulerOperator_eq_zero
  rw [← hp, ← hj] at hhi
  simpa using hhi

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
