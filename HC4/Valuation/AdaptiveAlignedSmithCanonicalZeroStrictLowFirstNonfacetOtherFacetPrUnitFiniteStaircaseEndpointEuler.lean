import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarInteriorFirstVariation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPairReesFirstVariation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiber
import Mathlib.Tactic

/-!
# A19 unit endpoint Euler laws on a common strict-interior fibre

The unit locked/contact selector and the unit pair-Rees selector already carry
independent first-variation Euler equations.  When their selected pair degrees
coincide, `PrUnitFiniteStaircaseOneFiber` identifies their literal source
layers, staircase heights, and one-variable coefficient profiles.

This file exposes the highest-end equation for an arbitrary already-selected
unit pair-Rees affine package and then places both endpoint equations on the
same nonzero source-honest profile.
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

namespace QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData

/-- Highest-end Euler equation for any honest selected unit pair-Rees affine
package. -/
theorem highest_affineTwoRootEulerOperator_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D) :
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
  have hzero :=
    D.zeroLayer_specialisedEulerHessian_eq_highestBinomialMomentHessian_unitLeft F
  have hfirst := A.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
  have hEuler :=
    affineTwoRootEulerOperator_eq_zero_of_firstActual_highest_moment_identification
      D.family D.positiveLayer D.hessian_zero
      1 F.highest.n A.k A.j
      (by norm_num : 0 < (1 : ℕ)) F.highest.n_two_le
      c d hc hd A.coefficientProfile
      (by simpa [c, d] using hzero)
      hfirst
  simpa [c, d] using hEuler

end QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData

/-- In the coincident-fibre unit case, the same nonzero source profile satisfies
both endpoint Euler equations. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_commonProfile_dualEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F Dhi)
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
