import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesHighestMomentRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInteriorMomentRealisation
import HC4.Valuation.PlanarHighestFirstVariationBridge
import Mathlib.Tactic

/-!
# A19 first pair-Rees layer -> highest-end affine two-root equation

The pair-degree reverse Rees is oriented from the primitive highest slice.
Under failure of `NoStrictInteriorSupport`, its least positive actual layer is
the highest surviving strict-interior staircase fibre.

The preceding source-honest adapters identify the zero layer with the literal
primitive highest binomial moment Hessian and the first positive layer with
the literal parallel-staircase moment Hessian.  The generic highest-end
parameter-gap dual-jet bridge therefore gives the affine two-root Euler
equation with roots `j,j+1` for that actual source profile.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrPairReesData

/-- **Highest-end equation for the highest surviving interior fibre.**

Everything in the conclusion is carried by the actual pair-Rees family and
its literal source coefficients.  No comparison with the contact-Rees family
is needed. -/
theorem exists_firstPositiveLayer_highestEulerEquation_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D,
      1 < A.k ∧ A.k < F.highest.n ∧
      0 < A.j ∧ A.j < F.locked.ell ∧
      HC4.Polynomial.affineTwoRootEulerOperator
        ((MvPolynomial.coeff F.highest.e0 S.slice) * (F.highest.n : K))
        ((MvPolynomial.coeff F.highest.e1 S.slice) *
          ((F.highest.n - 1 : ℕ) : K))
        A.j A.coefficientProfile = 0 := by
  let A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D :=
    Classical.choice
      (QsOtherFacetPrPairFirstInteriorAffineLayerData.exists_of_not_noStrictInterior
        F D hthree houtThree hnot)
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
  have hVpos : 0 < F.V :=
    lt_trans (Nat.zero_lt_succ 0) F.V_gt_one
  have hzero :=
    D.zeroLayer_specialisedEulerHessian_eq_highestBinomialMomentHessian_left F
  have hfirst := A.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
  have hEuler :=
    affineTwoRootEulerOperator_eq_zero_of_firstActual_highest_moment_identification
      D.family D.positiveLayer D.hessian_zero
      F.V F.highest.n A.k A.j
      hVpos F.highest.n_two_le
      c d hc hd A.coefficientProfile
      (by simpa [c, d] using hzero) hfirst
  exact ⟨A, A.k_gt_one, A.k_lt_highest, A.j_pos, A.j_lt_locked,
    by simpa [c, d] using hEuler⟩

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
