import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesHighestMomentRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInteriorMomentRealisation
import Mathlib.Tactic

/-!
# A19 highest-end first variation on the actual pair-Rees interior layer

If strict-interior support survives, the pair-degree reverse Rees selects the
highest surviving interior fibre as its first positive actual layer.  The
preceding source-honest realisations identify layer zero with the actual
primitive highest binomial and the first positive layer with the actual
parallel staircase profile.

The generic highest-end dual-jet bridge therefore applies directly and yields
the affine two-root Euler equation with roots `j,j+1`.
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

/-- **Highest-end source-honest interior Euler equation.**

Failure of endpoint-only support canonically supplies the first positive
pair-Rees interior fibre together with the dual Euler equation forced by the
singularity of the actual pair-Rees family. -/
theorem QsOtherFacetPrLeftVContactFrontierData.exists_pairReesFirstInterior_dualEuler
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
      let c := MvPolynomial.coeff F.highest.e0 S.slice
      let d := MvPolynomial.coeff F.highest.e1 S.slice
      HC4.Polynomial.affineTwoRootEulerOperator
        (c * (F.highest.n : K))
        (d * ((F.highest.n - 1 : ℕ) : K))
        A.j A.coefficientProfile = 0 := by
  rcases QsOtherFacetPrPairFirstInteriorAffineLayerData.exists_of_not_noStrictInterior
      F D hthree houtThree hnot with ⟨A⟩
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
  exact ⟨A, by simpa [c, d] using hEuler⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
