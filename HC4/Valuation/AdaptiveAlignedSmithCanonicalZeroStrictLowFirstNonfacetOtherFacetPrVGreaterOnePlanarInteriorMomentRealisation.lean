import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorAffineRealisation
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import Mathlib.Tactic

/-!
# A19 moment realisation of the first strict-interior layer

The first strict-interior parameter layer is now literally reconstructed by a
generic `RankThreeAffineLineData` object.  The generic affine moment theorem
therefore identifies its specialised Euler-scaled Hessian with the exact
`parallelStaircaseMomentHessian` used by the locked-binomial first-variation
calculation.

This is representation plumbing only.  It does not assert that the first
layer is singular and it does not impose any degree bound on its profile.
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

namespace QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- **Exact first-interior moment identification.**  The specialised
Euler-scaled Hessian of the honest first positive layer is the parallel
staircase moment Hessian of its source-derived coefficient profile. -/
theorem specialisedEulerHessian_eq_parallelStaircaseMomentHessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) :
    (fun r s =>
      HC4.Polynomial.rankThreeLineSpecialisation
        (HC4.Polynomial.eulerScaledHessian
          (familyParameterLayer D.family
            (firstPositiveActualParameterOrder D.family D.hasPositiveLayer))
          r s)) =
      HC4.Polynomial.parallelStaircaseMomentHessian
        F.V A.k A.j A.coefficientProfile := by
  have h := A.affineLineData.specialisation_eulerScaledHessian
  rw [A.affineLineData_polynomial_eq_layer] at h
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun h r) s
  simpa [HC4.Polynomial.parallelStaircaseMomentHessian] using hrs

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
