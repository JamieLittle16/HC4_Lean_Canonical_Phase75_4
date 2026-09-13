import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactLayerAffineRealisation
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import Mathlib.Tactic

/-!
# A19 moment realisation of every planar-contact parameter layer

The preceding module reconstructs every nonzero exact parameter layer as an
honest generic affine rank-three line.  The generic affine moment theorem
therefore identifies the specialised Euler-scaled Hessian of each exact layer
with the same parallel-staircase moment matrix already used at the first
positive layer.

This is the all-depth representation bridge needed to read the zero Hessian
determinant of the complete Rees family coefficient by coefficient.
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

namespace QsOtherFacetPrLeftVParameterAffineLayerData

/-- **Exact all-layer moment identification.**  The specialised Euler-scaled
Hessian of an arbitrary nonzero exact planar-contact layer is the parallel
staircase moment Hessian of its source-honest coefficient profile. -/
theorem specialisedEulerHessian_eq_parallelStaircaseMomentHessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order) :
    (fun r s =>
      HC4.Polynomial.rankThreeLineSpecialisation
        (HC4.Polynomial.eulerScaledHessian
          (familyParameterLayer D.family order) r s)) =
      HC4.Polynomial.parallelStaircaseMomentHessian
        F.V A.k A.j A.coefficientProfile := by
  have h := A.affineLineData.specialisation_eulerScaledHessian
  rw [A.affineLineData_polynomial_eq_layer] at h
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun h r) s
  simpa [HC4.Polynomial.parallelStaircaseMomentHessian] using hrs

end QsOtherFacetPrLeftVParameterAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
