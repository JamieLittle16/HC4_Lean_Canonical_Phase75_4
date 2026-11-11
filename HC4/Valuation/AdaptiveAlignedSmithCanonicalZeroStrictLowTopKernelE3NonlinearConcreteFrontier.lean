import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3NonlinearFrontier
import Mathlib.Tactic

/-!
# E3 nonlinear pure-longitudinal face: concrete finite kernel-opening frontier

The quadratic transverse source has been ruled out by a source-level
contradiction.  Consequently the first actual marked-axis face in the
pure-longitudinal E3 branch is nonzero, Hessian-singular and genuinely
nonlinear of transverse degree at least three.

This file decomposes its two surviving boundary types *without
conflating combinatorial support rank with Hessian rank*:

* a rank-three *support exponent* on a toric facet;
* a genuine coordinate kernel on the lower singular polynomial;
* a coordinate-max first opening away from the longitudinal axis;
* a longitudinal first opening with an actual rank-two Hessian minor;
* a longitudinal first opening of a homogeneous linear power, whose
  first kernel-row break carries the already-proved rank-two outcome.

In particular, a first opening is not asserted to be an ambient
zero-defect terminal chart or a represented-source Hessian certificate.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Exact outstanding nonlinear outcomes on the original first-actual lower
face.  The first two are support/kernel alternatives; only the last two
already carry rank-two Hessian geometry, and then only on the opened child
or its auxiliary reverse-Rees first break. -/
inductive PureLongitudinalMarkedE3NonlinearConcreteFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | facetSupport
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (facet : HC4.Toric.ToricFacet)
      (hfacet : MvRankThreeOnFacet facet N.vertex.exponent)
  | lowerFaceKernel
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (coordinate : Fin 4)
      (hkernel :
        MvPolynomial.pderiv coordinate
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder) = 0)
  | transverseFirstOpening
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (O : CanonicalCoordinateMaxKernelOpeningData
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder))
      (htrans : O.kernelCoordinate ≠ (0 : Fin 4))
  | longitudinalChildRankTwo
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (O : CanonicalCoordinateMaxKernelOpeningData
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder))
      (hlong : O.kernelCoordinate = (0 : Fin 4))
      (htwo : O.ChildHessianRankTwoWitness)
  | longitudinalPowerFirstBreak
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (O : CanonicalCoordinateMaxKernelOpeningData
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder))
      (hlong : O.kernelCoordinate = (0 : Fin 4))
      (LP : O.ChildLinearPowerData
        (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder))
      (hbreak :
        let B := kernelLastFamilyHessianFourBlock
          O.reverseReesFamily O.kernelCoordinate
        let hrow := O.kernelLastBlock_kernelRow_ne_zero
          N.support_degree_ge_three
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j)

/-- The quadratic-free E3 lower singular source reaches one of five
concrete outcomes.  All opening and rank-two witnesses refer to the
original first-actual face and its exact canonical descendants. -/
theorem PureLongitudinalMarkedE3Data.nonlinearConcreteFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    Nonempty P.PureLongitudinalMarkedE3NonlinearConcreteFrontier := by
  rcases P.pureLongitudinal_markedAxis_lowerBoundaryFrontier_nonempty
      D.coefficient_ne_zero D.topFace_eq with ⟨H⟩
  cases H with
  | quadratic hr =>
      exact (D.quadratic_relevel_impossible P hr).elim
  | rankThree N facet hfacet =>
      exact ⟨.facetSupport N facet hfacet⟩
  | kernelOpening N outcome =>
      cases outcome with
      | topKernel coordinate hkernel =>
          exact ⟨.lowerFaceKernel N coordinate hkernel⟩
      | firstOpening O =>
          by_cases hlong : O.kernelCoordinate = (0 : Fin 4)
          · rcases
                P.pureLongitudinal_lowerFirstOpening_longitudinal_rankTwoResolved
                  D.coefficient_ne_zero D.topFace_eq N O hlong with
              htwo | hpower
            · exact ⟨.longitudinalChildRankTwo N O hlong htwo⟩
            · rcases hpower with ⟨LP, hbreak⟩
              exact ⟨.longitudinalPowerFirstBreak N O hlong LP hbreak⟩
          · exact ⟨.transverseFirstOpening N O hlong⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
