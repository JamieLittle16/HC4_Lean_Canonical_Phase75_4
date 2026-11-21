import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3CodimensionTwoSourceMinorBridge
import Mathlib.Tactic

/-!
# The nonlinear E3 codimension-two branch after canonical minor provenance

The original first-opening classification gives either a rank-two Hessian
witness on the longitudinal opening's child, or a homogeneous linear-power
first-break witness.  Exact canonical chain provenance now lets us replace
the first alternative by an *actual nonzero Hessian two-by-two minor of the
original represented source*.

The other alternatives remain honest: a kernel on the lower face, an opening
of a transverse coordinate, or the linear-power rank-one first-break
geometry.  None of these is declared to be a terminal contradiction.
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

/-- The codimension-two first-actual lower-face branch has four remaining
outcomes, with a genuine source Hessian minor replacing the old
longitudinal-child-only rank-two witness. -/
theorem PureLongitudinalMarkedE3Data.codimensionTwoLowerFace_sourceRankTwoFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
    (hcodim : MvExponentOnCodimensionTwoBoundary N.vertex.exponent) :
    (∃ k : Fin 4,
      MvPolynomial.pderiv k
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) = 0) ∨
    (∃ O : CanonicalCoordinateMaxKernelOpeningData
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder),
        O.kernelCoordinate ≠ (0 : Fin 4)) ∨
    (∃ i j k l : Fin 4,
      hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0) ∨
    (∃ O : CanonicalCoordinateMaxKernelOpeningData
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder),
      O.kernelCoordinate = (0 : Fin 4) ∧
      ∃ LP : O.ChildLinearPowerData
          (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder),
        let B := kernelLastFamilyHessianFourBlock
          O.reverseReesFamily O.kernelCoordinate
        let hrow := O.kernelLastBlock_kernelRow_ne_zero
          N.support_degree_ge_three
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j) := by
  let F := familyParameterLayer
    T.topKernelMarkedAxisFirstContactFamily
    T.topKernelMarkedAxisFirstActualLayerOrder
  have hcodim' :
      MvExponentOnCodimensionTwoBoundary
        (exposedSingularNonlinearBoundaryVertex
          F N.face_ne N.hessian_zero N.support_degree_ge_three).exponent := by
    simpa [F, PureLongitudinalMarkedAxisLowerNonlinearData.vertex] using hcodim
  rcases canonicalCodimensionTwoKernel_or_firstOpening_withProvenance
      F N.face_ne N.hessian_zero N.support_degree_ge_three hcodim'
      with hkernel | hopen
  · exact Or.inl hkernel
  · rcases hopen with ⟨O, hprovenance⟩
    by_cases hlong : O.kernelCoordinate = (0 : Fin 4)
    · rcases
        P.pureLongitudinal_lowerFirstOpening_longitudinal_rankTwoResolved
          D.coefficient_ne_zero D.topFace_eq N O hlong with
        htwo | hpower
      · rcases canonicalOpeningRankTwo_source_of_threeFaceProvenance
          F N.face_ne O hprovenance htwo with ⟨i, j, k, l, hminorF⟩
        exact Or.inr (Or.inr (Or.inl ⟨i, j, k, l,
          D.firstActualTwoByTwoMinor_sourceLift P i j k l hminorF⟩))
      · rcases hpower with ⟨LP, hbreak⟩
        exact Or.inr (Or.inr (Or.inr ⟨O, hlong, LP, hbreak⟩))
    · exact Or.inr (Or.inl ⟨O, hlong⟩)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
