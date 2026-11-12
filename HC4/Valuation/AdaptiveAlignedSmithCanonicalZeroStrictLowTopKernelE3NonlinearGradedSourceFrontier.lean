import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3GradedSourceMinor
import Mathlib.Tactic

/-!
# Nonlinear E3 frontier retaining the exact graded represented-source minor

The older rank-two frontier records a nonzero Hessian 2x2 minor somewhere
on the represented determinant-one source.  That is too weak to
distinguish nonlinear E3 from generic determinant-one geometry.

Here the rank-two outcome instead retains a nonzero Hessian 2x2 minor
on the first actual marked-axis face itself.  This face is the exact
maximal transverse-weight component of the *unchanged* represented
source at the smaller cap r.  The proved graded-minor identity
therefore identifies a nonzero source-minor component at weight
2r - (w_i + w_j + w_k + w_l) >= 2.

The other four cases are not promoted to contradictions or ranks:
support-facet rank, lower-face coordinate kernel, transverse first
opening, or longitudinal linear-power first-break geometry.
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

/-- A source-honest five-way nonlinear E3 classification.  The marked-axis
rank-two case retains an exact minor on the first actual face; the source
grade and source nonvanishing follow from this stronger datum. -/
inductive PureLongitudinalMarkedE3NonlinearGradedSourceFrontier
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
  | gradedSourceRankTwo
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (i j k l : Fin 4)
      (hminor :
        hessianTwoByTwoMinor
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder) i j k l ≠ 0)
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

/-- Unconditional nonlinear E3 frontier with the precise first-face Hessian
minor preserved.  This starts from the original geometric boundary split,
then uses the canonical opening's *exact three-face provenance* to transport
any longitudinal child rank-two minor all the way to the first actual face.
No subsequent source-level grade is forgotten in the output packet. -/
theorem PureLongitudinalMarkedE3Data.nonlinearGradedSourceFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    Nonempty P.PureLongitudinalMarkedE3NonlinearGradedSourceFrontier := by
  rcases P.pureLongitudinal_markedAxis_lowerBoundaryFrontier_nonempty
      D.coefficient_ne_zero D.topFace_eq with ⟨H⟩
  cases H with
  | quadratic hr =>
      exact (D.quadratic_relevel_impossible P hr).elim
  | rankThree N facet hfacet =>
      exact ⟨.facetSupport N facet hfacet⟩
  | kernelOpening N _outcome =>
      rcases mvBoundary_rankThreeFacet_or_codimensionTwo
          N.vertex.exponent_boundary with hthree | hcodim
      · rcases hthree with ⟨facet, hfacet⟩
        exact ⟨.facetSupport N facet hfacet⟩
      · let F := familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder
        have hcodim' :
            MvExponentOnCodimensionTwoBoundary
              (exposedSingularNonlinearBoundaryVertex
                F N.face_ne N.hessian_zero
                  N.support_degree_ge_three).exponent := by
          simpa [F, PureLongitudinalMarkedAxisLowerNonlinearData.vertex]
            using hcodim
        rcases canonicalCodimensionTwoKernel_or_firstOpening_withProvenance
            F N.face_ne N.hessian_zero N.support_degree_ge_three hcodim'
            with hkernel | hopen
        · rcases hkernel with ⟨k, hk⟩
          exact ⟨.lowerFaceKernel N k hk⟩
        · rcases hopen with ⟨O, hprovenance⟩
          by_cases hlong : O.kernelCoordinate = (0 : Fin 4)
          · rcases
                P.pureLongitudinal_lowerFirstOpening_longitudinal_rankTwoResolved
                  D.coefficient_ne_zero D.topFace_eq N O hlong with
              htwo | hpower
            · rcases canonicalOpeningRankTwo_source_of_threeFaceProvenance
                F N.face_ne O hprovenance htwo with
                ⟨i, j, k, l, hminorF⟩
              exact ⟨.gradedSourceRankTwo N i j k l hminorF⟩
            · rcases hpower with ⟨LP, hbreak⟩
              exact ⟨.longitudinalPowerFirstBreak N O hlong LP hbreak⟩
          · exact ⟨.transverseFirstOpening N O hlong⟩

/-- The strong graded rank-two constructor carries a source minor with
nonzero exact transverse-weight component of degree at least two. -/
theorem PureLongitudinalMarkedE3Data.gradedSourceRankTwo_witness
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
    (i j k l : Fin 4)
    (hminor :
      hessianTwoByTwoMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j k l ≠ 0) :
    let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
    let w : Fin 4 → ℤ := fun a => (topKernelMarkedAxisNatWeight a : ℤ)
    let e : ℤ := ((r : ℤ) - w i - w k) + ((r : ℤ) - w j - w l)
    2 ≤ e ∧
      HC4.Polynomial.initialForm w e
        (hessianTwoByTwoMinor T.topKernelReesSource i j k l) ≠ 0 := by
  exact D.firstActualTwoByTwoMinor_sourcePositiveGraded P i j k l hminor

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
