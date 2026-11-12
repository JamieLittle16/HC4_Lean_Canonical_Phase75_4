import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3CanonicalOpeningProvenance
import Mathlib.Tactic

/-!
# From codimension-two nonlinear E3 openings to the genuine represented source

The exposed singular boundary vertex on the first actual lower transverse
face is constructed using the exact first-layer polynomial, not an
arbitrary approximation.  When its boundary exponent is codimension two,
a canonical first opening can be chosen with an explicit identity to
one of the first three coordinate-max faces of that same polynomial.

The three-step arbitrary-minor theorem then lifts any child Hessian rank-two
witness to the lower transverse face.  The relevelled maximal-transverse
source-minor theorem lifts it once more to the unchanged determinant-one
represented source.

No rank-two witness is postulated: it remains a conditional conclusion
on an actual child, ready to be discharged by the already-existing
longitudinal-opening rank-two/linear-power split.
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

/-- At a codimension-two exposed nonlinear boundary vertex, either the
first actual lower transverse face has a genuine coordinate kernel,
or there exists a *canonical, provenanced* opening whose rank-two child
witness would force a nonzero arbitrary Hessian minor of the unchanged
represented determinant-one source. -/
theorem PureLongitudinalMarkedE3Data.codimensionTwoLowerFace_kernelOrOpeningSourceMinor
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
      O.ChildHessianRankTwoWitness →
        ∃ i j k l : Fin 4,
          hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0) := by
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
    right
    refine ⟨O, ?_⟩
    intro htwo
    rcases canonicalOpeningRankTwo_source_of_threeFaceProvenance
        F N.face_ne O hprovenance htwo with ⟨i, j, k, l, hminorF⟩
    exact ⟨i, j, k, l,
      D.firstActualTwoByTwoMinor_sourceLift P i j k l hminorF⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
