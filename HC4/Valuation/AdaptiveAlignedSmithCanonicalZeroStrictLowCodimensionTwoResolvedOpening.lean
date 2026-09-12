import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoKernelOpening
import HC4.Valuation.CoordinateMaxKernelOpeningLinearPowerFirstBreak
import Mathlib.Tactic

/-!
# A19.55 resolved first-opening frontier

The source-facing codimension-two dispatcher previously left three outcomes:

* a coordinate kernel already on the actual A19 top face;
* an exact first-opening child with a nonzero Hessian `2 x 2` minor;
* an exact first-opening child equal to a scalar power of one linear form.

The last alternative is no longer an unresolved algebraic leaf.  The exact
coordinate-max provenance forces that linear form onto the extraction axis,
and the honest reverse-Rees family then gives concrete rank-two geometry at
the first actual kernel-row opening.

Thus every *first-opening* branch of A19.55 is now reduced to explicit
rank-two geometry.  The only separate local case retained here is the honest
case in which the A19 top face already has a coordinate kernel.

No auxiliary Rees clock is identified with the zero blocker and no repair
progress is asserted.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **Resolved source-honest A19.55 first-opening frontier.**

Apart from a coordinate kernel already present on the selected top face, the
canonical codimension-two extraction produces explicit rank-two geometry:
either directly on the exact child, or at the first honest kernel-row opening
of its reverse-Rees interpolation. -/
theorem exposedCodimensionTwo_topKernel_or_rankTwoGeometry
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hcodim : MvExponentOnCodimensionTwoBoundary
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ k : Fin 4,
        MvPolynomial.pderiv k T.topFace.face = 0) ∨
      (∃ D : CanonicalCoordinateMaxKernelOpeningData T.topFace.face,
        D.ChildHessianRankTwoWitness) ∨
      (∃ (D : CanonicalCoordinateMaxKernelOpeningData T.topFace.face)
          (P : D.ChildLinearPowerData T.topFace.degree),
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        let hrow := D.kernelLastBlock_kernelRow_ne_zero
          T.topFace.face_support_degree_ge_three
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j) := by
  rcases T.exposedCodimensionTwo_topKernel_or_openingRankTwo_or_linearPower hcodim with
    htop | htwo | hpower
  · exact Or.inl htop
  · exact Or.inr (Or.inl htwo)
  · rcases hpower with ⟨D, hP⟩
    rcases hP with ⟨P⟩
    right
    right
    refine ⟨D, P, ?_⟩
    exact P.firstBreakRankTwoOutcome
      T.topFace.degree_ge_three
      T.topFace.face_support_degree_ge_three

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
