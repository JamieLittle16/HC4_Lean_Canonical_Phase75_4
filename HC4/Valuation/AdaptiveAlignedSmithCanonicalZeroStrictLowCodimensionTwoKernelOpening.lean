import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoCarrierKernel
import HC4.Newton.FiniteSupportSingularBoundaryKernelOpening
import HC4.Valuation.CoordinateMaxKernelOpeningDegenerateClassification
import Mathlib.Tactic

/-!
# A19.55 source-facing codimension-two kernel-opening frontier

The codimension-two branch of the actual zero strict-low terminal already
retains the canonical singular top face and its exposed boundary vertex.  The
finite coordinate-max construction on that same source has only two first
possibilities: either the kernel direction already annihilates the top face,
or there is an exact initial-form child on which that kernel first appears.

Because the A19 top face is honestly homogeneous of degree at least three,
every such exact child remains homogeneous at that same degree.  The existing
rank-one Hessian classification then gives a finite source-honest frontier:

* a coordinate kernel already on the top face;
* an exact first-opening child with a nonzero Hessian `2 x 2` minor; or
* an exact first-opening child which is a scalar power of one linear form.

No auxiliary Rees clock is identified with the zero blocker and no repair
progress is asserted here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Finite source-honest frontier for the A19.55 codimension-two branch. -/
theorem exposedCodimensionTwo_topKernel_or_openingRankTwo_or_linearPower
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hcodim : MvExponentOnCodimensionTwoBoundary
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ k : Fin 4,
        MvPolynomial.pderiv k T.topFace.face = 0) ∨
      (∃ D : CanonicalCoordinateMaxKernelOpeningData T.topFace.face,
        D.ChildHessianRankTwoWitness) ∨
      (∃ D : CanonicalCoordinateMaxKernelOpeningData T.topFace.face,
        Nonempty (D.ChildLinearPowerData T.topFace.degree)) := by
  let O :=
    HC4.Newton.exposedSingularNonlinearBoundaryVertex_codimensionTwoKernelOutcome
      T.topFace.face
      T.topFace.face_ne_zero
      T.topFace.hessian_zero
      T.topFace.face_support_degree_ge_three
      hcodim
  cases O with
  | topKernel k hk =>
      exact Or.inl ⟨k, hk⟩
  | firstOpening D =>
      rcases D.child_rankTwo_or_linearPower
          T.topFace.face_isHomogeneous (by omega : 2 ≤ T.topFace.degree) with
        htwo | hpower
      · exact Or.inr (Or.inl ⟨D, htwo⟩)
      · exact Or.inr (Or.inr ⟨D, hpower⟩)

/-- In either first-opening branch the retained child is literally supported
inside the actual A19 top face, hence inside the source selected by the
strict-low terminal.  This convenience theorem prevents later consumers from
reconstructing provenance through the coordinate-max chain. -/
theorem exposedCodimensionTwo_firstOpening_child_support_subset
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : CanonicalCoordinateMaxKernelOpeningData T.topFace.face) :
    D.child.support ⊆ T.topFace.face.support :=
  D.child_support_subset_source

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
