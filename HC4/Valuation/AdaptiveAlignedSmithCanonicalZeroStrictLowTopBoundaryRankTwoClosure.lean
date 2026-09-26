import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopBoundaryNextRay
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBalanceFreeRayRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTopFaceHomogeneous
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Consume a lossless top-boundary transition to rank-two geometry or codimension two

The lossless A19 frontier retains enough starting-facet provenance to turn a
top-face boundary transition into an honest cross-facet ray.  The existing
balance-free homogeneous ray theorem then gives either:

* a genuine nonzero principal Hessian minor on that exact singular top face; or
* a codimension-two endpoint of the normalized ray.

In the Hessian-minor branch, maximal ordinary initial-form covariance lifts the
minor from the singular top face back to the represented special fibre, where
it packages as the existing actual rank-two Hessian chart.

The codimension-two alternatives are deliberately retained verbatim.  In
particular, no normalized-ray endpoint is identified with the canonical
A19.55 exposed codimension-two vertex.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Residual codimension-two data left after consuming a top-boundary
transition through the balance-free homogeneous ray theorem. -/
inductive TopBoundaryCodimensionTwoResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet) : Type (u + 1)
  | direct
      (d : Fin 4 →₀ ℕ)
      (mem : d ∈ T.topFace.face.support)
      (boundary : MvExponentOnCodimensionTwoBoundary d)
  | normalizedRay
      (next : ToricFacet)
      (next_ne : next ≠ facet)
      (R : CrossFacetRayData T.topFace.face
        (HC4.Polynomial.facetOmittedCoordinate next))
      (boundary :
        MvExponentOnCodimensionTwoBoundary
            R.renameContactToZero.facetExponent ∨
          MvExponentOnCodimensionTwoBoundary
            (R.renameContactToZero.zeroAffineLineData.exponent
              R.renameContactToZero.zeroCoefficientPolynomial.natDegree))

/-- **Top-boundary rank-two closure up to explicit codimension two.**

A genuine top-face boundary transition either produces an actual rank-two
Hessian chart on the represented state, or leaves one of the two honest
codimension-two residuals above. -/
theorem topBoundaryTransition_actualRankTwo_or_codimensionTwo
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree :
      MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
    (htransition :
      AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
        facet T.topFace.face) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty (T.TopBoundaryCodimensionTwoResidual facet) := by
  rcases T.topBoundaryTransition_nextRay_or_codimensionTwo
      facet hthree htransition with hray | hcodim
  · rcases hray with ⟨next, hne, hR⟩
    rcases hR with ⟨R⟩
    have hhom :
        ∀ d ∈ T.topFace.face.support,
          HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
      intro d hd
      exact T.topFace.face_support_ordinaryDegree_eq hd
    rcases balanceFreeHomogeneousRay_codimensionTwo_or_sourceRankTwo
        R T.topFace.hessian_zero hhom with hnear | hfar | hminor
    · exact Or.inr ⟨.normalizedRay next hne R (Or.inl hnear)⟩
    · exact Or.inr ⟨.normalizedRay next hne R (Or.inr hfar)⟩
    · rcases hminor with ⟨i, k, hik, hminorTop⟩
      have hweight :
          HC4.Polynomial.IsWeightLE
            (fun _ : Fin 4 => (1 : ℤ))
            (T.topFace.degree : ℤ)
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family) := by
        intro d hd
        change
          Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d ≤
            (T.topFace.degree : ℤ)
        rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
        exact_mod_cast T.topFace.maximal d hd
      have hminorSource :
          HC4.Polynomial.hessianPrincipalMinor
              (polynomialFamilySpecialFiber
                T.terminal.blocker.presented.family) i k ≠ 0 := by
        apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
          hweight i k
        simpa [T.topFace.face_eq] using hminorTop
      exact Or.inl
        ⟨actualRankTwoHessianChart_of_specialFiber_minor
          hik hminorSource⟩
  · rcases hcodim with ⟨d, hd, hboundary⟩
    exact Or.inr ⟨.direct d hd hboundary⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
