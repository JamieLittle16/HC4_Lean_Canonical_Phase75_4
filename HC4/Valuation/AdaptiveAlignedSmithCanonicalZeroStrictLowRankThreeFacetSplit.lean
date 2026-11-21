import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowRecenteredOutsideSupport
import HC4.Newton.FirstContactCrossFacetAffineLine
import Mathlib.Tactic

/-!
# A19.58: rank-three top-face support either crosses its facet or is confined to it

A19.56 retains an actual supported exponent in the relative interior of a
coordinate facet whenever the balance-free boundary split lands in rank three.
For the next first-contact step the only finite-support question is whether the
same singular top face already has support on the other side of that facet.

This file makes that dichotomy exact.  If positive omitted-coordinate support
is present, `crossFacetInitialData` constructs the genuine two-sided exact face
immediately.  Otherwise every supported exponent has omitted coordinate zero,
so the whole top face is confined to the facet.  The latter is precisely the
honest top-degree-on-facet hypothesis needed by the first-nonfacet machinery.

No torus balance, terminal cocharacter, outside witness, or progress claim is
introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A rank-three exposed top-face exponent either already sits on a genuine
cross-facet exact face, or the entire singular top face is supported on that
coordinate facet. -/
theorem rankThree_crossFacetInitial_or_topFaceOnFacet
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree : MvRankThreeOnFacet facet
      T.exposedSingularBoundaryVertex.exponent) :
    Nonempty
        (CrossFacetInitialData T.topFace.face
          (HC4.Newton.crossFacetOppositeCoordinate
            (HC4.Polynomial.facetOmittedCoordinate facet))
          (HC4.Polynomial.facetOmittedCoordinate facet)) ∨
      HC4.Polynomial.MvSupportOnFacet facet T.topFace.face := by
  let j : Fin 4 := HC4.Polynomial.facetOmittedCoordinate facet
  have hfacet : (zeroCoordinateSupport j T.topFace.face).Nonempty := by
    simpa [j] using T.rankThree_zeroCoordinateSupport_nonempty facet hthree
  by_cases hout : (positiveCoordinateSupport j T.topFace.face).Nonempty
  · exact Or.inl ⟨crossFacetInitialData
      (i := HC4.Newton.crossFacetOppositeCoordinate j) hfacet hout⟩
  · right
    intro d hd
    apply (HC4.Polynomial.onFacet_toToricExponent_iff facet d).2
    have hnotpos : ¬ 0 < d j := by
      intro hpos
      exact hout ⟨d, mem_positiveCoordinateSupport.mpr ⟨hd, hpos⟩⟩
    have hz : d j = 0 := Nat.eq_zero_of_not_pos hnotpos
    simpa [j] using hz

/-- In the actual cross-facet branch, the constructed exact face remains
Hessian singular.  This is the balance-free singularity input needed by the
later affine-support analysis. -/
theorem rankThree_crossFacetInitial_hessian_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (D : CrossFacetInitialData T.topFace.face
      (HC4.Newton.crossFacetOppositeCoordinate
        (HC4.Polynomial.facetOmittedCoordinate facet))
      (HC4.Polynomial.facetOmittedCoordinate facet)) :
    HC4.Polynomial.hessianDeterminant D.face = 0 :=
  D.hessian_zero T.topFace_hessianDeterminant_eq_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
