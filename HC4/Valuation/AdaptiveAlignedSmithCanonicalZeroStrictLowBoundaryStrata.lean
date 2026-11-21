import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryFrontier
import HC4.Newton.FiniteSupportCrossFacetExposure
import Mathlib.Tactic

/-!
# A19.56: retain actual finite-support boundary strata at the zero strict-low terminal

A19.55 exposes a genuine nonlinear monomial of the singular maximal ordinary
top face and proves the balance-free dichotomy

* rank three on one coordinate facet; or
* codimension two on two distinct coordinate boundaries.

For the next cross-facet step we need the corresponding finite-support slices,
not merely the abstract vanishing equations.  This file turns the A19.55
exponent into those exact nonempty support slices.  No outside support is
invented here: proving that one of these boundary slices has an actual
first-departure exponent on the other side is the next geometric obligation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Exact finite-support stratum carried by the A19.55 exposed top-face
exponent.  The rank-three branch remembers the facet itself; the
codimension-two branch remembers the two distinct zero coordinates. -/
inductive AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStratum
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | rankThree
      (facet : ToricFacet)
      (rankThree : MvRankThreeOnFacet facet
        T.exposedSingularBoundaryVertex.exponent)
  | codimensionTwo
      (i j : Fin 4)
      (distinct : i ≠ j)
      (first_zero : T.exposedSingularBoundaryVertex.exponent i = 0)
      (second_zero : T.exposedSingularBoundaryVertex.exponent j = 0)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The A19.55 balance-free split as an explicit Type-valued finite stratum. -/
noncomputable def boundaryStratum
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStratum T :=
  Classical.choice (by
    show Nonempty (AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStratum T)
    rcases T.exposedBoundary_rankThreeFacet_or_codimensionTwo with
      ⟨facet, hthree⟩ | htwo
    · exact ⟨.rankThree facet hthree⟩
    · rcases htwo with ⟨i, j, hij, hi, hj⟩
      exact ⟨.codimensionTwo i j hij hi hj⟩)

/-- The exposed exponent used by the stratum is literal support of the actual
singular top face. -/
theorem exposedBoundary_exponent_mem_topFace
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.exposedSingularBoundaryVertex.exponent ∈ T.topFace.face.support :=
  T.exposedSingularBoundaryVertex.exponent_mem_source

/-- Hence its ordinary degree is exactly the selected maximal degree. -/
theorem exposedBoundary_exponent_degree_eq_topFace
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HC4.Polynomial.ordinaryDegree4
        T.exposedSingularBoundaryVertex.exponent = T.topFace.degree :=
  T.topFace.face_support_ordinaryDegree_eq
    T.exposedBoundary_exponent_mem_topFace

/-- A rank-three boundary stratum gives the actual nonempty on-facet support
slice needed by finite-support cross-facet exposure. -/
theorem rankThree_zeroCoordinateSupport_nonempty
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree : MvRankThreeOnFacet facet
      T.exposedSingularBoundaryVertex.exponent) :
    (zeroCoordinateSupport
      (HC4.Polynomial.facetOmittedCoordinate facet) T.topFace.face).Nonempty := by
  have hzero :
      T.exposedSingularBoundaryVertex.exponent
        (HC4.Polynomial.facetOmittedCoordinate facet) = 0 := by
    have hcoords :=
      (mvRankThreeOnFacet_iff facet
        T.exposedSingularBoundaryVertex.exponent).1 hthree
    cases facet <;> exact hcoords.1
  exact ⟨T.exposedSingularBoundaryVertex.exponent,
    mem_zeroCoordinateSupport.mpr
      ⟨T.exposedBoundary_exponent_mem_topFace, hzero⟩⟩

/-- A codimension-two boundary stratum gives two genuinely distinct nonempty
coordinate-boundary support slices of the same actual top face. -/
theorem codimensionTwo_zeroCoordinateSupports_nonempty
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i j : Fin 4)
    (hij : i ≠ j)
    (hi : T.exposedSingularBoundaryVertex.exponent i = 0)
    (hj : T.exposedSingularBoundaryVertex.exponent j = 0) :
    i ≠ j ∧
      (zeroCoordinateSupport i T.topFace.face).Nonempty ∧
      (zeroCoordinateSupport j T.topFace.face).Nonempty := by
  refine ⟨hij, ?_, ?_⟩
  · exact ⟨T.exposedSingularBoundaryVertex.exponent,
      mem_zeroCoordinateSupport.mpr
        ⟨T.exposedBoundary_exponent_mem_topFace, hi⟩⟩
  · exact ⟨T.exposedSingularBoundaryVertex.exponent,
      mem_zeroCoordinateSupport.mpr
        ⟨T.exposedBoundary_exponent_mem_topFace, hj⟩⟩

/-- Assembly-facing exhaustive finite-support boundary frontier. -/
theorem finiteSupportBoundaryStrata
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (∃ facet : ToricFacet,
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent ∧
          (zeroCoordinateSupport
            (HC4.Polynomial.facetOmittedCoordinate facet)
            T.topFace.face).Nonempty) ∨
      (∃ i j : Fin 4,
        i ≠ j ∧
          T.exposedSingularBoundaryVertex.exponent i = 0 ∧
          T.exposedSingularBoundaryVertex.exponent j = 0 ∧
          (zeroCoordinateSupport i T.topFace.face).Nonempty ∧
          (zeroCoordinateSupport j T.topFace.face).Nonempty) := by
  rcases T.exposedBoundary_rankThreeFacet_or_codimensionTwo with
    ⟨facet, hthree⟩ | htwo
  · exact Or.inl ⟨facet, hthree,
      T.rankThree_zeroCoordinateSupport_nonempty facet hthree⟩
  · rcases htwo with ⟨i, j, hij, hi, hj⟩
    have hs := T.codimensionTwo_zeroCoordinateSupports_nonempty i j hij hi hj
    exact Or.inr ⟨i, j, hij, hi, hj, hs.2.1, hs.2.2⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
