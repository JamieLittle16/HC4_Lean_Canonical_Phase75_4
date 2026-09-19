import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsExposedTopFace
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsRayTerminalReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayBoundary
import Mathlib.Tactic

/-!
# A19.80: collapse the `qs` rank-three branch to genuine lower boundary strata

A19.78 proves that, when the canonically exposed singular top-face vertex is
rank three on `.qs`, the entire maximal ordinary top face is already supported
on `.qs`.  Hence no balance-free cross-facet ray of that top face can exist:
its retained outside exponent has positive coordinate `0`.

A19.73 therefore leaves only the genuine lower first-contact carrier or the
literal coordinate-`0` quadratic square.  For the lower carrier, its retained
ray facet endpoint is either already codimension two, or it is rank three on
`.qs`.  In the latter case A19.76 sends the *actual retained outside endpoint*
to a different rank-three coordinate facet or codimension two.

This is the assembly-facing `qs` closure.  It does not introduce a balance
relation, transport support between carriers, or add a termination measure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A cross-facet ray cannot be supported on a polynomial already confined to
`.qs`, because the ray retains an outside exponent with positive coordinate
`0`. -/
theorem qs_topFace_ray_impossible
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent)
    (R : HC4.Newton.CrossFacetRayData T.topFace.face (0 : Fin 4)) : False := by
  have htop := T.qs_exposed_topFaceOnFacet hthree
  have hon := htop R.outsideExponent (R.support_subset R.outside_mem_face)
  have hz : R.outsideExponent (0 : Fin 4) = 0 := by
    have htoric :=
      (HC4.Polynomial.onFacet_toToricExponent_iff .qs R.outsideExponent).1 hon
    simpa [HC4.Polynomial.facetOmittedCoordinate] using htoric
  exact (Nat.ne_of_gt R.outside_coordinate_pos) hz

/-- Boundary outcome retained by the genuine lower first-contact `.qs` ray.
The first alternative records that its starting endpoint was already
codimension two; otherwise the actual outside endpoint has crossed to a new
rank-three facet or codimension two. -/
def QsLowerBoundaryOutcome
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      (K := K) T .qs) : Prop :=
  HC4.Newton.MvExponentOnCodimensionTwoBoundary C.ray.facetExponent ∨
    (∃ next : ToricFacet,
      next ≠ .qs ∧ HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) ∨
    HC4.Newton.MvExponentOnCodimensionTwoBoundary C.ray.outsideExponent

/-- **A19.80 `qs` boundary closure.**  The canonically exposed `.qs`
rank-three branch has no direct top-face ray.  What remains is either a genuine
lower first-contact carrier already reaching a boundary stratum, or the
literal omitted-coordinate quadratic square. -/
theorem qs_rankThree_lowerBoundary_or_quadraticSquare
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ C :
        AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
          (K := K) T .qs,
      QsLowerBoundaryOutcome C) ∨
      (∃ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        HC4.Polynomial.ordinaryDegree4 d = 2 ∧
        d (0 : Fin 4) = 2 ∧
        ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0) := by
  rcases T.qs_rankThree_affineTerminal_or_codimensionTwo_or_quadraticSquare
      hthree with htop | hlower | hsquare
  · rcases htop with ⟨R, _hendpoint⟩
    exact (T.qs_topFace_ray_impossible hthree R).elim
  · rcases hlower with ⟨C, hfacet⟩
    left
    refine ⟨C, ?_⟩
    rcases hfacet with hfacetThree | hfacetTwo
    · rcases C.qs_ray_outside_boundaryTransition hfacetThree with
        houtThree | houtTwo
      · exact Or.inr (Or.inl houtThree)
      · exact Or.inr (Or.inr houtTwo)
    · exact Or.inl hfacetTwo
  · exact Or.inr hsquare



/-- **Strengthened `.qs` boundary closure with no quadratic-square leaf.**

The strict-low comparison contact removes the former low-degree square
exception before the boundary analysis starts.  Hence the canonically exposed
`.qs` rank-three branch always reaches a genuine lower first-contact carrier.
Its retained facet endpoint is either already codimension two, or the actual
outside endpoint crosses to a different rank-three facet / codimension two. -/
theorem qs_rankThree_lowerBoundary
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    ∃ C :
        AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
          (K := K) T .qs,
      QsLowerBoundaryOutcome C := by
  rcases T.qs_rankThree_crossFacet_or_firstNonfacetCrossFacet_or_nonlinearConfined
      hthree with htop | hlower | hconfined
  · rcases htop with ⟨D⟩
    have htopOn := T.qs_exposed_topFaceOnFacet hthree
    have hon := htopOn D.outsideExponent D.outside_mem
    have hz : D.outsideExponent (0 : Fin 4) = 0 := by
      have htoric :=
        (HC4.Polynomial.onFacet_toToricExponent_iff .qs D.outsideExponent).1 hon
      simpa [HC4.Polynomial.facetOmittedCoordinate] using htoric
    exact (Nat.ne_of_gt D.outside_coordinate_pos hz).elim
  · rcases hlower with ⟨C⟩
    refine ⟨C, ?_⟩
    rcases C.ray.zero_terminalCertificate_or_codimensionTwo C.hessian_zero with
      hterminal | htwo
    · have hfacetThree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent :=
        hterminal.1
      rcases C.qs_ray_outside_boundaryTransition hfacetThree with
        houtThree | houtTwo
      · exact Or.inr (Or.inl houtThree)
      · exact Or.inr (Or.inr houtTwo)
    · exact Or.inl htwo
  · rcases T.strictLow_sourceCodimensionTwo_two_le with
      ⟨d, hd, hdeg, hd0, _hcodim⟩
    have hon := hconfined d hd hdeg
    have hz : d (0 : Fin 4) = 0 := by
      have htoric :=
        (HC4.Polynomial.onFacet_toToricExponent_iff .qs d).1 hon
      simpa [HC4.Polynomial.facetOmittedCoordinate] using htoric
    omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
