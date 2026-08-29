import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetDirectionLock
import Mathlib.Tactic

/-!
# A19.95: assemble the locked lower `qs` other-facet frontier

A19.93 leaves a genuine lower `qs` survivor only when its actual outside
endpoint is rank three on a coordinate facet different from `qs`.  A19.94
proves the strict transverse direction lock separately in the three possible
cyclic facets.

This file is the finite assembly seam between those two statements.  It does
not add a new progress measure or a new geometric alternative: it simply
eliminates the abstract `next ≠ .qs` witness and exposes the already-proved
strict proportional drop in the appropriate transverse pair.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The abstract different-facet witness has exactly the three cyclic locked
forms proved in A19.94. -/
theorem qs_ray_otherFacet_strict_directionLock
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    (HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent ∧
      C.ray.facetExponent 2 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 2 ∧
      C.ray.outsideExponent 2 < C.ray.facetExponent 2 ∧
      C.ray.outsideExponent 3 < C.ray.facetExponent 3) ∨
    (HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent ∧
      C.ray.facetExponent 1 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 1 ∧
      C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
      C.ray.outsideExponent 3 < C.ray.facetExponent 3) ∨
    (HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent ∧
      C.ray.facetExponent 1 * C.ray.outsideExponent 2 =
        C.ray.facetExponent 2 * C.ray.outsideExponent 1 ∧
      C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
      C.ray.outsideExponent 2 < C.ray.facetExponent 2) := by
  cases next with
  | pr =>
      exact Or.inl ⟨houtThree,
        C.qs_ray_pr_outside_strict_directionLock hthree houtThree⟩
  | rq =>
      exact Or.inr (Or.inr ⟨houtThree,
        C.qs_ray_rq_outside_strict_directionLock hthree houtThree⟩)
  | qs =>
      exact (hne rfl).elim
  | sp =>
      exact Or.inr (Or.inl ⟨houtThree,
        C.qs_ray_sp_outside_strict_directionLock hthree houtThree⟩)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19.95 locked exposed-`qs` frontier.**  The only non-codimension-two,
non-square lower survivor is now one of the three explicit strict direction
locks from A19.94. -/
theorem qs_rankThree_startCodimensionTwo_or_lockedOtherFacet_or_quadraticSquare
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        (K := K) T .qs,
      HC4.Newton.MvExponentOnCodimensionTwoBoundary C.ray.facetExponent) ∨
    (∃ C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        (K := K) T .qs,
      HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent ∧
      ((HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent ∧
          C.ray.facetExponent 2 * C.ray.outsideExponent 3 =
            C.ray.facetExponent 3 * C.ray.outsideExponent 2 ∧
          C.ray.outsideExponent 2 < C.ray.facetExponent 2 ∧
          C.ray.outsideExponent 3 < C.ray.facetExponent 3) ∨
        (HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent ∧
          C.ray.facetExponent 1 * C.ray.outsideExponent 3 =
            C.ray.facetExponent 3 * C.ray.outsideExponent 1 ∧
          C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
          C.ray.outsideExponent 3 < C.ray.facetExponent 3) ∨
        (HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent ∧
          C.ray.facetExponent 1 * C.ray.outsideExponent 2 =
            C.ray.facetExponent 2 * C.ray.outsideExponent 1 ∧
          C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
          C.ray.outsideExponent 2 < C.ray.facetExponent 2))) ∨
    (∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      HC4.Polynomial.ordinaryDegree4 d = 2 ∧
      d (0 : Fin 4) = 2 ∧
      ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0) := by
  rcases T.qs_rankThree_startCodimensionTwo_or_otherFacet_or_quadraticSquare
      hthree with hstart | hother | hsquare
  · exact Or.inl hstart
  · rcases hother with ⟨C, next, hCthree, hne, hnext⟩
    exact Or.inr (Or.inl ⟨C, hCthree,
      C.qs_ray_otherFacet_strict_directionLock hCthree hne hnext⟩)
  · exact Or.inr (Or.inr hsquare)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
