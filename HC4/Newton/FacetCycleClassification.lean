import HC4.Newton.BoundaryCycle

/-!
# The reduced facet-cycle combinatorics

The four toric facets form a 4-cycle.  This file isolates the finite
combinatorial content of the manuscript's boundary-polygon lemma:

* there is no reduced three-facet cycle;
* a reduced four-facet cycle is, up to cyclic rotation and reversal, exactly
  `pr -> rq -> qs -> sp -> pr`.

The genuinely convex-geometric step saying that a two-dimensional Newton
polygon whose edges lie in cone facets reduces to such a facet cycle is kept
separate.  No geometric assumption is hidden in this module.
-/

namespace HC4.Newton

open HC4.Toric

/-- The eight cyclic orientations of the four toric facets. -/
def IsCanonicalFourFacetCycle
    (F0 F1 F2 F3 : ToricFacet) : Prop :=
  (F0 = .pr ∧ F1 = .rq ∧ F2 = .qs ∧ F3 = .sp) ∨
  (F0 = .rq ∧ F1 = .qs ∧ F2 = .sp ∧ F3 = .pr) ∨
  (F0 = .qs ∧ F1 = .sp ∧ F2 = .pr ∧ F3 = .rq) ∨
  (F0 = .sp ∧ F1 = .pr ∧ F2 = .rq ∧ F3 = .qs) ∨
  (F0 = .pr ∧ F1 = .sp ∧ F2 = .qs ∧ F3 = .rq) ∨
  (F0 = .sp ∧ F1 = .qs ∧ F2 = .rq ∧ F3 = .pr) ∨
  (F0 = .qs ∧ F1 = .rq ∧ F2 = .pr ∧ F3 = .sp) ∨
  (F0 = .rq ∧ F1 = .pr ∧ F2 = .sp ∧ F3 = .qs)

/-- Adjacency of toric facets is symmetric. -/
theorem adjacentFacets_comm {F G : ToricFacet} :
    AdjacentFacets F G ↔ AdjacentFacets G F := by
  cases F <;> cases G <;> simp [AdjacentFacets, OppositeFacets]

/-- The facet adjacency graph is a square, so it has no triangle. -/
theorem no_three_facet_cycle
    {F0 F1 F2 : ToricFacet}
    (h01 : AdjacentFacets F0 F1)
    (h12 : AdjacentFacets F1 F2)
    (h20 : AdjacentFacets F2 F0) : False := by
  cases F0 <;> cases F1 <;> cases F2 <;>
    simp [AdjacentFacets, OppositeFacets] at h01 h12 h20

/-- A reduced four-edge walk in the facet adjacency graph must be the full
cyclic four-facet boundary, up to rotation and reversal.  The two extra
nonrepetition hypotheses are exactly what rules out immediate backtracking. -/
theorem four_facet_cycle_normal_form
    {F0 F1 F2 F3 : ToricFacet}
    (h01 : AdjacentFacets F0 F1)
    (h12 : AdjacentFacets F1 F2)
    (h23 : AdjacentFacets F2 F3)
    (h30 : AdjacentFacets F3 F0)
    (h02 : F0 ≠ F2)
    (h13 : F1 ≠ F3) :
    IsCanonicalFourFacetCycle F0 F1 F2 F3 := by
  cases F0 <;> cases F1 <;> cases F2 <;> cases F3 <;>
    simp_all [AdjacentFacets, OppositeFacets, IsCanonicalFourFacetCycle]

/-- Every canonical four-facet cycle uses four distinct facets. -/
theorem canonical_four_facet_cycle_pairwise_distinct
    {F0 F1 F2 F3 : ToricFacet}
    (h : IsCanonicalFourFacetCycle F0 F1 F2 F3) :
    F0 ≠ F1 ∧ F0 ≠ F2 ∧ F0 ≠ F3 ∧
    F1 ≠ F2 ∧ F1 ≠ F3 ∧ F2 ≠ F3 := by
  rcases h with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;> decide

end HC4.Newton
