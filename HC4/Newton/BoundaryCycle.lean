import HC4.Toric.BoundaryGeometry

/-!
# Cyclic facet transitions

A compact combinatorial layer for the boundary-polygon proof.  It records
that a nonzero balanced boundary point cannot lie in opposite facets and that
transitions between distinct admissible facet labels occur on the expected
extreme ray.
-/

namespace HC4.Newton

open HC4.Toric

/-- Two distinct toric facets are adjacent exactly when they are not opposite. -/
def AdjacentFacets (F G : ToricFacet) : Prop :=
  F ≠ G ∧ ¬ OppositeFacets F G

/-- Distinct facets through a nonzero balanced exponent must be adjacent. -/
theorem facets_adjacent_of_common_nonzero
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {F G : ToricFacet} (hFG : F ≠ G)
    {u : Exponent} (hu0 : u ≠ originExponent)
    (hBal : Balanced a b u) (hF : OnFacet F u) (hG : OnFacet G u) :
    AdjacentFacets F G := by
  refine ⟨hFG, ?_⟩
  intro hOpp
  apply hu0
  exact opposite_facets_intersection_origin ha hb hOpp hBal hF hG

/-- Every adjacent boundary transition lies on one of the four extreme rays. -/
theorem adjacent_transition_on_extreme_ray
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {F G : ToricFacet} (hAdj : AdjacentFacets F G)
    {u : Exponent} (hBal : Balanced a b u)
    (hF : OnFacet F u) (hG : OnFacet G u) :
    OnRay a b F G u := by
  rcases hAdj with ⟨hne, hnopp⟩
  cases F <;> cases G <;>
    simp [AdjacentFacets, OppositeFacets, OnRay] at hne hnopp ⊢
  · exact on_r_ray_of_pr_rq ha hb hcop hBal hF hG
  · exact on_p_ray_of_pr_sp ha hb hBal hF hG
  · exact on_r_ray_of_pr_rq ha hb hcop hBal hG hF
  · exact on_q_ray_of_rq_qs ha hb hBal hF hG
  · exact on_q_ray_of_rq_qs ha hb hBal hG hF
  · exact on_s_ray_of_qs_sp ha hb hcop hBal hF hG
  · exact on_p_ray_of_pr_sp ha hb hBal hG hF
  · exact on_s_ray_of_qs_sp ha hb hcop hBal hG hF

end HC4.Newton
