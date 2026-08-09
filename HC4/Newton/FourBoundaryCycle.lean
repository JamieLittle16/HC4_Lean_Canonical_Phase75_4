import HC4.Newton.FacetCycleClassification

/-!
# Four-sided toric boundary cycles

This is the support-level combinatorial object appearing in the second branch
of the boundary-polygon lemma.  The four edges carry reduced facet labels;
each transition vertex lies in the two incident facets.  The previously
verified toric boundary geometry then forces every transition onto the
corresponding extreme ray.
-/

namespace HC4.Newton

open HC4.Toric

/-- A reduced four-sided boundary cycle in the symmetric invariant cone.
`u0` lies between the edges labelled `F3` and `F0`, etc. -/
structure FourBoundaryCycle (a b : ℕ) where
  F0 : ToricFacet
  F1 : ToricFacet
  F2 : ToricFacet
  F3 : ToricFacet
  u0 : Exponent
  u1 : Exponent
  u2 : Exponent
  u3 : Exponent
  adj01 : AdjacentFacets F0 F1
  adj12 : AdjacentFacets F1 F2
  adj23 : AdjacentFacets F2 F3
  adj30 : AdjacentFacets F3 F0
  nonback02 : F0 ≠ F2
  nonback13 : F1 ≠ F3
  bal0 : Balanced a b u0
  bal1 : Balanced a b u1
  bal2 : Balanced a b u2
  bal3 : Balanced a b u3
  u0_left : OnFacet F3 u0
  u0_right : OnFacet F0 u0
  u1_left : OnFacet F0 u1
  u1_right : OnFacet F1 u1
  u2_left : OnFacet F1 u2
  u2_right : OnFacet F2 u2
  u3_left : OnFacet F2 u3
  u3_right : OnFacet F3 u3

/-- The facet labels of a reduced four-sided boundary cycle are necessarily
one of the two cyclic orientations of `pr,rq,qs,sp`, up to rotation. -/
theorem FourBoundaryCycle.facet_normal_form
    {a b : ℕ} (C : FourBoundaryCycle a b) :
    IsCanonicalFourFacetCycle C.F0 C.F1 C.F2 C.F3 := by
  exact four_facet_cycle_normal_form
    C.adj01 C.adj12 C.adj23 C.adj30 C.nonback02 C.nonback13

/-- Every transition vertex of a four-sided boundary cycle lies on its
corresponding extreme ray. -/
theorem FourBoundaryCycle.vertices_on_transition_rays
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (C : FourBoundaryCycle a b) :
    OnRay a b C.F3 C.F0 C.u0 ∧
    OnRay a b C.F0 C.F1 C.u1 ∧
    OnRay a b C.F1 C.F2 C.u2 ∧
    OnRay a b C.F2 C.F3 C.u3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact adjacent_transition_on_extreme_ray ha hb hcop C.adj30
      C.bal0 C.u0_left C.u0_right
  · exact adjacent_transition_on_extreme_ray ha hb hcop C.adj01
      C.bal1 C.u1_left C.u1_right
  · exact adjacent_transition_on_extreme_ray ha hb hcop C.adj12
      C.bal2 C.u2_left C.u2_right
  · exact adjacent_transition_on_extreme_ray ha hb hcop C.adj23
      C.bal3 C.u3_left C.u3_right

/-- In the forward canonical orientation, the transition vertices are
respectively on the pure rays `p,r,q,s`. -/
theorem FourBoundaryCycle.forward_vertices_are_p_r_q_s
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (C : FourBoundaryCycle a b)
    (h0 : C.F0 = .pr) (h1 : C.F1 = .rq)
    (h2 : C.F2 = .qs) (h3 : C.F3 = .sp) :
    (∃ A : ℕ, C.u0 = Exponent.scale A pExponent) ∧
    (∃ B : ℕ, C.u1 = Exponent.scale B (rExponent a b)) ∧
    (∃ D : ℕ, C.u2 = Exponent.scale D qExponent) ∧
    (∃ E : ℕ, C.u3 = Exponent.scale E (sExponent a b)) := by
  have hRays := C.vertices_on_transition_rays ha hb hcop
  rw [h0, h1, h2, h3] at hRays
  simpa [OnRay] using hRays

end HC4.Newton
