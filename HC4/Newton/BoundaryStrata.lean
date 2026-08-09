import HC4.Newton.BoundaryCycle

/-!
# Boundary strata of the symmetric toric cone

A nonzero balanced exponent on a toric facet is either in the relative
interior of that facet (hence a rank-three monomial exponent), or it lies on
one of the two extreme rays bounding the facet.

This is the endpoint classification used in the Newton-edge elimination:
once an exposed zero-Hessian edge has boundary vertices, each endpoint is
rank three or pure-ray.  The later rank-three and complementary-edge
obstructions can therefore cover all non-facet edges.
-/

namespace HC4.Newton

open HC4.Toric

/-- A boundary exponent in the relative interior of one toric facet.  In
four variables this is exactly a monomial omitting one coordinate and using
the other three with positive exponent. -/
def RankThreeOnFacet : ToricFacet → Exponent → Prop
  | .pr, u => u.x2 = 0 ∧ 0 < u.x1 ∧ 0 < u.x3 ∧ 0 < u.x4
  | .rq, u => u.x4 = 0 ∧ 0 < u.x1 ∧ 0 < u.x2 ∧ 0 < u.x3
  | .qs, u => u.x1 = 0 ∧ 0 < u.x2 ∧ 0 < u.x3 ∧ 0 < u.x4
  | .sp, u => u.x3 = 0 ∧ 0 < u.x1 ∧ 0 < u.x2 ∧ 0 < u.x4

/-- A balanced point of a fixed facet is either rank three in that facet or
lies on one of its two bounding extreme rays. -/
theorem rankThree_or_transitionRay_of_onFacet
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {F : ToricFacet} {u : Exponent}
    (hBal : Balanced a b u) (hF : OnFacet F u) :
    RankThreeOnFacet F u ∨
      ∃ G : ToricFacet, AdjacentFacets F G ∧ OnRay a b F G u := by
  cases F with
  | pr =>
      rcases balanced_on_pr_normal_form ha hb hcop hBal hF with ⟨i, k, rfl⟩
      by_cases hi : i = 0
      · subst i
        right
        refine ⟨.rq, ?_, ?_⟩
        · simp [AdjacentFacets, OppositeFacets]
        · exact ⟨k, by ext <;> simp [OnRay, Exponent.scale, rExponent,
            rBranch, Nat.mul_comm]⟩
      · by_cases hk : k = 0
        · subst k
          right
          refine ⟨.sp, ?_, ?_⟩
          · simp [AdjacentFacets, OppositeFacets]
          · exact ⟨i, by ext <;> simp [OnRay, Exponent.scale, pExponent,
              rBranch]⟩
        · left
          have hip : 0 < i := Nat.pos_of_ne_zero hi
          have hkp : 0 < k := Nat.pos_of_ne_zero hk
          have hbk : 0 < b * k := Nat.mul_pos hb hkp
          have hak : 0 < a * k := Nat.mul_pos ha hkp
          simp [RankThreeOnFacet, rBranch, hip, hbk, hak]
  | rq =>
      rcases balanced_on_rq_normal_form ha hb hcop hBal hF with ⟨j, k, rfl⟩
      by_cases hj : j = 0
      · subst j
        right
        refine ⟨.pr, ?_, ?_⟩
        · simp [AdjacentFacets, OppositeFacets]
        · exact ⟨k, by ext <;> simp [OnRay, Exponent.scale, rExponent,
            rBranch, Nat.mul_comm]⟩
      · by_cases hk : k = 0
        · subst k
          right
          refine ⟨.qs, ?_, ?_⟩
          · simp [AdjacentFacets, OppositeFacets]
          · exact ⟨j, by ext <;> simp [OnRay, Exponent.scale, qExponent,
              rBranch]⟩
        · left
          have hjp : 0 < j := Nat.pos_of_ne_zero hj
          have hkp : 0 < k := Nat.pos_of_ne_zero hk
          have hbk : 0 < b * k := Nat.mul_pos hb hkp
          have hak : 0 < a * k := Nat.mul_pos ha hkp
          simp [RankThreeOnFacet, rBranch, hjp, hbk, hak]
  | qs =>
      rcases balanced_on_qs_normal_form ha hb hcop hBal hF with ⟨j, k, rfl⟩
      by_cases hj : j = 0
      · subst j
        right
        refine ⟨.sp, ?_, ?_⟩
        · simp [AdjacentFacets, OppositeFacets]
        · exact ⟨k, by ext <;> simp [OnRay, Exponent.scale, sExponent,
            sBranch, Nat.mul_comm]⟩
      · by_cases hk : k = 0
        · subst k
          right
          refine ⟨.rq, ?_, ?_⟩
          · simp [AdjacentFacets, OppositeFacets]
          · exact ⟨j, by ext <;> simp [OnRay, Exponent.scale, qExponent,
              sBranch]⟩
        · left
          have hjp : 0 < j := Nat.pos_of_ne_zero hj
          have hkp : 0 < k := Nat.pos_of_ne_zero hk
          have hbk : 0 < b * k := Nat.mul_pos hb hkp
          have hak : 0 < a * k := Nat.mul_pos ha hkp
          simp [RankThreeOnFacet, sBranch, hjp, hbk, hak]
  | sp =>
      rcases balanced_on_sp_normal_form ha hb hcop hBal hF with ⟨i, k, rfl⟩
      by_cases hi : i = 0
      · subst i
        right
        refine ⟨.qs, ?_, ?_⟩
        · simp [AdjacentFacets, OppositeFacets]
        · exact ⟨k, by ext <;> simp [OnRay, Exponent.scale, sExponent,
            sBranch, Nat.mul_comm]⟩
      · by_cases hk : k = 0
        · subst k
          right
          refine ⟨.pr, ?_, ?_⟩
          · simp [AdjacentFacets, OppositeFacets]
          · exact ⟨i, by ext <;> simp [OnRay, Exponent.scale, pExponent,
              sBranch]⟩
        · left
          have hip : 0 < i := Nat.pos_of_ne_zero hi
          have hkp : 0 < k := Nat.pos_of_ne_zero hk
          have hbk : 0 < b * k := Nat.mul_pos hb hkp
          have hak : 0 < a * k := Nat.mul_pos ha hkp
          simp [RankThreeOnFacet, sBranch, hip, hbk, hak]

/-- Any balanced boundary exponent is rank three on some facet or lies on an
extreme ray. -/
theorem boundary_rankThree_or_extremeRay
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u)
    (hbdry : ∃ F : ToricFacet, OnFacet F u) :
    (∃ F : ToricFacet, RankThreeOnFacet F u) ∨
      (∃ F G : ToricFacet, AdjacentFacets F G ∧ OnRay a b F G u) := by
  rcases hbdry with ⟨F, hF⟩
  rcases rankThree_or_transitionRay_of_onFacet ha hb hcop hBal hF with h | h
  · exact Or.inl ⟨F, h⟩
  · rcases h with ⟨G, hAdj, hRay⟩
    exact Or.inr ⟨F, G, hAdj, hRay⟩

end HC4.Newton
