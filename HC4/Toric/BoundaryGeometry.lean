import HC4.Toric.Facets

/-!
# Boundary geometry of the symmetric invariant cone

This module packages the exact facet-intersection facts used in the boundary
polygon argument.  Opposite facets meet only at the origin; adjacent facets
meet on one of the four extreme rays.
-/

namespace HC4.Toric

/-- The origin exponent. -/
def originExponent : Exponent := ⟨0, 0, 0, 0⟩

/-- A nonnegative multiple of one of the four toric ray generators. -/
def OnRay (a b : ℕ) : ToricFacet → ToricFacet → Exponent → Prop
  | .pr, .sp, u => ∃ n : ℕ, u = Exponent.scale n pExponent
  | .sp, .pr, u => ∃ n : ℕ, u = Exponent.scale n pExponent
  | .pr, .rq, u => ∃ n : ℕ, u = Exponent.scale n (rExponent a b)
  | .rq, .pr, u => ∃ n : ℕ, u = Exponent.scale n (rExponent a b)
  | .rq, .qs, u => ∃ n : ℕ, u = Exponent.scale n qExponent
  | .qs, .rq, u => ∃ n : ℕ, u = Exponent.scale n qExponent
  | .qs, .sp, u => ∃ n : ℕ, u = Exponent.scale n (sExponent a b)
  | .sp, .qs, u => ∃ n : ℕ, u = Exponent.scale n (sExponent a b)
  | _, _, _ => False

/-- The two pairs of nonadjacent/opposite facets. -/
def OppositeFacets : ToricFacet → ToricFacet → Prop
  | .pr, .qs => True
  | .qs, .pr => True
  | .rq, .sp => True
  | .sp, .rq => True
  | _, _ => False

/-- Opposite facets contain no nonzero balanced exponent. -/
theorem opposite_facets_intersection_origin
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {F G : ToricFacet} (hOpp : OppositeFacets F G)
    {u : Exponent} (hBal : Balanced a b u)
    (hF : OnFacet F u) (hG : OnFacet G u) :
    u = originExponent := by
  cases F <;> cases G <;> simp [OppositeFacets] at hOpp
  · rcases u with ⟨u1,u2,u3,u4⟩
    simp [OnFacet] at hF hG
    subst u2
    subst u1
    simp [Balanced] at hBal
    have hu3 : u3 = 0 := by
      by_contra hne
      have hu3pos : 0 < u3 := Nat.pos_of_ne_zero hne
      have hprod : 0 < b * u3 := Nat.mul_pos hb hu3pos
      omega
    have hu4 : u4 = 0 := by
      by_contra hne
      have hu4pos : 0 < u4 := Nat.pos_of_ne_zero hne
      have hprod : 0 < a * u4 := Nat.mul_pos ha hu4pos
      omega
    subst u3
    subst u4
    rfl
  · rcases u with ⟨u1,u2,u3,u4⟩
    simp [OnFacet] at hF hG
    subst u4
    subst u3
    simp [Balanced] at hBal
    have hu1 : u1 = 0 := by
      by_contra hne
      have hu1pos : 0 < u1 := Nat.pos_of_ne_zero hne
      have hprod : 0 < a * u1 := Nat.mul_pos ha hu1pos
      omega
    have hu2 : u2 = 0 := by
      by_contra hne
      have hu2pos : 0 < u2 := Nat.pos_of_ne_zero hne
      have hprod : 0 < b * u2 := Nat.mul_pos hb hu2pos
      omega
    subst u1
    subst u2
    rfl
  · rcases u with ⟨u1,u2,u3,u4⟩
    simp [OnFacet] at hF hG
    subst u1
    subst u2
    simp [Balanced] at hBal
    have hu3 : u3 = 0 := by
      by_contra hne
      have hu3pos : 0 < u3 := Nat.pos_of_ne_zero hne
      have hprod : 0 < b * u3 := Nat.mul_pos hb hu3pos
      omega
    have hu4 : u4 = 0 := by
      by_contra hne
      have hu4pos : 0 < u4 := Nat.pos_of_ne_zero hne
      have hprod : 0 < a * u4 := Nat.mul_pos ha hu4pos
      omega
    subst u3
    subst u4
    rfl
  · rcases u with ⟨u1,u2,u3,u4⟩
    simp [OnFacet] at hF hG
    subst u3
    subst u4
    simp [Balanced] at hBal
    have hu1 : u1 = 0 := by
      by_contra hne
      have hu1pos : 0 < u1 := Nat.pos_of_ne_zero hne
      have hprod : 0 < a * u1 := Nat.mul_pos ha hu1pos
      omega
    have hu2 : u2 = 0 := by
      by_contra hne
      have hu2pos : 0 < u2 := Nat.pos_of_ne_zero hne
      have hprod : 0 < b * u2 := Nat.mul_pos hb hu2pos
      omega
    subst u1
    subst u2
    rfl

/-- The `pr ∩ sp` boundary transition is the `p` ray. -/
theorem on_p_ray_of_pr_sp
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {u : Exponent} (hBal : Balanced a b u)
    (hpr : OnFacet .pr u) (hsp : OnFacet .sp u) :
    ∃ n : ℕ, u = Exponent.scale n pExponent := by
  rcases u with ⟨u1,u2,u3,u4⟩
  simp [OnFacet] at hpr hsp
  simp [Balanced] at hBal
  subst u2
  subst u3
  have hBal' : a * u1 = a * u4 := by simpa using hBal
  have : u1 = u4 := Nat.mul_left_cancel ha hBal'
  subst u4
  exact ⟨u1, by ext <;> simp [Exponent.scale, pExponent]⟩

/-- The `pr ∩ rq` boundary transition is the `r` ray. -/
theorem on_r_ray_of_pr_rq
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u)
    (hpr : OnFacet .pr u) (hrq : OnFacet .rq u) :
    ∃ n : ℕ, u = Exponent.scale n (rExponent a b) := by
  rcases balanced_on_pr_normal_form ha hb hcop hBal hpr with ⟨i,k,hU⟩
  subst u
  have hi : i = 0 := by simpa [OnFacet, rBranch] using hrq
  subst i
  exact ⟨k, by ext <;> simp [Exponent.scale, rExponent, rBranch, Nat.mul_comm]⟩

/-- The `rq ∩ qs` boundary transition is the `q` ray. -/
theorem on_q_ray_of_rq_qs
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {u : Exponent} (hBal : Balanced a b u)
    (hrq : OnFacet .rq u) (hqs : OnFacet .qs u) :
    ∃ n : ℕ, u = Exponent.scale n qExponent := by
  rcases u with ⟨u1,u2,u3,u4⟩
  simp [OnFacet] at hrq hqs
  simp [Balanced] at hBal
  subst u4
  subst u1
  have hBal' : b * u2 = b * u3 := by simpa using hBal
  have : u2 = u3 := Nat.mul_left_cancel hb hBal'
  subst u3
  exact ⟨u2, by ext <;> simp [Exponent.scale, qExponent]⟩

/-- The `qs ∩ sp` boundary transition is the `s` ray. -/
theorem on_s_ray_of_qs_sp
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u)
    (hqs : OnFacet .qs u) (hsp : OnFacet .sp u) :
    ∃ n : ℕ, u = Exponent.scale n (sExponent a b) := by
  rcases balanced_on_qs_normal_form ha hb hcop hBal hqs with ⟨j,k,hU⟩
  subst u
  have hj : j = 0 := by simpa [OnFacet, sBranch] using hsp
  subst j
  exact ⟨k, by ext <;> simp [Exponent.scale, sExponent, sBranch, Nat.mul_comm]⟩

end HC4.Toric
