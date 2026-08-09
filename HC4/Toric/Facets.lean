import HC4.Toric.BranchReversal

/-!
# The four toric facets

The invariant exponent cone has cyclic facets `pr`, `rq`, `qs`, and `sp`.
They are exactly the coordinate hyperplanes omitting respectively
`x₂`, `x₄`, `x₁`, and `x₃`.  This module records the facet predicates,
their behaviour under coordinate reversal, and the normal forms of balanced
exponents lying on each facet.
-/

namespace HC4.Toric

/-- The four cyclic facets of the symmetric invariant cone. -/
inductive ToricFacet where
  | pr | rq | qs | sp
  deriving DecidableEq, Repr

/-- Membership in a toric facet, expressed by the omitted coordinate. -/
def OnFacet : ToricFacet → Exponent → Prop
  | .pr, u => u.x2 = 0
  | .rq, u => u.x4 = 0
  | .qs, u => u.x1 = 0
  | .sp, u => u.x3 = 0

/-- Coordinate reversal exchanges opposite facets. -/
def reverseFacet : ToricFacet → ToricFacet
  | .pr => .sp
  | .rq => .qs
  | .qs => .rq
  | .sp => .pr

@[simp] theorem reverseFacet_involutive (F : ToricFacet) :
    reverseFacet (reverseFacet F) = F := by
  cases F <;> rfl

@[simp] theorem onFacet_reverseExponent_iff (F : ToricFacet) (u : Exponent) :
    OnFacet (reverseFacet F) (reverseExponent u) ↔ OnFacet F u := by
  cases F <;> simp [OnFacet, reverseFacet, reverseExponent]

@[simp] theorem p_on_pr : OnFacet .pr pExponent := rfl
@[simp] theorem p_on_sp : OnFacet .sp pExponent := rfl
@[simp] theorem q_on_rq : OnFacet .rq qExponent := rfl
@[simp] theorem q_on_qs : OnFacet .qs qExponent := rfl
@[simp] theorem r_on_pr (a b : ℕ) : OnFacet .pr (rExponent a b) := rfl
@[simp] theorem r_on_rq (a b : ℕ) : OnFacet .rq (rExponent a b) := rfl
@[simp] theorem s_on_qs (a b : ℕ) : OnFacet .qs (sExponent a b) := rfl
@[simp] theorem s_on_sp (a b : ℕ) : OnFacet .sp (sExponent a b) := rfl

/-- A balanced exponent on the `p-r` facet has the form `p^i r^k`. -/
theorem balanced_on_pr_normal_form
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u) (hF : OnFacet .pr u) :
    ∃ i k : ℕ, u = rBranch a b i 0 k := by
  rcases (balanced_iff_normal_form ha hb hcop).mp hBal with
    ⟨i, j, k, hU⟩ | ⟨i, j, k, hk, hU⟩
  · subst u
    have hj : j = 0 := by simpa [OnFacet, rBranch] using hF
    subst j
    exact ⟨i, k, rfl⟩
  · subst u
    have hzero : j + a * k = 0 := by simpa [OnFacet, sBranch] using hF
    have hpos : 0 < a * k := Nat.mul_pos ha hk
    omega

/-- A balanced exponent on the `r-q` facet has the form `q^j r^k`. -/
theorem balanced_on_rq_normal_form
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u) (hF : OnFacet .rq u) :
    ∃ j k : ℕ, u = rBranch a b 0 j k := by
  rcases (balanced_iff_normal_form ha hb hcop).mp hBal with
    ⟨i, j, k, hU⟩ | ⟨i, j, k, hk, hU⟩
  · subst u
    have hi : i = 0 := by simpa [OnFacet, rBranch] using hF
    subst i
    exact ⟨j, k, rfl⟩
  · subst u
    have hzero : i + b * k = 0 := by simpa [OnFacet, sBranch] using hF
    have hpos : 0 < b * k := Nat.mul_pos hb hk
    omega

/-- A balanced exponent on the `q-s` facet has the form `q^j s^k`. -/
theorem balanced_on_qs_normal_form
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u) (hF : OnFacet .qs u) :
    ∃ j k : ℕ, u = sBranch a b 0 j k := by
  rcases (balanced_iff_normal_form ha hb hcop).mp hBal with
    ⟨i, j, k, hU⟩ | ⟨i, j, k, _hk, hU⟩
  · subst u
    have hzero : i + b * k = 0 := by simpa [OnFacet, rBranch] using hF
    have hi : i = 0 := by omega
    have hk : k = 0 := by
      by_contra hk0
      have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      have : 0 < b * k := Nat.mul_pos hb hkPos
      omega
    subst i
    subst k
    exact ⟨j, 0, by ext <;> simp [rBranch, sBranch]⟩
  · subst u
    have hi : i = 0 := by simpa [OnFacet, sBranch] using hF
    subst i
    exact ⟨j, k, rfl⟩

/-- A balanced exponent on the `s-p` facet has the form `p^i s^k`. -/
theorem balanced_on_sp_normal_form
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u) (hF : OnFacet .sp u) :
    ∃ i k : ℕ, u = sBranch a b i 0 k := by
  rcases (balanced_iff_normal_form ha hb hcop).mp hBal with
    ⟨i, j, k, hU⟩ | ⟨i, j, k, _hk, hU⟩
  · subst u
    have hzero : j + a * k = 0 := by simpa [OnFacet, rBranch] using hF
    have hj : j = 0 := by omega
    have hk : k = 0 := by
      by_contra hk0
      have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      have : 0 < a * k := Nat.mul_pos ha hkPos
      omega
    subst j
    subst k
    exact ⟨i, 0, by ext <;> simp [rBranch, sBranch]⟩
  · subst u
    have hj : j = 0 := by simpa [OnFacet, sBranch] using hF
    subst j
    exact ⟨i, k, rfl⟩

end HC4.Toric
