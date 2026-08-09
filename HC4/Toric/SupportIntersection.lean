import HC4.Toric.SparseEigenSupport

/-!
# Intersection obstruction for opposite branch supports

The positive `r` and positive `s` strata are disjoint.  This module lifts that
fact to arbitrary supports and to sparse polynomial supports.  It also proves
that a nonempty support lying on both an `r` level and an `s` level must have
both levels zero, hence lies in the `p,q` cone.
-/

namespace HC4.Toric

/-- A positive `r` level and a positive `s` level have empty intersection. -/
theorem no_common_positive_r_s_support
    {a b k l : ℕ} (hb : 0 < b) (hl : 0 < l)
    {S : Set Exponent}
    (hR : OnRLevel a b k S) (hS : OnSLevel a b l S) :
    S = ∅ := by
  ext u
  constructor
  · intro hu
    rcases hR u hu with ⟨i, j, huR⟩
    rcases hS u hu with ⟨i', j', huS⟩
    have hEq : rBranch a b i j k = sBranch a b i' j' l := huR.symm.trans huS
    exact False.elim ((rBranch_ne_positive_sBranch hb hl) hEq)
  · simp

/-- On a nonempty common `r`/`s` support, both branch levels are zero. -/
theorem common_r_s_levels_eq_zero
    {a b k l : ℕ} (hb : 0 < b)
    {S : Set Exponent} (hne : S.Nonempty)
    (hR : OnRLevel a b k S) (hS : OnSLevel a b l S) :
    k = 0 ∧ l = 0 := by
  rcases hne with ⟨u, hu⟩
  rcases hR u hu with ⟨i, j, huR⟩
  rcases hS u hu with ⟨i', j', huS⟩
  have hl0 : l = 0 := by
    by_contra hlNe
    have hlPos : 0 < l := Nat.pos_of_ne_zero hlNe
    have hEq : rBranch a b i j k = sBranch a b i' j' l := huR.symm.trans huS
    exact (rBranch_ne_positive_sBranch hb hlPos) hEq
  subst l
  have hs0 : sBranch a b i' j' 0 = rBranch a b i' j' 0 := by
    ext <;> simp [sBranch, rBranch]
  have hEqR : rBranch a b i j k = rBranch a b i' j' 0 :=
    huR.symm.trans (huS.trans hs0)
  have hk0 : k = 0 := (rBranch_parameters_unique hb hEqR).2.2
  exact ⟨hk0, rfl⟩

/-- A nonempty support lying on both branch levels is contained in the `p,q` cone. -/
theorem common_r_s_support_on_pq_cone
    {a b k l : ℕ} (hb : 0 < b)
    {S : Set Exponent} (hne : S.Nonempty)
    (hR : OnRLevel a b k S) (hS : OnSLevel a b l S) :
    OnPQCone S := by
  rcases common_r_s_levels_eq_zero hb hne hR hS with ⟨hk0, _hl0⟩
  subst k
  intro u hu
  rcases hR u hu with ⟨i, j, hU⟩
  refine ⟨i, j, ?_⟩
  rw [hU, rBranch_as_generators]
  ext <;> simp [Exponent.add, Exponent.scale, rExponent]

/-- Sparse version: simultaneous branch support forces both levels to vanish. -/
theorem sparse_common_r_s_levels_eq_zero
    {K : Type*} [Zero K]
    {a b k l : ℕ} (hb : 0 < b)
    {f : SparsePolynomial K} (hne : f.support.Nonempty)
    (hR : SparseOnRLevel a b k f) (hS : SparseOnSLevel a b l f) :
    k = 0 ∧ l = 0 := by
  let S : Set Exponent := ↑f.support
  have hSNonempty : S.Nonempty := by
    rcases hne with ⟨u, hu⟩
    exact ⟨u, hu⟩
  exact common_r_s_levels_eq_zero hb hSNonempty
    (fun u hu => hR u hu) (fun u hu => hS u hu)

/-- Sparse version: simultaneous branch support lies in the `p,q` cone. -/
theorem sparse_common_r_s_support_on_pq_cone
    {K : Type*} [Zero K]
    {a b k l : ℕ} (hb : 0 < b)
    {f : SparsePolynomial K} (hne : f.support.Nonempty)
    (hR : SparseOnRLevel a b k f) (hS : SparseOnSLevel a b l f) :
    SparseOnPQCone f := by
  let S : Set Exponent := ↑f.support
  have hSNonempty : S.Nonempty := by
    rcases hne with ⟨u, hu⟩
    exact ⟨u, hu⟩
  exact common_r_s_support_on_pq_cone hb hSNonempty
    (fun u hu => hR u hu) (fun u hu => hS u hu)

end HC4.Toric
