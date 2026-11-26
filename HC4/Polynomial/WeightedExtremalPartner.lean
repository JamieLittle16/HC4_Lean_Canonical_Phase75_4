module

public import HC4.Polynomial.WeightedExtremalSplitRow

/-!
# Weight-partner restrictions on genuine counterexamples

The full-source split-row theorem is invariant under relabelling.
A high-weight coordinate of a counterexample must have at least
two distinct other coordinates with weight sum at most the cap.
Moreover two coordinates cannot both have weight greater than
half the cap at a positive-clock global optimum.

These restrictions concern the actual source, not just its
singular leading Hessian.
-/

public section

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Split-row terminal with arbitrary distinct coordinate placement. -/
theorem gradient_injective_of_splitRow
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K) (hdet : hessianDeterminant P = 1)
    (j k : Fin 4) (hjk : j ≠ k)
    (hrow : ∀ i : Fin 4, i ≠ k → hessian P j i = 0) :
    Function.Injective (mvGradientMap P) := by
  classical
  let s : Equiv.Perm (Fin 4) := Equiv.swap k 0
  let rho : Equiv.Perm (Fin 4) := s.trans (Equiv.swap (s j) 3)
  have hs0 : s k = 0 := Equiv.swap_apply_left _ _
  have hsj : s j ≠ 0 := by
    intro h
    exact hjk (s.injective (h.trans hs0.symm))
  have hk : rho k = 0 := by
    change Equiv.swap (s j) 3 (s k) = 0
    rw [hs0, Equiv.swap_apply_of_ne_of_ne (Ne.symm hsj) (by decide : (0 : Fin 4) ≠ 3)]
  have hj : rho j = 3 := by
    change Equiv.swap (s j) 3 (s j) = 3
    exact Equiv.swap_apply_left _ _
  have hk' : rho.symm 0 = k := by rw [← hk, rho.symm_apply_apply]
  have hj' : rho.symm 3 = j := by rw [← hj, rho.symm_apply_apply]
  apply mvGradientMap_injective_of_rename_perm rho P
  apply gradient_injective_of_splitRow_standard hJC2
  · rw [hessianDeterminant_rename_perm, hdet, map_one]
  · intro i hi
    rw [hessian_rename_perm]
    change rename rho (hessian P (rho.symm 3) (rho.symm i)) = 0
    rw [hj']
    have hne : rho.symm i ≠ k := by
      intro he
      exact hi (rho.symm.injective (he.trans hk'.symm))
    rw [hrow _ hne, map_zero]

/-- The entire Hessian row cannot vanish. A nonzero determinant
therefore forces a partner of complementary or lower weight. -/
theorem weightCap_exists_partner
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hcap : IsWeightLE w m P)
    (hdet : hessianDeterminant P = 1) (j : Fin 4) :
    ∃ k : Fin 4, w j + w k ≤ m := by
  classical
  by_contra hn
  push_neg at hn
  have hzero (i : Fin 4) : hessian P i j = 0 :=
    eq_zero_of_nonnegativeWeight_negative_cap w hw _
      (by have h := hn i; omega) _ (hcap.hessian_entry i j)
  exact one_ne_zero (hdet.symm.trans (Matrix.det_eq_zero_of_column_eq_zero j hzero))

/-- In particular all coordinate weights are at most the cap. -/
theorem weightCap_coordinate_le
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hcap : IsWeightLE w m P)
    (hdet : hessianDeterminant P = 1) (j : Fin 4) :
    w j ≤ m := by
  obtain ⟨k,hk⟩ := weightCap_exists_partner P w m hw hcap hdet j
  have h := hw k
  omega

/-- A coordinate above half the cap must have at least two
different possible partners in a genuine counterexample. -/
theorem counterexample_highWeight_two_partners
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hcap : IsWeightLE w m P)
    (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (j : Fin 4) (hj : m < 2*w j) :
    ∃ k l : Fin 4, k ≠ l ∧ k ≠ j ∧ l ≠ j ∧
      w j + w k ≤ m ∧ w j + w l ≤ m := by
  classical
  obtain ⟨k,hk⟩ := weightCap_exists_partner P w m hw hcap hdet j
  have hjk : j ≠ k := by
    intro he
    rw [← he] at hk
    omega
  by_contra hn
  have hrow (i : Fin 4) (hi : i ≠ k) : hessian P j i = 0 := by
    apply eq_zero_of_nonnegativeWeight_negative_cap w hw _ ?_ _ (hcap.hessian_entry j i)
    by_contra h
    have hwi : w j + w i ≤ m := by omega
    have hij : i ≠ j := by
      intro he
      rw [he] at hwi
      omega
    exact hn ⟨k,i,Ne.symm hi,Ne.symm hjk,hij,hk,hwi⟩
  exact hnoninj (gradient_injective_of_splitRow hJC2 P hdet j k hjk hrow)

/-- Two weights above half the cap would force a zero principal
plane, contradicting the signed-slope obstruction. -/
theorem globalWeightOptimum_atMostOne_highWeight
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ k, 0 ≤ w k) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ k, w k))
    (hopt : IsGlobalWeightOptimum P w m)
    (i j : Fin 4) (hi : m < 2*w i) (hj : m < 2*w j) :
    i = j := by
  classical
  by_contra hij
  let L := initialForm w m P
  have hL : IsWeightLE w m L :=
    isWeightLE_of_isWeightedHomogeneous (initialForm_isWeightedHomogeneous w m P)
  have hz (a b : Fin 4) (h : m < w a + w b) : hessian L a b = 0 :=
    eq_zero_of_nonnegativeWeight_negative_cap w hw _ (by omega) _ (hL.hessian_entry a b)
  obtain ⟨u,hu,hgt⟩ := globalWeightOptimum_no_jointlyAffine_support P w m
    hw hm hcap hclock hopt i j
  have hle := extremal_jointlyAffine_support_of_hessian_zero L i j hij
    (hz i i (by omega)) (hz j j (by omega)) (hz i j (by omega)) u hu
  omega

/-- A counterexample with a cap-weight
coordinate must have at least two distinct zero weights. -/
theorem counterexample_capWeight_two_zeros
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (j : Fin 4) (hj : w j = m) :
    ∃ k l : Fin 4, k ≠ l ∧ w k = 0 ∧ w l = 0 := by
  obtain ⟨k,l,hkl,_,_,hk,hl⟩ := counterexample_highWeight_two_partners
    hJC2 P w m hw hcap hdet hnoninj j (by omega)
  have hk0 := hw k
  have hl0 := hw l
  exact ⟨k,l,hkl,by omega,by omega⟩

end
end HC4.Polynomial

#print axioms HC4.Polynomial.counterexample_highWeight_two_partners
#print axioms HC4.Polynomial.globalWeightOptimum_atMostOne_highWeight
#print axioms HC4.Polynomial.counterexample_capWeight_two_zeros
