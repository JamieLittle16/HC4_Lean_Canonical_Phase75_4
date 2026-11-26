import HC4.Polynomial.WeightedWallAnnihilator

/-!
# Positive-weight zero-clock endpoint

When the maximal possible Hessian determinant weight is zero,
the leading Hessian has the same nonzero constant determinant as
the full source. At the origin its matrix is invertible and has
support only between complementary weight blocks.

A collision is impossible: select the least weight of a differing
coordinate. In the complementary gradient rows the difference is
exactly the leading linear Hessian applied to that weight block.
All other rows of that matrix kill the block by weight support.

This proves injectivity directly, without polynomial inverse
construction or an assumption of planar JC2.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

private theorem positiveWeight_nonneg
    (w : σ → ℤ) (hw : ∀ i, 0 < w i) (u : σ →₀ ℕ) :
    0 ≤ Finsupp.weight w u := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro i _
  exact nsmul_nonneg (le_of_lt (hw i)) _

private theorem positiveWeight_pos_of_ne_zero
    (w : σ → ℤ) (hw : ∀ i, 0 < w i) (u : σ →₀ ℕ) (hu : u ≠ 0) :
    0 < Finsupp.weight w u := by
  classical
  have hex : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  let v := u - Finsupp.single i 1
  have hv : v + Finsupp.single i 1 = u :=
    Finsupp.sub_add_single_one_cancel hi
  have he := congrArg (Finsupp.weight w) hv
  rw [map_add, Finsupp.weight_single, one_smul] at he
  have hn := positiveWeight_nonneg w hw v
  have hp := hw i
  omega

/-- A monomial of weight at most s involving a variable of weight
at least s is exactly that single variable, of weight s. -/
private theorem positiveWeight_high_variable
    (w : σ → ℤ) (hw : ∀ i, 0 < w i) (s : ℤ)
    (u : σ →₀ ℕ) (hu : Finsupp.weight w u ≤ s)
    (i : σ) (hi : u i ≠ 0) (hwi : s ≤ w i) :
    u = Finsupp.single i 1 ∧ w i = s := by
  let v := u - Finsupp.single i 1
  have hv : v + Finsupp.single i 1 = u :=
    Finsupp.sub_add_single_one_cancel hi
  have he := congrArg (Finsupp.weight w) hv
  rw [map_add, Finsupp.weight_single, one_smul] at he
  have hn := positiveWeight_nonneg w hw v
  have hv0 : v = 0 := by
    by_contra h
    have hp := positiveWeight_pos_of_ne_zero w hw v h
    omega
  rw [hv0, zero_add] at hv
  refine ⟨hv.symm, ?_⟩
  omega

/-- At the first weight block at which two points differ, the
evaluation difference of a bounded polynomial is its linear part
on that block. -/
theorem eval_sub_eq_weightBlock_linear
    (w : σ → ℤ) (hw : ∀ i, 0 < w i) (s : ℤ)
    (q : MvPolynomial σ K) (hq : IsWeightLE w s q)
    (x y : σ → K) (hxy : ∀ i, w i < s → x i = y i) :
    MvPolynomial.eval x q - MvPolynomial.eval y q =
      ∑ i : σ, coeff (Finsupp.single i 1) q *
        (if w i = s then x i - y i else 0) := by
  classical
  let v : σ → K := fun i => if w i = s then x i - y i else 0
  have hmono (u : σ →₀ ℕ) (hu : u ∈ q.support) :
      MvPolynomial.eval x (monomial u (coeff u q)) -
        MvPolynomial.eval y (monomial u (coeff u q)) =
      ∑ i : σ, coeff (Finsupp.single i 1) (monomial u (coeff u q)) * v i := by
    by_cases h : ∃ i, u i ≠ 0 ∧ s ≤ w i
    · obtain ⟨i, hi, hwi⟩ := h
      obtain ⟨he, hwis⟩ := positiveWeight_high_variable w hw s u (hq hu) i hi hwi
      have hj (j : σ) (hji : j ≠ i) :
          Finsupp.single i (1 : ℕ) ≠ Finsupp.single j 1 := by
        intro hh
        have hh' := congrArg (fun d : σ →₀ ℕ => d i) hh
        simp [Finsupp.single_apply, hji] at hh'
      rw [Finset.sum_eq_single i]
      · rw [he]
        simp only [MvPolynomial.coeff_monomial, if_pos rfl, ite_true]
        rw [← MvPolynomial.C_mul_X_eq_monomial]
        simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, v, if_pos hwis]
        ring
      · intro j _ hj'
        rw [he]
        simp only [MvPolynomial.coeff_monomial, if_neg (hj j hj'), zero_mul]
      · simp
    · push_neg at h
      have he : MvPolynomial.eval x (monomial u (coeff u q)) =
          MvPolynomial.eval y (monomial u (coeff u q)) := by
        rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
        congr 1
        unfold Finsupp.prod
        apply Finset.prod_congr rfl
        intro i hi
        change x i ^ u i = y i ^ u i
        rw [hxy i (h i (Finsupp.mem_support_iff.mp hi))]
      rw [he, sub_self]
      symm
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : w i = s
      · have hn : u ≠ Finsupp.single i 1 := by
          intro hu'
          have hne : u i ≠ 0 := by simp [hu']
          exact (ne_of_lt (h i hne)) hi
        simp only [MvPolynomial.coeff_monomial, if_neg hn, zero_mul]
      · simp [v, hi]
  change MvPolynomial.eval x q - MvPolynomial.eval y q =
    ∑ i : σ, coeff (Finsupp.single i 1) q * v i
  calc
    _ = ∑ u ∈ q.support, (MvPolynomial.eval x (monomial u (coeff u q)) -
        MvPolynomial.eval y (monomial u (coeff u q))) := by
          rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← q.as_sum]
    _ = ∑ u ∈ q.support, ∑ i : σ,
        coeff (Finsupp.single i 1) (monomial u (coeff u q)) * v i := by
          exact Finset.sum_congr rfl hmono
    _ = ∑ i : σ, ∑ u ∈ q.support,
        coeff (Finsupp.single i 1) (monomial u (coeff u q)) * v i :=
          Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, ← MvPolynomial.coeff_sum, ← q.as_sum]

/-- The coefficient of a linear variable in a gradient row is
the corresponding Hessian entry at zero. -/
theorem gradient_linearCoeff_eq_hessian_origin
    (P : MvPolynomial σ K) (j i : σ) :
    coeff (Finsupp.single i 1) (pderiv j P) =
      MvPolynomial.eval (0 : σ → K) (hessian P j i) := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, hessian_apply]
  simp only [HC4.Newton.coeff_pderiv_backport]
  simp

set_option maxHeartbeats 3000000 in
/-- The gradient of a source with positive coordinate weights and
zero determinant clock is injective. This is an unconditional
terminal endpoint for weighted descent. -/
theorem gradient_injective_of_positiveWeight_zeroClock
    (w : σ → ℤ) (hw : ∀ i, 0 < w i) (m : ℤ)
    (P : MvPolynomial σ K) (hcap : IsWeightLE w m P)
    (hclock : (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i) = 0)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant P = MvPolynomial.C δ) :
    Function.Injective (fun x : σ → K => fun j : σ =>
      MvPolynomial.eval x (pderiv j P)) := by
  classical
  let L := initialForm w m P
  let e := MvPolynomial.eval (0 : σ → K)
  let A := (hessian L).map e
  have hLdet : hessianDeterminant L = MvPolynomial.C δ := by
    change hessianDeterminant (initialForm w m P) = MvPolynomial.C δ
    rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m P hcap,
      hclock, hdet]
    exact initialForm_eq_self_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_C w δ)
  have hA : A.det = δ := by
    change (e.mapMatrix (hessian L)).det = δ
    rw [← RingHom.map_det, show (hessian L).det = MvPolynomial.C δ from hLdet]
    exact MvPolynomial.eval_C δ
  have hblock (j i : σ) (h : w j + w i ≠ m) : A j i = 0 := by
    have hh := hessian_entry_isWeightedHomogeneous
      (initialForm_isWeightedHomogeneous w m P) j i
    change MvPolynomial.eval (0 : σ → K) (hessian L j i) = 0
    rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    exact hh.coeff_eq_zero 0 (by rw [map_zero]; omega)
  have hlin (j i : σ) (h : w j + w i = m) :
      coeff (Finsupp.single i 1) (pderiv j P) = A j i := by
    have he := gradient_linearCoeff_eq_hessian_origin L j i
    change coeff (Finsupp.single i 1) (pderiv j L) = A j i at he
    rw [← he]
    change coeff (Finsupp.single i 1) (pderiv j P) =
      coeff (Finsupp.single i 1) (pderiv j (initialForm w m P))
    rw [pderiv_initialForm, coeff_initialForm, Finsupp.weight_single, one_smul, if_pos (by omega)]
  intro x y hxy
  by_contra hn
  let S := Finset.univ.filter (fun i : σ => x i ≠ y i)
  have hS : S.Nonempty := by
    by_contra h
    apply hn
    funext i
    by_contra hi
    exact h ⟨i, by simp [S, hi]⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image S w hS
  let s := w k
  let v : σ → K := fun i => if w i = s then x i - y i else 0
  have hlower (i : σ) (hi : w i < s) : x i = y i := by
    by_contra h
    exact (not_lt_of_ge (hmin i (by simp [S, h]))) hi
  have hvk : v k ≠ 0 := by
    have hh : x k ≠ y k := (Finset.mem_filter.mp hk).2
    simpa [v, s] using sub_ne_zero.mpr hh
  have hAv : A *ᵥ v = 0 := by
    funext j
    change (∑ i : σ, A j i * v i) = 0
    by_cases hj : m - w j = s
    · have hq : IsWeightLE w s (pderiv j P) := by
        rw [← hj]
        exact hcap.pderiv j
      have he := eval_sub_eq_weightBlock_linear w hw s (pderiv j P) hq x y hlower
      have hz : MvPolynomial.eval x (pderiv j P) -
          MvPolynomial.eval y (pderiv j P) = 0 :=
        sub_eq_zero.mpr (congrFun hxy j)
      rw [hz] at he
      change 0 = ∑ i : σ, coeff (Finsupp.single i 1) (pderiv j P) * v i at he
      rw [he]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : w i = s
      · rw [hlin j i (by omega)]
      · simp [v, hi]
    · apply Finset.sum_eq_zero
      intro i _
      by_cases hi : w i = s
      · rw [hblock j i (by omega), zero_mul]
      · simp [v, hi]
  have hunit : IsUnit A.det := by rw [hA]; exact isUnit_iff_ne_zero.mpr hδ
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hunit)
  have hv0 : v = 0 := hinj (hAv.trans (Matrix.mulVec_zero A).symm)
  exact hvk (congrFun hv0 k)

end
end HC4.Polynomial

#print axioms HC4.Polynomial.gradient_injective_of_positiveWeight_zeroClock
