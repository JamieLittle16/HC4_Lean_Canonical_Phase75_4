import HC4.Polynomial.TwoZeroWeightFullSource

/-!
# Fibrewise injectivity at every nonnegative zero clock

The least differing positive-weight block argument works also in
the presence of zero weights, provided the points agree there.
The coefficient matrix must be evaluated at their common base,
rather than at the origin. We use the actual Hessian at one point.

This leaves only recovery of the zero-weight coordinates.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

private theorem nonnegativeWeight_nonneg
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (u : σ →₀ ℕ) :
    0 ≤ Finsupp.weight w u := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro i _
  exact nsmul_nonneg (hw i) _

private theorem nonnegativeWeight_remove_one
    (w : σ → ℤ) (u : σ →₀ ℕ) (i : σ) (hi : u i ≠ 0) :
    Finsupp.weight w (u - Finsupp.single i 1) + w i =
      Finsupp.weight w u := by
  have he := congrArg (Finsupp.weight w) (Finsupp.sub_add_single_one_cancel hi)
  rw [map_add, Finsupp.weight_single, one_smul] at he
  exact he

private theorem nonnegativeWeight_zero_support
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (u : σ →₀ ℕ)
    (hu : Finsupp.weight w u = 0) (i : σ) (hi : u i ≠ 0) :
    w i = 0 := by
  have he := nonnegativeWeight_remove_one w u i hi
  have hn := nonnegativeWeight_nonneg w hw (u - Finsupp.single i 1)
  have hwi := hw i
  omega

/-- A bounded polynomial of negative weight vanishes for
nonnegative coordinate weights. -/
theorem eq_zero_of_nonnegativeWeight_negative_cap
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (s : ℤ) (hs : s < 0)
    (q : MvPolynomial σ K) (hq : IsWeightLE w s q) : q = 0 := by
  classical
  ext u
  rw [coeff_zero]
  by_contra hu
  have he := hq (MvPolynomial.mem_support_iff.mpr hu)
  have hn := nonnegativeWeight_nonneg w hw u
  omega

set_option maxHeartbeats 4000000 in
/-- Exact linearity of the first differing positive block, with
coefficients evaluated at the original point. -/
theorem eval_sub_eq_nonnegativeWeightBlock_deriv
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (s : ℤ) (hs : 0 < s)
    (q : MvPolynomial σ K) (hq : IsWeightLE w s q)
    (x y : σ → K) (hxy : ∀ i, w i < s → x i = y i) :
    MvPolynomial.eval x q - MvPolynomial.eval y q =
      ∑ i : σ, MvPolynomial.eval x (pderiv i q) *
        (if w i = s then x i - y i else 0) := by
  classical
  let v : σ → K := fun i => if w i = s then x i - y i else 0
  have hmono (u : σ →₀ ℕ) (hu : u ∈ q.support) :
      MvPolynomial.eval x (monomial u (coeff u q)) -
        MvPolynomial.eval y (monomial u (coeff u q)) =
      ∑ i : σ, MvPolynomial.eval x (pderiv i (monomial u (coeff u q))) * v i := by
    by_cases h : ∃ i, u i ≠ 0 ∧ s ≤ w i
    · obtain ⟨i, hi, hwi⟩ := h
      let t := u - Finsupp.single i 1
      have htadd : t + Finsupp.single i 1 = u :=
        Finsupp.sub_add_single_one_cancel hi
      have hweight := nonnegativeWeight_remove_one w u i hi
      have hnonneg := nonnegativeWeight_nonneg w hw t
      have hbound := hq hu
      have hwi' : w i = s := by omega
      have ht : Finsupp.weight w t = 0 := by omega
      have htz (j : σ) (hj : 0 < w j) : t j = 0 := by
        by_contra hn
        have he := nonnegativeWeight_zero_support w hw t ht j hn
        omega
      let g := monomial t (coeff u q)
      have hform : monomial u (coeff u q) = g * X i := by
        rw [MvPolynomial.X, g, MvPolynomial.monomial_mul, htadd, mul_one]
      have hge : MvPolynomial.eval x g = MvPolynomial.eval y g := by
        rw [g, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
        congr 1
        unfold Finsupp.prod
        apply Finset.prod_congr rfl
        intro j hj
        have hz := nonnegativeWeight_zero_support w hw t ht j (Finsupp.mem_support_iff.mp hj)
        change x j ^ t j = y j ^ t j
        rw [hxy j (by omega)]
      have hgder (j : σ) (hj : w j = s) : pderiv j g = 0 := by
        rw [g, MvPolynomial.pderiv_monomial, htz j (by omega), Nat.cast_zero, mul_zero, map_zero]
      rw [Finset.sum_eq_single i]
      · rw [hform, Derivation.leibniz, hgder i hwi']
        simp only [MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one, zero_mul, add_zero,
          map_mul, MvPolynomial.eval_X, v, if_pos hwi']
        rw [← hge]
        ring
      · intro j _ hj
        by_cases hjs : w j = s
        · rw [hform, Derivation.leibniz, hgder j hjs]
          simp [MvPolynomial.pderiv_X, Pi.single_apply, hj, Ne.symm hj]
        · simp [v, hjs]
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
      · have hz : u i = 0 := by
          by_contra hn
          exact (ne_of_lt (h i hn)) hi
        rw [MvPolynomial.pderiv_monomial, hz, Nat.cast_zero, mul_zero, map_zero,
          map_zero, zero_mul]
      · simp [v, hi]
  change MvPolynomial.eval x q - MvPolynomial.eval y q =
    ∑ i : σ, MvPolynomial.eval x (pderiv i q) * v i
  calc
    _ = ∑ u ∈ q.support, (MvPolynomial.eval x (monomial u (coeff u q)) -
        MvPolynomial.eval y (monomial u (coeff u q))) := by
          rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← q.as_sum]
    _ = ∑ u ∈ q.support, ∑ i : σ,
        MvPolynomial.eval x (pderiv i (monomial u (coeff u q))) * v i :=
          Finset.sum_congr rfl hmono
    _ = ∑ i : σ, ∑ u ∈ q.support,
        MvPolynomial.eval x (pderiv i (monomial u (coeff u q))) * v i :=
          Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← q.as_sum]

set_option maxHeartbeats 4000000 in
/-- All nonnegative zero-clock sources are injective on fibres
of their zero-weight coordinate projection. -/
theorem gradient_eq_imp_eq_of_nonnegativeWeight_zeroClock
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (m : ℤ)
    (P : MvPolynomial σ K) (hcap : IsWeightLE w m P)
    (hclock : (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i) = 0)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant P = MvPolynomial.C δ)
    (x y : σ → K) (hz : ∀ i, w i = 0 → x i = y i)
    (hxy : ∀ j, MvPolynomial.eval x (pderiv j P) = MvPolynomial.eval y (pderiv j P)) :
    x = y := by
  classical
  let L := initialForm w m P
  have hLdet : hessianDeterminant L = MvPolynomial.C δ := by
    change hessianDeterminant (initialForm w m P) = MvPolynomial.C δ
    rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m P hcap,
      hclock, hdet]
    exact initialForm_eq_self_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_C w δ)
  have hentry (j i : σ) (h : w j + w i = m) :
      hessian P j i = hessian L j i := by
    change hessian P j i = hessian (initialForm w m P) j i
    rw [hessian_initialForm_entry]
    have hh := sub_initialForm_isWeightLT (hcap.hessian_entry j i)
    have hb : IsWeightLE w (-1) (hessian P j i -
        initialForm w (m - w j - w i) (hessian P j i)) := by
      intro u hu
      have he := hh hu
      omega
    exact sub_eq_zero.mp (eq_zero_of_nonnegativeWeight_negative_cap w hw (-1)
      (by decide) _ hb)
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
  have hkne : x k ≠ y k := (Finset.mem_filter.mp hk).2
  have hs : 0 < s := by
    have h := hw k
    by_contra h'
    exact hkne (hz k (by omega))
  let v : σ → K := fun i => if w i = s then x i - y i else 0
  have hlower (i : σ) (hi : w i < s) : x i = y i := by
    by_contra h
    exact (not_lt_of_ge (hmin i (by simp [S, h]))) hi
  have hvk : v k ≠ 0 := by simpa [v, s] using sub_ne_zero.mpr hkne
  -- Evaluate the exact homogeneous Hessian on the common zero-weight
  -- base, with all positive-weight coordinates set to zero.
  let z : σ → K := fun i => if w i = 0 then x i else 0
  let T := (hessian L).map (MvPolynomial.eval z)
  have hT : T.det = δ := by
    change ((MvPolynomial.eval z).mapMatrix (hessian L)).det = δ
    rw [← RingHom.map_det, show (hessian L).det = MvPolynomial.C δ from hLdet]
    exact MvPolynomial.eval_C δ
  have hzeroEval (q : MvPolynomial σ K) (hQ : IsWeightLE w 0 q) :
      MvPolynomial.eval z q = MvPolynomial.eval x q := by
    have hm (u : σ →₀ ℕ) (hu : u ∈ q.support) :
        MvPolynomial.eval z (monomial u (coeff u q)) =
          MvPolynomial.eval x (monomial u (coeff u q)) := by
      have hwt : Finsupp.weight w u = 0 :=
        le_antisymm (hQ hu) (nonnegativeWeight_nonneg w hw u)
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      congr 1
      unfold Finsupp.prod
      apply Finset.prod_congr rfl
      intro i hi
      have hwi := nonnegativeWeight_zero_support w hw u hwt i (Finsupp.mem_support_iff.mp hi)
      change z i ^ u i = x i ^ u i
      simp [z, hwi]
    calc
      _ = ∑ u ∈ q.support, MvPolynomial.eval z (monomial u (coeff u q)) := by
        rw [← map_sum, ← q.as_sum]
      _ = ∑ u ∈ q.support, MvPolynomial.eval x (monomial u (coeff u q)) :=
        Finset.sum_congr rfl hm
      _ = _ := by rw [← map_sum, ← q.as_sum]
  have hTblock (j i : σ) (h : w j + w i ≠ m) : T j i = 0 := by
    change MvPolynomial.eval z (hessian L j i) = 0
    have hh := hessian_entry_isWeightedHomogeneous
      (initialForm_isWeightedHomogeneous w m P) j i
    have hm (u : σ →₀ ℕ) (hu : coeff u (hessian L j i) ≠ 0) :
        ∃ l ∈ u.support, z l = 0 := by
      by_contra hn
      push_neg at hn
      have hwt := hh hu
      have hwt0 : Finsupp.weight w u = 0 := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        apply Finset.sum_eq_zero
        intro l hl
        have hwi : w l = 0 := by
          by_contra hne
          exact hn l hl (by simp [z, hne])
        rw [hwi, smul_zero]
      omega
    exact MvPolynomial.eval₂Hom_eq_zero (RingHom.id K) z _ hm
  have hTv : T *ᵥ v = 0 := by
    funext j
    change (∑ i : σ, T j i * v i) = 0
    by_cases hj : m - w j = s
    · have hq : IsWeightLE w s (pderiv j P) := by
        rw [← hj]
        exact hcap.pderiv j
      have he := eval_sub_eq_nonnegativeWeightBlock_deriv w hw s hs
        (pderiv j P) hq x y hlower
      rw [hxy j, sub_self] at he
      change 0 = ∑ i : σ, MvPolynomial.eval x (hessian P j i) * v i at he
      rw [he]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : w i = s
      · have hh := hcap.hessian_entry j i
        have hh0 : IsWeightLE w 0 (hessian P j i) := by
          intro u hu
          have h := hh hu
          omega
        change MvPolynomial.eval z (hessian L j i) * v i =
          MvPolynomial.eval x (hessian P j i) * v i
        rw [← hentry j i (by omega), hzeroEval _ hh0]
      · simp [v, hi]
    · apply Finset.sum_eq_zero
      intro i _
      by_cases hi : w i = s
      · rw [hTblock j i (by omega), zero_mul]
      · simp [v, hi]
  have hunit : IsUnit T.det := by rw [hT]; exact isUnit_iff_ne_zero.mpr hδ
  have hinj : Function.Injective T.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det T).mpr hunit)
  have hv0 : v = 0 := hinj (hTv.trans (Matrix.mulVec_zero T).symm)
  exact hvk (congrFun hv0 k)

end
end HC4.Polynomial

#print axioms HC4.Polynomial.gradient_eq_imp_eq_of_nonnegativeWeight_zeroClock
