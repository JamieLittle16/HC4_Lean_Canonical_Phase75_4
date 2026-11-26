import HC4.Polynomial.NonnegativeWeightZeroClock
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Degree.Units

/-!
# One-zero terminal injectivity

At determinant clock zero the leading Hessian at the origin
pairs complementary weights. A zero weight therefore has a
partner of weight m. The latter gradient row has weight bound
zero and depends only on the unique zero coordinate.

All other entries of this Hessian row vanish, so its remaining
entry is a unit by the full determinant-one identity.
After univariate specialization the derivative is a nonzero
constant, forcing an affine gradient row. Recover the base
coordinate and apply the certified fibrewise endpoint.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K] [CharZero K]

private theorem oneZero_weight_nonneg
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (u : σ →₀ ℕ) :
    0 ≤ Finsupp.weight w u := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro i _
  exact nsmul_nonneg (hw i) _

private theorem oneZero_support
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i)
    (k : σ) (hk : ∀ i, w i = 0 → i = k)
    (q : MvPolynomial σ K) (hq : IsWeightLE w 0 q)
    (u : σ →₀ ℕ) (hu : u ∈ q.support) (i : σ) (hi : i ∈ u.support) :
    i = k := by
  have he := congrArg (Finsupp.weight w)
    (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi))
  rw [map_add, Finsupp.weight_single, one_smul] at he
  have hn := oneZero_weight_nonneg w hw (u - Finsupp.single i 1)
  have hb := hq hu
  have hwi := hw i
  exact hk i (by omega)

/-- A weight-zero gradient row with a unique zero coordinate is
literally its univariate specialization on every point. -/
theorem oneZero_eval_specialization
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i)
    (k : σ) (hk : ∀ i, w i = 0 → i = k)
    (q : MvPolynomial σ K) (hq : IsWeightLE w 0 q)
    (x : σ → K) :
    _root_.Polynomial.eval (x k)
      (MvPolynomial.aeval (fun i : σ =>
        if i = k then (_root_.Polynomial.X : _root_.Polynomial K) else 0) q) =
      MvPolynomial.eval x q := by
  classical
  let z : σ → _root_.Polynomial K := fun i => if i = k then _root_.Polynomial.X else 0
  let E : MvPolynomial σ K →ₐ[K] _root_.Polynomial K := MvPolynomial.aeval z
  have he : _root_.Polynomial.eval (x k) (E q) =
      MvPolynomial.eval (fun i => if i = k then x k else 0) q := by
    let f : _root_.Polynomial K →ₐ[K] K := _root_.Polynomial.aeval (x k)
    have h : f.comp E = MvPolynomial.aeval (fun i : σ => if i = k then x k else 0) := by
      ext i
      by_cases hi : i = k <;> simp [E, z, f, hi]
    exact AlgHom.congr_fun h q
  change _root_.Polynomial.eval (x k) (E q) = MvPolynomial.eval x q
  rw [he]
  have hm (u : σ →₀ ℕ) (hu : u ∈ q.support) :
      MvPolynomial.eval (fun i => if i = k then x k else 0) (monomial u (coeff u q)) =
        MvPolynomial.eval x (monomial u (coeff u q)) := by
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    congr 1
    unfold Finsupp.prod
    apply Finset.prod_congr rfl
    intro i hi
    have hik := oneZero_support w hw k hk q hq u hu i hi
    subst i
    simp
  calc
    _ = ∑ u ∈ q.support, MvPolynomial.eval (fun i => if i = k then x k else 0)
        (monomial u (coeff u q)) := by rw [← map_sum, ← q.as_sum]
    _ = ∑ u ∈ q.support, MvPolynomial.eval x (monomial u (coeff u q)) :=
      Finset.sum_congr rfl hm
    _ = _ := by rw [← map_sum, ← q.as_sum]

set_option maxHeartbeats 4000000 in
/-- The entire one-zero-weight terminal is injective without JC2. -/
theorem gradient_injective_of_oneZeroWeight_zeroClock
    (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (m : ℤ)
    (k : σ) (hk0 : w k = 0) (hk : ∀ i, w i = 0 → i = k)
    (P : MvPolynomial σ K) (hcap : IsWeightLE w m P)
    (hclock : (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i) = 0)
    (hdet : hessianDeterminant P = 1) :
    Function.Injective (fun x : σ → K => fun i : σ =>
      MvPolynomial.eval x (pderiv i P)) := by
  classical
  let L := initialForm w m P
  have hL : hessianDeterminant L = 1 := by
    change hessianDeterminant (initialForm w m P) = 1
    rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m P hcap,
      hclock, hdet]
    exact initialForm_eq_self_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_one K w)
  let T := (hessian L).map (MvPolynomial.eval (0 : σ → K))
  have hT : T.det = 1 := by
    change ((MvPolynomial.eval (0 : σ → K)).mapMatrix (hessian L)).det = 1
    rw [← RingHom.map_det, show (hessian L).det = 1 from hL, map_one]
  have hex : ∃ j : σ, w j = m := by
    by_contra h
    push_neg at h
    have hcol (j : σ) : T j k = 0 := by
      have hh := hessian_entry_isWeightedHomogeneous
        (initialForm_isWeightedHomogeneous w m P) j k
      change MvPolynomial.eval (0 : σ → K) (hessian L j k) = 0
      rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
      exact hh.coeff_eq_zero 0 (by
        rw [map_zero, hk0]
        have hj := h j
        omega)
    exact one_ne_zero (hT.symm.trans (Matrix.det_eq_zero_of_column_eq_zero k hcol))
  obtain ⟨j, hj⟩ := hex
  let g := pderiv j P
  have hg : IsWeightLE w 0 g := by
    have h := hcap.pderiv j
    simpa [hj] using h
  have hrow (i : σ) (hi : i ≠ k) : hessian P j i = 0 := by
    have hwi : 0 < w i := by
      have hn := hw i
      by_contra h
      exact hi (hk i (by omega))
    exact eq_zero_of_nonnegativeWeight_negative_cap w hw _ (by omega)
      _ (hcap.hessian_entry j i)
  have hmul : hessian P j k * (hessian P).adjugate k j = 1 := by
    have he := congrArg (fun M : Matrix σ σ (MvPolynomial σ K) => M j j)
      (Matrix.mul_adjugate (hessian P))
    change (∑ i : σ, hessian P j i * (hessian P).adjugate i j) =
      ((hessian P).det • (1 : Matrix σ σ (MvPolynomial σ K))) j j at he
    rw [show (hessian P).det = 1 from hdet, one_smul, Matrix.one_apply_eq] at he
    rw [Finset.sum_eq_single k] at he
    · exact he
    · intro i _ hi
      rw [hrow i hi, zero_mul]
    · simp
  let z : σ → _root_.Polynomial K := fun i => if i = k then _root_.Polynomial.X else 0
  let E : MvPolynomial σ K →ₐ[K] _root_.Polynomial K := MvPolynomial.aeval z
  let f := E g
  have hfder : f.derivative = E (hessian P j k) := by
    change _root_.Polynomial.derivative' (E g) = E (hessian P j k)
    rw [HC4.Polynomial.RankThreeCubic.derivation_aeval]
    rw [Finset.sum_eq_single k]
    · simp [E, z, hessian_apply, g]
    · intro i _ hi
      simp [z, hi]
    · simp
  have hunit : IsUnit f.derivative := by
    rw [hfder]
    apply isUnit_iff_dvd_one.mpr
    refine ⟨E ((hessian P).adjugate k j), ?_⟩
    rw [← map_mul, hmul, map_one]
  obtain ⟨a, ha, hda⟩ := _root_.Polynomial.isUnit_iff.mp hunit
  have hlin : ∃ b : K, f = _root_.Polynomial.C a * _root_.Polynomial.X + _root_.Polynomial.C b := by
    let r := f - _root_.Polynomial.C a * _root_.Polynomial.X
    have hr : r.derivative = 0 := by
      change (f - _root_.Polynomial.C a * _root_.Polynomial.X).derivative = 0
      rw [_root_.Polynomial.derivative_sub, _root_.Polynomial.derivative_C_mul_X, ← hda, sub_self]
    have he := _root_.Polynomial.eq_C_of_derivative_eq_zero hr
    refine ⟨r.coeff 0, ?_⟩
    change f - _root_.Polynomial.C a * _root_.Polynomial.X = _ at he
    linear_combination he
  obtain ⟨b, hb⟩ := hlin
  intro x y hxy
  have he := congrFun hxy j
  change MvPolynomial.eval x g = MvPolynomial.eval y g at he
  have hx := oneZero_eval_specialization w hw k hk g hg x
  have hy := oneZero_eval_specialization w hw k hk g hg y
  change _root_.Polynomial.eval (x k) f = _ at hx
  change _root_.Polynomial.eval (y k) f = _ at hy
  rw [← hx, ← hy, hb] at he
  simp only [_root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_C, _root_.Polynomial.eval_X] at he
  have hbase : x k = y k := mul_left_cancel₀ ha.ne_zero (add_right_cancel he)
  apply gradient_eq_imp_eq_of_nonnegativeWeight_zeroClock w hw m P hcap hclock
    (δ := (1 : K)) one_ne_zero (by simpa using hdet) x y
  · intro i hi
    rw [hk i hi]
    exact hbase
  · exact congrFun hxy

end
end HC4.Polynomial

#print axioms HC4.Polynomial.gradient_injective_of_oneZeroWeight_zeroClock
