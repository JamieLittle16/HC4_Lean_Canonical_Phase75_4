import HC4.Newton.CharZeroHessianKernelRigidity
import HC4.Newton.ExactCollisionFirstWall
import HC4.Polynomial.HessianDeterminant
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# Determinant preservation across a transverse degree gap

For the marked-axis weights `(0,1,1,1)`, a potential of transverse weight at
most two has Hessian determinant of weight at most two. A perturbation whose
terms all have weight at least five changes its Hessian determinant only in
weights at least three. In particular, a determinant-one source split across
this gap has a determinant-one quadratic part.
-/

namespace HC4.Valuation.TransverseGap

open MvPolynomial
open scoped BigOperators Pointwise

noncomputable section

variable {K : Type*} [Field K]

/-- The longitudinal coordinate has weight zero and each transverse
coordinate has weight one. -/
def markedAxisWeight (i : Fin 4) : ℤ := if i = 0 then 0 else 1

local notation "w" => markedAxisWeight

private abbrev P (K : Type*) [Field K] := MvPolynomial (Fin 4) K

private def AtLeast (n : ℤ) (p : P K) : Prop :=
  ∀ m ∈ p.support, n ≤ Finsupp.weight w m

private def AtMost (n : ℤ) (p : P K) : Prop :=
  ∀ m ∈ p.support, Finsupp.weight w m ≤ n

private lemma w_nonneg (i : Fin 4) : 0 ≤ w i := by
  fin_cases i <;> decide

private lemma w_le_one (i : Fin 4) : w i ≤ 1 := by
  fin_cases i <;> decide

private lemma weight_nonneg (m : Fin 4 →₀ ℕ) : 0 ≤ Finsupp.weight w m := by
  classical
  rw [Finsupp.weight_apply]
  exact Finset.sum_nonneg fun i _ => nsmul_nonneg (w_nonneg i) _

private lemma lower_zero (n : ℤ) : AtLeast n (0 : P K) := by
  simp [AtLeast]

private lemma lower_add {n : ℤ} {p q : P K} (hp : AtLeast n p) (hq : AtLeast n q) :
    AtLeast n (p + q) := by
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h
  · exact hq m h

private lemma lower_mul {n k : ℤ} {p q : P K} (hp : AtLeast n p) (hq : AtLeast k q) :
    AtLeast (n + k) (p * q) := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  rw [map_add]
  exact add_le_add (hp a ha) (hq b hb)

private lemma upper_mul {n k : ℤ} {p q : P K} (hp : AtMost n p) (hq : AtMost k q) :
    AtMost (n + k) (p * q) := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  rw [map_add]
  exact add_le_add (hp a ha) (hq b hb)

private lemma upper_sum {α : Type*} (s : Finset α) (f : α → P K) {n : ℤ}
    (h : ∀ i ∈ s, AtMost n (f i)) : AtMost n (∑ i ∈ s, f i) := by
  intro m hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact h i hi m hmi

private lemma upper_C (a : K) : AtMost 0 (MvPolynomial.C a : P K) := by
  intro m hm
  rw [MvPolynomial.C_apply] at hm
  have h : m = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  simp [h]

private lemma upper_prod {α : Type*} (s : Finset α) (f : α → P K) (n : α → ℤ)
    (h : ∀ i ∈ s, AtMost (n i) (f i)) : AtMost (∑ i ∈ s, n i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (upper_C (1 : K))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact upper_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma support_pderiv_shift {p : P K} {m : Fin 4 →₀ ℕ} (i : Fin 4)
    (hm : m ∈ (pderiv i p).support) : m + Finsupp.single i 1 ∈ p.support := by
  rw [MvPolynomial.mem_support_iff, HC4.Newton.coeff_pderiv_backport] at hm
  rw [MvPolynomial.mem_support_iff]
  exact fun h => hm (by simp [h])

private lemma lower_pderiv {n : ℤ} {p : P K} (h : AtLeast n p) (i : Fin 4) :
    AtLeast (n - w i) (pderiv i p) := by
  intro m hm
  have h' := h _ (support_pderiv_shift i hm)
  rw [map_add, Finsupp.weight_single, one_smul] at h'
  omega

private lemma upper_pderiv {n : ℤ} {p : P K} (h : AtMost n p) (i : Fin 4) :
    AtMost (n - w i) (pderiv i p) := by
  intro m hm
  have h' := h _ (support_pderiv_shift i hm)
  rw [map_add, Finsupp.weight_single, one_smul] at h'
  omega

private def orderIdeal (n : ℤ) : Ideal (P K) where
  carrier := {p | AtLeast n p}
  zero_mem' := lower_zero n
  add_mem' := lower_add
  smul_mem' a p hp := by
    rw [smul_eq_mul]
    simpa using lower_mul (n := 0) (p := a) (fun m _ => weight_nonneg m) hp

private lemma hess_upper {q : P K} (hq : AtMost 2 q) (i j : Fin 4) :
    AtMost (2 - w i - w j) (HC4.Polynomial.hessian q i j) := by
  simpa only [HC4.Polynomial.hessian_apply] using upper_pderiv (upper_pderiv hq i) j

private lemma det_upper {q : P K} (hq : AtMost 2 q) :
    AtMost 2 (HC4.Polynomial.hessianDeterminant q) := by
  classical
  unfold HC4.Polynomial.hessianDeterminant
  rw [Matrix.det_apply']
  refine upper_sum _ _ fun π _ => ?_
  have ht := upper_prod Finset.univ (fun i => HC4.Polynomial.hessian q (π i) i)
    (fun i => 2 - w (π i) - w i) (fun i _ => hess_upper hq (π i) i)
  change AtMost (HC4.Polynomial.hessianTermWeight w 2 π) _ at ht
  rw [HC4.Polynomial.hessianTermWeight_eq] at ht
  have hsum : (∑ i : Fin 4, w i) = 3 := by decide
  rw [hsum] at ht
  norm_num at ht
  simpa only [map_intCast, zero_add, HC4.Polynomial.hessian_apply] using
    upper_mul (upper_C ((Equiv.Perm.sign π : ℤ) : K)) ht

private lemma det_mod_order_three {q r : P K} (hr : AtLeast 5 r) :
    HC4.Polynomial.hessianDeterminant (q + r) -
      HC4.Polynomial.hessianDeterminant q ∈ (orderIdeal (K := K) 3) := by
  let I : Ideal (P K) := orderIdeal 3
  let φ := Ideal.Quotient.mk I
  have hm : φ.mapMatrix (HC4.Polynomial.hessian (q + r)) =
      φ.mapMatrix (HC4.Polynomial.hessian q) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, HC4.Polynomial.hessian_apply,
      map_add]
    have hr' : pderiv j (pderiv i r) ∈ I := by
      intro m hm
      have h := lower_pderiv (lower_pderiv hr i) j m hm
      have hi := w_le_one i
      have hj := w_le_one j
      omega
    rw [show φ (pderiv j (pderiv i r)) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hr',
      add_zero]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I) _ _).mp
  change φ ((HC4.Polynomial.hessian (q + r)).det) = φ ((HC4.Polynomial.hessian q).det)
  rw [φ.map_det, φ.map_det, hm]

/-- Terms of transverse weight at least five cannot repair a nonunit Hessian
determinant of a transverse-quadratic potential. -/
theorem quadraticDeterminant_one_of_highWeightPerturbation (q r : MvPolynomial (Fin 4) K)
    (hq : ∀ m ∈ q.support, Finsupp.weight w m ≤ 2)
    (hr : ∀ m ∈ r.support, 5 ≤ Finsupp.weight w m)
    (hdet : HC4.Polynomial.hessianDeterminant (q + r) = 1) :
    HC4.Polynomial.hessianDeterminant q = 1 := by
  have h := det_mod_order_three (q := q) hr
  rw [hdet] at h
  rw [← sub_eq_zero]
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  by_contra hm
  have hm' : m ∈ (HC4.Polynomial.hessianDeterminant q - 1).support :=
    MvPolynomial.mem_support_iff.mpr hm
  have hm'' : m ∈ (1 - HC4.Polynomial.hessianDeterminant q).support := by
    rwa [← neg_sub, MvPolynomial.support_neg]
  change AtLeast 3 _ at h
  have hlow := h m hm''
  have hhigh : Finsupp.weight w m ≤ 2 := by
    rw [sub_eq_add_neg] at hm'
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm') with hx | hx
    · exact det_upper hq m hx
    · rw [MvPolynomial.support_neg] at hx
      have hz := upper_C (1 : K) m (by simpa using hx)
      omega
  omega

/-- The grades zero, one and two of the original polynomial for the
marked-axis transverse grading. -/
def quadraticTruncation (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm w 0 F +
    HC4.Polynomial.initialForm w 1 F + HC4.Polynomial.initialForm w 2 F

private lemma quadraticTruncation_upper (F : P K) :
    AtMost 2 (quadraticTruncation F) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  by_contra! h
  have h0 : Finsupp.weight w m ≠ 0 := by omega
  have h1 : Finsupp.weight w m ≠ 1 := by omega
  have h2 : Finsupp.weight w m ≠ 2 := by omega
  simp [quadraticTruncation, MvPolynomial.coeff_add,
    HC4.Polynomial.coeff_initialForm, h0, h1, h2] at hm

private lemma quadraticRemainder_lower (F : P K)
    (h3 : HC4.Polynomial.initialForm w 3 F = 0)
    (h4 : HC4.Polynomial.initialForm w 4 F = 0) :
    AtLeast 5 (F - quadraticTruncation F) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  by_contra! h
  have hlo := weight_nonneg m
  have hhi : Finsupp.weight w m ≤ 4 := by omega
  interval_cases hw : Finsupp.weight w m
  all_goals
    first
    | have hc := congrArg (MvPolynomial.coeff m) h3
      have hz : MvPolynomial.coeff m F = 0 := by
        simpa [HC4.Polynomial.coeff_initialForm, hw] using hc
      simp [quadraticTruncation, MvPolynomial.coeff_add, MvPolynomial.coeff_sub,
        HC4.Polynomial.coeff_initialForm, hw, hz] at hm
    | have hc := congrArg (MvPolynomial.coeff m) h4
      have hz : MvPolynomial.coeff m F = 0 := by
        simpa [HC4.Polynomial.coeff_initialForm, hw] using hc
      simp [quadraticTruncation, MvPolynomial.coeff_add, MvPolynomial.coeff_sub,
        HC4.Polynomial.coeff_initialForm, hw, hz] at hm
    | simp [quadraticTruncation, MvPolynomial.coeff_add, MvPolynomial.coeff_sub,
        HC4.Polynomial.coeff_initialForm, hw] at hm

private def axisPoint (x : K) : Fin 4 → K := Fin.cons x (fun _ => 0)

private lemma eval_axis_eq_zero_of_positive {p : P K} (hp : AtLeast 1 p) (x : K) :
    MvPolynomial.eval (axisPoint x) p = 0 := by
  classical
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_eq_zero
  intro m hm
  have hw := hp m hm
  have hex : ∃ i : Fin 4, i ≠ 0 ∧ m i ≠ 0 := by
    by_contra! h
    have hz : Finsupp.weight w m = 0 := by
      rw [Finsupp.weight_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = 0
      · simp [hi, markedAxisWeight]
      · simp [h i hi]
    omega
  obtain ⟨i, hi, hmi⟩ := hex
  have he : axisPoint x i = 0 := by
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ => simp [axisPoint]
  have hz : (∏ j : Fin 4, axisPoint x j ^ m j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [he, zero_pow hmi])
  rw [hz, mul_zero]

/-- If the cubic and quartic transverse grades are absent, the marked
quadratic truncation inherits both the determinant and the marked gradient
collision. -/
theorem quadraticTruncation_inherits_of_gap (F : MvPolynomial (Fin 4) K)
    (h3 : HC4.Polynomial.initialForm w 3 F = 0)
    (h4 : HC4.Polynomial.initialForm w 4 F = 0)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hcoll : HC4.Newton.HasExactGradientCollision F
      (Fin.cons 0 (fun _ : Fin 3 => 0)) (Fin.cons 1 (fun _ : Fin 3 => 0))) :
    (∀ m ∈ (quadraticTruncation F).support, Finsupp.weight w m ≤ 2) ∧
    HC4.Polynomial.hessianDeterminant (quadraticTruncation F) = 1 ∧
    HC4.Newton.HasExactGradientCollision (quadraticTruncation F)
      (Fin.cons 0 (fun _ : Fin 3 => 0)) (Fin.cons 1 (fun _ : Fin 3 => 0)) := by
  let q := quadraticTruncation F
  let r := F - q
  have hsplit : q + r = F := by
    dsimp [r]
    abel
  have hq := quadraticTruncation_upper F
  have hr : AtLeast 5 r := quadraticRemainder_lower F h3 h4
  have hd := quadraticDeterminant_one_of_highWeightPerturbation q r hq hr
    (hsplit ▸ hdet)
  refine ⟨hq, hd, ?_⟩
  intro i
  have hz (x : K) :
      MvPolynomial.eval (axisPoint x) (pderiv i r) = 0 := by
    apply eval_axis_eq_zero_of_positive
    intro m hm
    have hh := lower_pderiv hr i m hm
    have hi := w_le_one i
    omega
  have hh := hcoll i
  rw [← hsplit] at hh
  change MvPolynomial.eval (axisPoint 0) (pderiv i (q + r)) =
    MvPolynomial.eval (axisPoint 1) (pderiv i (q + r)) at hh
  change MvPolynomial.eval (axisPoint 0) (pderiv i q) =
    MvPolynomial.eval (axisPoint 1) (pderiv i q)
  simpa only [map_add, hz, add_zero] using hh

end

end HC4.Valuation.TransverseGap
