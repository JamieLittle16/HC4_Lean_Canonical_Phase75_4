import HC4.Polynomial.WeightedExtremalObstruction

/-!
# Constant kernel exclusion at a global optimum

The leading Hessian of a positive-clock globally optimal
determinant-one source has no nonzero constant kernel vector.

Project a constant directional derivative onto one equal-weight
block and align that block by a determinant-one column shear.
If the resulting derivative is nonzero constant, its weight is
zero and the strictly lower source correction cannot affect it.
The full Hessian would then be singular. If it is zero, the
verified extremal missing-coordinate obstruction applies.

No analogous assertion about adjugate annihilators is made.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- All vanishing partials imply a ground-field constant. -/
theorem extremal_eq_C_of_all_pderiv_zero
    (f : MvPolynomial (Fin 4) K) (hf : ∀ i, pderiv i f = 0) :
    f = MvPolynomial.C (coeff 0 f) := by
  classical
  ext u
  by_cases hu : u = 0
  · subst u
    simp
  · have hz : coeff u f = 0 := by
      by_contra hn
      apply hu
      ext i
      exact exponent_eq_zero_of_pderiv_eq_zero i f (hf i) u hn
    simp [hz, MvPolynomial.coeff_C, Ne.symm hu]

def extremalDirectionalDerivative (d : Fin 4 → K) (L : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  ∑ i : Fin 4, pderiv i L * MvPolynomial.C (d i)

/-- A constant Hessian kernel makes the actual directional
derivative constant. -/
theorem extremalDirectionalDerivative_eq_C_of_kernel
    (d : Fin 4 → K) (L : MvPolynomial (Fin 4) K)
    (hd : hessian L *ᵥ (fun i => MvPolynomial.C (d i)) = 0) :
    ∃ c : K, extremalDirectionalDerivative d L = MvPolynomial.C c := by
  refine ⟨coeff 0 (extremalDirectionalDerivative d L), extremal_eq_C_of_all_pderiv_zero _ ?_⟩
  intro j
  unfold extremalDirectionalDerivative
  rw [map_sum]
  have he := congrFun hd j
  change (∑ i : Fin 4, hessian L j i * MvPolynomial.C (d i)) = 0 at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (pderiv i L), MvPolynomial.pderiv_C_mul, mul_comm,
    pderiv_comm_backport j i, hessian_apply]

/-- Weight projection isolates an equal-weight block of the
constant directional derivative. -/
theorem extremalDirectionalDerivative_block
    (w : Fin 4 → ℤ) (m s : ℤ) (L : MvPolynomial (Fin 4) K)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m)
    (d : Fin 4 → K) :
    extremalDirectionalDerivative (fun i => if w i = s then d i else 0) L =
      initialForm w (m-s) (extremalDirectionalDerivative d L) := by
  classical
  unfold extremalDirectionalDerivative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hh : MvPolynomial.IsWeightedHomogeneous w
      (pderiv i L * MvPolynomial.C (d i)) (m-w i) := by
    simpa only [add_zero] using (pderiv_isWeightedHomogeneous hL i).mul
      (MvPolynomial.isWeightedHomogeneous_C w (d i))
  change pderiv i L * MvPolynomial.C (if w i = s then d i else 0) = _
  by_cases hi : w i = s
  · rw [if_pos hi, ← hi, initialForm_eq_self_of_isWeightedHomogeneous hh]
  · rw [if_neg hi, map_zero, mul_zero,
      initialForm_eq_zero_of_isWeightedHomogeneous hh _ (by omega)]

/-- The column shear aligns a genuine vector (rather than a
covector) with a coordinate. -/
def extremalKernelShear (d : Fin 4 → K) (k : Fin 4) : Matrix (Fin 4) (Fin 4) K :=
  (annihilatorShear (fun i => if i = k then d k else -d i) k).transpose

theorem extremalKernelShear_det (d : Fin 4 → K) (k : Fin 4) :
    (extremalKernelShear d k).det = 1 := by
  rw [extremalKernelShear, Matrix.det_transpose, annihilatorShear_det]

theorem extremalKernelShear_respects_weight
    (w : Fin 4 → ℤ) (d : Fin 4 → K) (k : Fin 4)
    (hd : ∀ i, w i ≠ w k → d i = 0) :
    ∀ i j, w i ≠ w j → extremalKernelShear d k i j = 0 := by
  classical
  intro i j hij
  apply annihilatorShear_respects_weight w _ k _ j i (Ne.symm hij)
  intro l hl
  have hlk : l ≠ k := by
    intro h
    exact hl (congrArg w h)
  simp [hlk, hd l hl]

theorem extremalKernelShear_column
    (d : Fin 4 → K) (k : Fin 4) (hk : d k ≠ 0) (i : Fin 4) :
    extremalKernelShear d k i k = d i / d k := by
  classical
  by_cases hi : i = k
  · subst i
    simp [extremalKernelShear, annihilatorShear, Matrix.updateRow_apply, hk]
  · simp [extremalKernelShear, annihilatorShear, Matrix.updateRow_apply, hi, neg_div]

theorem extremalKernelShear_partial
    (L : MvPolynomial (Fin 4) K) (d : Fin 4 → K) (k : Fin 4) (hk : d k ≠ 0) :
    pderiv k (weightedLinearSubstitution (extremalKernelShear d k) L) =
      weightedLinearSubstitution (extremalKernelShear d k)
        (extremalDirectionalDerivative d L) * MvPolynomial.C ((d k)⁻¹) := by
  classical
  rw [weightedLinearSubstitution_partial, extremalDirectionalDerivative, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [extremalKernelShear_column d k hk, div_eq_mul_inv, map_mul, map_mul]
  have he : weightedLinearSubstitution (extremalKernelShear d k) (MvPolynomial.C (d i)) = MvPolynomial.C (d i) :=
    (weightedLinearSubstitution (extremalKernelShear d k)).commutes (d i)
  rw [he, mul_assoc]

/-- No leading partial at a positive-clock optimum can be
constant, including a nonzero affine coefficient. -/
theorem globalWeightOptimum_no_constant_partial
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (k : Fin 4) (c : K) :
    pderiv k (initialForm w m P) ≠ MvPolynomial.C c := by
  classical
  intro hc
  by_cases hz : c = 0
  · subst c
    have he := globalWeightOptimum_no_missing_coordinate P w m hw hm hcap hclock hopt
      (1 : Matrix (Fin 4) (Fin 4) K) Matrix.det_one
      (by intro i j hij; have hne : i ≠ j := by
            intro h; exact hij (congrArg w h)
          simp [Matrix.one_apply, hne]) k
    rw [weightedLinearSubstitution_one] at he
    exact he (by simpa using hc)
  · have hh := pderiv_isWeightedHomogeneous (initialForm_isWeightedHomogeneous w m P) k
    rw [hc] at hh
    have hcoef : coeff (0 : Fin 4 →₀ ℕ) (MvPolynomial.C c : MvPolynomial (Fin 4) K) ≠ 0 := by
      simpa using hz
    have he := hh hcoef
    rw [map_zero] at he
    have hshift : m - w k = 0 := he.symm
    have hrem := sub_initialForm_isWeightLT (hcap.pderiv k)
    rw [← pderiv_initialForm, hc, hshift] at hrem
    have hneg : IsWeightLE w (-1) (pderiv k P - MvPolynomial.C c) := by
      intro u hu
      have hb := hrem hu
      omega
    have hp : pderiv k P = MvPolynomial.C c := sub_eq_zero.mp
      (eq_zero_of_nonnegativeWeight_negative_cap w hw (-1) (by decide) _ hneg)
    have hcol (i : Fin 4) : hessian P i k = 0 := by
      rw [hessian_apply, pderiv_comm_backport k i, hp, pderiv_C]
    exact one_ne_zero (hdet.symm.trans (Matrix.det_eq_zero_of_column_eq_zero k hcol))

set_option maxHeartbeats 4000000 in
/-- The genuine leading Hessian has no nonzero constant vector
in its kernel at any positive-clock globally optimal presentation. -/
theorem globalWeightOptimum_no_constantHessianKernel
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (d : Fin 4 → K)
    (hd : hessian (initialForm w m P) *ᵥ (fun i => MvPolynomial.C (d i)) = 0) :
    d = 0 := by
  classical
  by_contra hn
  have hex : ∃ k, d k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨k,hk⟩ := hex
  let L := initialForm w m P
  let b : Fin 4 → K := fun i => if w i = w k then d i else 0
  have hbk : b k ≠ 0 := by simpa [b] using hk
  have hb (i : Fin 4) (hi : w i ≠ w k) : b i = 0 := by simp [b, hi]
  obtain ⟨c,hc⟩ := extremalDirectionalDerivative_eq_C_of_kernel d L hd
  have hblock := extremalDirectionalDerivative_block w m (w k) L
    (initialForm_isWeightedHomogeneous w m P) d
  change extremalDirectionalDerivative b L =
    initialForm w (m-w k) (extremalDirectionalDerivative d L) at hblock
  rw [hc] at hblock
  have hconst : ∃ a : K, extremalDirectionalDerivative b L = MvPolynomial.C a := by
    by_cases he : m - w k = 0
    · refine ⟨c, ?_⟩
      rw [hblock, he, initialForm_eq_self_of_isWeightedHomogeneous
        (MvPolynomial.isWeightedHomogeneous_C w c)]
    · refine ⟨0, ?_⟩
      rw [hblock, initialForm_eq_zero_of_isWeightedHomogeneous
        (MvPolynomial.isWeightedHomogeneous_C w c) _ he, map_zero]
  obtain ⟨a,ha⟩ := hconst
  let N := extremalKernelShear b k
  let Q := weightedLinearSubstitution N P
  have hN : N.det = 1 := extremalKernelShear_det b k
  have hNb := extremalKernelShear_respects_weight w b k hb
  have hcapQ := weightedLinearSubstitution_isWeightLE w N hNb m P hcap
  have hoptQ := hopt.substitution N hN
  have hdetQ : hessianDeterminant Q = 1 := by
    change hessianDeterminant (weightedLinearSubstitution N P) = 1
    rw [weightedLinearSubstitution_det N hN, hdet, map_one]
  have hp : pderiv k (initialForm w m Q) = MvPolynomial.C (a * (b k)⁻¹) := by
    change pderiv k (initialForm w m (weightedLinearSubstitution N P)) = _
    rw [weightedLinearSubstitution_initialForm w N hNb]
    change pderiv k (weightedLinearSubstitution (extremalKernelShear b k) L) = _
    rw [extremalKernelShear_partial L b k hbk, ha]
    have he : weightedLinearSubstitution (extremalKernelShear b k) (MvPolynomial.C a) = MvPolynomial.C a :=
      (weightedLinearSubstitution (extremalKernelShear b k)).commutes a
    rw [he, map_mul]
  exact globalWeightOptimum_no_constant_partial Q w m hw hm hcapQ hclock hoptQ hdetQ k _ hp

end
end HC4.Polynomial

#print axioms HC4.Polynomial.globalWeightOptimum_no_constantHessianKernel
