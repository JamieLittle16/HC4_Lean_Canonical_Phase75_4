import HC4.Polynomial.WeightedGlobalOptimum

/-!
# Positive-clock global extremal obstruction

At an attained global optimum the old face forbids every
infinitesimal improving weight slope, including signed slopes
at strictly positive coordinates. A sufficiently large integral
rescaling makes the perturbation feasible on the entire source.

The obstruction holds in every determinant-one weight-compatible
chart of the extremal source. It is stronger than the fixed-source
missing-coordinate obstruction and does not assume a wall producer.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The source-local formulation of global normalized optimality. -/
def IsGlobalWeightOptimum (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ) : Prop :=
  ∀ (N : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → ℤ) (n : ℤ),
    N.det = 1 → (∀ i, 0 ≤ v i) → 0 < n →
    IsWeightLE v n (weightedLinearSubstitution N P) →
    0 ≤ (Fintype.card (Fin 4) : ℤ)*n - 2*(∑ i, v i) →
    (∑ i : Fin 4, (v i : ℚ)/(n : ℚ)) ≤ ∑ i : Fin 4, (w i : ℚ)/(m : ℚ)

theorem weightedLinearSubstitution_one (P : MvPolynomial (Fin 4) K) :
    weightedLinearSubstitution (1 : Matrix (Fin 4) (Fin 4) K) P = P := by
  classical
  have he : weightedLinearSubstitution (1 : Matrix (Fin 4) (Fin 4) K) =
      AlgHom.id K (MvPolynomial (Fin 4) K) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [weightedLinearSubstitution, MvPolynomial.aeval_X]
    change (∑ j : Fin 4, MvPolynomial.C ((1 : Matrix (Fin 4) (Fin 4) K) i j) * X j) = X i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.one_apply, Ne.symm hj]
    · simp
  exact AlgHom.congr_fun he P

/-- Optimality transfers to every determinant-one chart, with the
same reference value; composition cannot leave the linear orbit. -/
theorem IsGlobalWeightOptimum.substitution
    {P : MvPolynomial (Fin 4) K} {w : Fin 4 → ℤ} {m : ℤ}
    (hopt : IsGlobalWeightOptimum P w m)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : M.det = 1) :
    IsGlobalWeightOptimum (weightedLinearSubstitution M P) w m := by
  intro N v n hN hv hn hcap hclock
  rw [weightedLinearSubstitution_comp] at hcap
  exact hopt (M*N) v n (by rw [Matrix.det_mul, hM, hN, mul_one]) hv hn hcap hclock

set_option maxHeartbeats 4000000 in
/-- An arbitrary counterexample can be placed in a globally
optimal, strictly positive-clock presentation. -/
theorem exists_counterexample_globalWeightOptimum
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P)) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ),
      M.det = 1 ∧ (∀ i, 0 ≤ w i) ∧ 0 < m ∧
      let Q := weightedLinearSubstitution M P
      IsWeightLE w m Q ∧ hessianDeterminant Q = 1 ∧
      ¬ Function.Injective (mvGradientMap Q) ∧
      0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i) ∧
      IsGlobalWeightOptimum Q w m := by
  obtain ⟨M,w,m,hM,hw,hm,hcap,hclock,hopt⟩ := exists_global_integralWeightOptimum P
  let Q := weightedLinearSubstitution M P
  have hdetQ : hessianDeterminant Q = 1 := by
    change hessianDeterminant (weightedLinearSubstitution M P) = 1
    rw [weightedLinearSubstitution_det M hM, hdet, map_one]
  have hnQ : ¬ Function.Injective (mvGradientMap Q) := by
    intro h
    exact hnoninj ((weightedLinearSubstitution_gradient_injective_iff M hM P).mp h)
  have hpos : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i) := by
    by_contra h
    exact hnQ (gradient_injective_of_nonnegativeWeight_zeroClock_of_JC2
      hJC2 w hw m hm Q hcap (by omega) hdetQ)
  refine ⟨M,w,m,hM,hw,hm,hcap,hdetQ,hnQ,hpos,?_⟩
  exact IsGlobalWeightOptimum.substitution hopt M hM

set_option maxHeartbeats 4000000 in
/-- A signed slope with positive sum and no increase on the old
face gives a feasible strict improvement, unless the clock is zero.
The scale is chosen explicitly from the finite support and slope. -/
theorem globalWeightOptimum_no_improvingSlope
    (P : MvPolynomial (Fin 4) K) (w v : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m)
    (hvzero : ∀ i, w i = 0 → 0 ≤ v i)
    (hvsum : 0 < ∑ i, v i) :
    ∃ u ∈ (initialForm w m P).support, 0 < Finsupp.weight v u := by
  classical
  by_contra hn
  push_neg at hn
  let A : ℤ := ∑ i : Fin 4, |v i|
  let B : ℤ := ∑ u ∈ P.support, |Finsupp.weight v u|
  let b : ℤ := 1 + 2*A + B
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun u _ => abs_nonneg (Finsupp.weight v u))
  have hb : 0 < b := by dsimp [b]; omega
  have hvi (i : Fin 4) : |v i| ≤ A := by
    exact Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
  have hVu (u : Fin 4 →₀ ℕ) (hu : u ∈ P.support) : |Finsupp.weight v u| ≤ B := by
    exact Finset.single_le_sum (fun u _ => abs_nonneg (Finsupp.weight v u)) hu
  have hsum : (∑ i : Fin 4, v i) ≤ A :=
    Finset.sum_le_sum (fun i _ => le_abs_self (v i))
  let w' : Fin 4 → ℤ := fun i => b*w i + v i
  let m' := b*m
  have hw' (i : Fin 4) : 0 ≤ w' i := by
    by_cases hi : w i = 0
    · simpa [w', hi] using hvzero i hi
    · have hwi : 1 ≤ w i := by have h := hw i; omega
      have hmul : b*1 ≤ b*w i := mul_le_mul_of_nonneg_left hwi (le_of_lt hb)
      have hav := neg_abs_le (v i)
      have hv := hvi i
      change 0 ≤ b*w i + v i
      dsimp [b] at *
      omega
  have hcap' : IsWeightLE w' m' P := by
    intro u hu
    change Finsupp.weight (fun i => b*w i + v i) u ≤ b*m
    have hfun : (fun i => b*w i + v i) = (fun i => b*w i + 1*v i) := by simp
    rw [hfun, firstWall_weight_scaled_add, one_mul]
    by_cases he : Finsupp.weight w u = m
    · have hz := hn u ((mem_support_initialForm_iff w m P u).mpr ⟨hu,he⟩)
      rw [he]
      omega
    · have hgap : Finsupp.weight w u + 1 ≤ m := by
        have h := hcap hu
        omega
      have hmul := mul_le_mul_of_nonneg_left hgap (le_of_lt hb)
      rw [mul_add, mul_one] at hmul
      have hv := hVu u hu
      have hva := le_abs_self (Finsupp.weight v u)
      dsimp [b] at *
      omega
  have hclock' : 0 ≤ (Fintype.card (Fin 4) : ℤ)*m' - 2*(∑ i, w' i) := by
    have hW : 1 ≤ (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i) := by omega
    have hmul := mul_le_mul_of_nonneg_left hW (le_of_lt hb)
    have hcalc : (Fintype.card (Fin 4) : ℤ)*m' - 2*(∑ i, w' i) =
        b*((Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i)) - 2*(∑ i, v i) := by
      dsimp [m',w']
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [hcalc]
    rw [mul_one] at hmul
    dsimp [b] at *
    omega
  have hh := hopt (1 : Matrix (Fin 4) (Fin 4) K) w' m' Matrix.det_one hw'
    (mul_pos hb hm) (by rw [weightedLinearSubstitution_one]; exact hcap') hclock'
  rw [← Finset.sum_div, ← Finset.sum_div] at hh
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hm'q : (0 : ℚ) < (m' : ℚ) := by exact_mod_cast mul_pos hb hm
  have he := (div_le_div_iff₀ hm'q hmq).mp hh
  have he' : (∑ i : Fin 4, w' i)*m ≤ (∑ i : Fin 4, w i)*m' := by
    exact_mod_cast he
  have hsum' : (∑ i : Fin 4, w' i) = b*(∑ i : Fin 4, w i) + ∑ i : Fin 4, v i := by
    dsimp [w']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum'] at he'
  change (b*(∑ i : Fin 4, w i) + ∑ i : Fin 4, v i)*m ≤
    (∑ i : Fin 4, w i)*(b*m) at he'
  have hpos := mul_pos hvsum hm
  nlinarith only [he', hpos]

/-- In every weight-compatible chart the extremal leading layer
contains each coordinate. This excludes the missing-variable
escape even after changing the linear chart. -/
theorem globalWeightOptimum_no_missing_coordinate
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m)
    (N : Matrix (Fin 4) (Fin 4) K) (hN : N.det = 1)
    (hblock : ∀ i j, w i ≠ w j → N i j = 0)
    (k : Fin 4) :
    pderiv k (initialForm w m (weightedLinearSubstitution N P)) ≠ 0 := by
  classical
  intro hk
  let Q := weightedLinearSubstitution N P
  let v : Fin 4 → ℤ := fun i => if i = k then 1 else 0
  have hcapQ := weightedLinearSubstitution_isWeightLE w N hblock m P hcap
  have hoptQ := hopt.substitution N hN
  have hv (i : Fin 4) : 0 ≤ v i := by
    by_cases hi : i = k <;> simp [v, hi]
  have hsum : (∑ i : Fin 4, v i) = 1 := by simp [v]
  obtain ⟨u, hu, hpos⟩ := globalWeightOptimum_no_improvingSlope Q w v m
    hw hm hcapQ hclock hoptQ (fun i _ => hv i) (by rw [hsum]; decide)
  have hz := exponent_eq_zero_of_pderiv_eq_zero k (initialForm w m Q) hk u
    (MvPolynomial.mem_support_iff.mp hu)
  have he : Finsupp.weight v u = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp [v, hz]
    · intro i
      simp
  omega

end
end HC4.Polynomial

#print axioms HC4.Polynomial.exists_counterexample_globalWeightOptimum
#print axioms HC4.Polynomial.globalWeightOptimum_no_improvingSlope
#print axioms HC4.Polynomial.globalWeightOptimum_no_missing_coordinate
