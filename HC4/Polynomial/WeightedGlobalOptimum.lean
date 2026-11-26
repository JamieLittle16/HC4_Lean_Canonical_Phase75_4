module

public import HC4.Polynomial.WeightedLinearOrbit
public import HC4.Polynomial.RationalLinearProjection

/-!
# Global normalized weight optimum over genuine linear charts

The admissible normalized weights are nonnegative, have sum at
most two, and give every actual supported exponent weight at most
one. Each realized support pattern is a finite rational linear
system. Choose its attained maximum, then maximize over the finite
set of realized patterns and clear denominators.

The resulting optimum ranges over every determinant-one linear
chart, not just weight-preserving shears.
-/

@[expose] public section

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators Matrix

noncomputable section

def normalizedWeightFeasible (T : Finset (Fin 4 →₀ ℕ)) (x : Fin 4 → ℚ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 2 ∧
    ∀ u ∈ T, (∑ i : Fin 4, (u i : ℚ) * x i) ≤ 1

def weightSupportRow (u : Fin 4 →₀ ℕ) : RationalProjectionRow 4 :=
  ⟨fun i => u i, 0, 1⟩

def weightNonnegRow (j : Fin 4) : RationalProjectionRow 4 :=
  ⟨fun i => if i = j then -1 else 0, 0, 0⟩

def weightSumRow : RationalProjectionRow 4 := ⟨fun _ => 1, -1, 0⟩
def weightSumReverseRow : RationalProjectionRow 4 := ⟨fun _ => -1, 1, 0⟩
def weightBoundRow : RationalProjectionRow 4 := ⟨fun _ => 0, 1, 2⟩

def weightOptimizationRows (T : Finset (Fin 4 →₀ ℕ)) : Finset (RationalProjectionRow 4) :=
  ((T.image weightSupportRow ∪ Finset.univ.image weightNonnegRow) ∪
    {weightSumRow, weightSumReverseRow, weightBoundRow})

theorem weightOptimizationRows_iff (T : Finset (Fin 4 →₀ ℕ)) (t : ℚ) (x : Fin 4 → ℚ) :
    (∀ r ∈ weightOptimizationRows T, r.holds t x) ↔
      normalizedWeightFeasible T x ∧ t = ∑ i, x i := by
  classical
  have hn (j : Fin 4) : (weightNonnegRow j).holds t x ↔ 0 ≤ x j := by
    simp only [weightNonnegRow, RationalProjectionRow.holds, zero_mul, add_zero]
    have he : (∑ i : Fin 4, (if i = j then (-1 : ℚ) else 0) * x i) = -x j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
    rw [he]
    constructor <;> intro h <;> linarith only [h]
  have hs : weightSumRow.holds t x ↔ (∑ i, x i) ≤ t := by
    simp only [weightSumRow, RationalProjectionRow.holds, one_mul, neg_mul]
    constructor <;> intro h <;> linarith only [h]
  have hr : weightSumReverseRow.holds t x ↔ t ≤ ∑ i, x i := by
    simp only [weightSumReverseRow, RationalProjectionRow.holds, neg_mul, one_mul,
      Finset.sum_neg_distrib]
    constructor <;> intro h <;> linarith only [h]
  have hb : weightBoundRow.holds t x ↔ t ≤ 2 := by
    simp [weightBoundRow, RationalProjectionRow.holds]
  have hu (u : Fin 4 →₀ ℕ) : (weightSupportRow u).holds t x ↔
      (∑ i : Fin 4, (u i : ℚ) * x i) ≤ 1 := by
    simp [weightSupportRow, RationalProjectionRow.holds]
  constructor
  · intro h
    have hmem (r : RationalProjectionRow 4)
        (hr' : r ∈ ({weightSumRow, weightSumReverseRow, weightBoundRow} :
          Finset (RationalProjectionRow 4))) : r.holds t x :=
      h r (Finset.mem_union_right _ hr')
    have h1 := hs.mp (hmem _ (by simp))
    have h2 := hr.mp (hmem _ (by simp))
    have ht : t = ∑ i, x i := le_antisymm h2 h1
    refine ⟨⟨?_, ?_, ?_⟩, ht⟩
    · intro i
      apply (hn i).mp
      apply h
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    · rw [← ht]
      exact hb.mp (hmem _ (by simp))
    · intro u hsu
      apply (hu u).mp
      apply h
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨u, hsu, rfl⟩))
  · rintro ⟨⟨hpos, hbound, hcap⟩, ht⟩ r hm
    change r ∈ ((T.image weightSupportRow ∪ Finset.univ.image weightNonnegRow) ∪
      {weightSumRow, weightSumReverseRow, weightBoundRow}) at hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp hm
        exact (hu u).mpr (hcap u hu')
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
        exact (hn i).mpr (hpos i)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · exact hs.mpr (by rw [ht])
      · exact hr.mpr (by rw [ht])
      · exact hb.mpr (by rw [ht]; exact hbound)

theorem exists_max_normalizedWeight (T : Finset (Fin 4 →₀ ℕ)) :
    ∃ x : Fin 4 → ℚ, normalizedWeightFeasible T x ∧
      ∀ y : Fin 4 → ℚ, normalizedWeightFeasible T y → (∑ i, y i) ≤ ∑ i, x i := by
  have hzero : normalizedWeightFeasible T (fun _ => 0) := by
    simp [normalizedWeightFeasible]
  obtain ⟨t, x, hx, hmax⟩ := RationalProjectionRow.exists_max_parameter 4
    (weightOptimizationRows T)
    ⟨0, fun _ => 0, (weightOptimizationRows_iff T _ _).mpr ⟨hzero, by simp⟩⟩
    2 (by
      rintro t ⟨x, hx⟩
      obtain ⟨hf, ht⟩ := (weightOptimizationRows_iff T t x).mp hx
      rw [ht]
      exact hf.2.1)
  obtain ⟨hf, ht⟩ := (weightOptimizationRows_iff T t x).mp hx
  refine ⟨x, hf, ?_⟩
  intro y hy
  rw [← ht]
  exact hmax _ ⟨y, (weightOptimizationRows_iff T _ _).mpr ⟨hy, rfl⟩⟩

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 4000000 in
/-- The exact rational maximum over all actual determinant-one charts. -/
theorem exists_global_normalizedWeight (P : MvPolynomial (Fin 4) K) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (x : Fin 4 → ℚ),
      M.det = 1 ∧ normalizedWeightFeasible (weightedLinearSubstitution M P).support x ∧
      ∀ (N : Matrix (Fin 4) (Fin 4) K) (y : Fin 4 → ℚ), N.det = 1 →
        normalizedWeightFeasible (weightedLinearSubstitution N P).support y →
        (∑ i, y i) ≤ ∑ i, x i := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_linearOrbit_support_patterns P
  have hne : S.Nonempty :=
    ⟨(weightedLinearSubstitution (1 : Matrix (Fin 4) (Fin 4) K) P).support,
      (hS _).mpr ⟨1, Matrix.det_one, rfl⟩⟩
  choose x hx hmax using exists_max_normalizedWeight
  obtain ⟨T, hT, hopt⟩ := Finset.exists_max_image S (fun T => ∑ i, x T i) hne
  obtain ⟨M, hM, hMT⟩ := (hS T).mp hT
  refine ⟨M, x T, hM, ?_, ?_⟩
  · rw [hMT]
    exact hx T
  · intro N y hN hy
    let U := (weightedLinearSubstitution N P).support
    have hU : U ∈ S := (hS U).mpr ⟨N, hN, rfl⟩
    exact (hmax U y hy).trans (hopt U hU)

/-- Clearing a common positive denominator of a finite rational vector. -/
theorem exists_integral_normalizedWeight (x : Fin 4 → ℚ) :
    ∃ (w : Fin 4 → ℤ) (m : ℤ), 0 < m ∧
      ∀ i, (w i : ℚ) / (m : ℚ) = x i := by
  classical
  let m : ℤ := ∏ i : Fin 4, ((x i).den : ℤ)
  let w : Fin 4 → ℤ := fun i => (x i).num *
    ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, ((x j).den : ℤ)
  have hpos : 0 < m := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast (x i).den_pos
  refine ⟨w,m,hpos,?_⟩
  intro i
  let d : ℤ := ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, ((x j).den : ℤ)
  have hd : 0 < d := by
    apply Finset.prod_pos
    intro j _
    exact_mod_cast (x j).den_pos
  have hm : m = ((x i).den : ℤ) * d :=
    (Finset.mul_prod_erase Finset.univ (fun j : Fin 4 => ((x j).den : ℤ))
      (Finset.mem_univ i)).symm
  change (((x i).num * d : ℤ) : ℚ) / (m : ℚ) = x i
  rw [hm]
  push_cast
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  rw [mul_div_mul_right _ _ hdq]
  exact Rat.num_div_den (x i)

/-- Integral weights and normalized rational weights give the same
linear inequality after multiplying by the positive cap. -/
theorem normalizedWeightFeasible_iff_integral
    (T : Finset (Fin 4 →₀ ℕ)) (w : Fin 4 → ℤ) (m : ℤ) (hm : 0 < m) :
    normalizedWeightFeasible T (fun i => (w i : ℚ) / (m : ℚ)) ↔
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) ≤ 2*m ∧
        ∀ u ∈ T, Finsupp.weight w u ≤ m := by
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hsum : (∑ i : Fin 4, (w i : ℚ) / (m : ℚ)) =
      ((∑ i : Fin 4, w i : ℤ) : ℚ) / (m : ℚ) := by
    rw [← Finset.sum_div]
    push_cast <;> rfl
  have hu (u : Fin 4 →₀ ℕ) :
      (∑ i : Fin 4, (u i : ℚ) * ((w i : ℚ) / (m : ℚ))) =
        (Finsupp.weight w u : ℚ) / (m : ℚ) := by
    simp only [← mul_div_assoc, ← Finset.sum_div]
    congr 1
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · push_cast
      simp [nsmul_eq_mul]
    · intro i
      simp
  constructor
  · rintro ⟨hpos,hb,hcap⟩
    refine ⟨?_,?_,?_⟩
    · intro i
      have he := (le_div_iff₀ hmq).mp (hpos i)
      rw [zero_mul] at he
      exact_mod_cast he
    · rw [hsum] at hb
      exact_mod_cast (div_le_iff₀ hmq).mp hb
    · intro u hmem
      have he := hcap u hmem
      rw [hu] at he
      have he' := (div_le_iff₀ hmq).mp he
      exact_mod_cast (show (Finsupp.weight w u : ℚ) ≤ (m : ℚ) by simpa using he')
  · rintro ⟨hpos,hb,hcap⟩
    refine ⟨?_,?_,?_⟩
    · intro i
      exact div_nonneg (by exact_mod_cast hpos i) (le_of_lt hmq)
    · rw [hsum]
      apply (div_le_iff₀ hmq).mpr
      exact_mod_cast hb
    · intro u hmem
      rw [hu]
      apply (div_le_iff₀ hmq).mpr
      simp only [one_mul]
      exact_mod_cast hcap u hmem

set_option maxHeartbeats 4000000 in
/-- The attained global optimum, with integer weights and actual chart. -/
theorem exists_global_integralWeightOptimum (P : MvPolynomial (Fin 4) K) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ),
      M.det = 1 ∧ (∀ i, 0 ≤ w i) ∧ 0 < m ∧
      IsWeightLE w m (weightedLinearSubstitution M P) ∧
      0 ≤ (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i) ∧
      ∀ (N : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → ℤ) (n : ℤ),
        N.det = 1 → (∀ i, 0 ≤ v i) → 0 < n →
        IsWeightLE v n (weightedLinearSubstitution N P) →
        0 ≤ (Fintype.card (Fin 4) : ℤ)*n - 2*(∑ i, v i) →
        (∑ i : Fin 4, (v i : ℚ)/(n : ℚ)) ≤ ∑ i : Fin 4, (w i : ℚ)/(m : ℚ) := by
  obtain ⟨M,x,hM,hx,hmax⟩ := exists_global_normalizedWeight P
  obtain ⟨w,m,hm,hw⟩ := exists_integral_normalizedWeight x
  have he : (fun i => (w i : ℚ)/(m : ℚ)) = x := funext hw
  have hf := (normalizedWeightFeasible_iff_integral _ w m hm).mp
    (show normalizedWeightFeasible (weightedLinearSubstitution M P).support
      (fun i => (w i : ℚ)/(m : ℚ)) by rw [he]; exact hx)
  refine ⟨M,w,m,hM,hf.1,hm,hf.2.2,?_,?_⟩
  · have hh := hf.2.1
    norm_num
    omega
  · intro N v n hN hv hn hcap hclock
    have hs : (∑ i, v i) ≤ 2*n := by
      norm_num at hclock
      omega
    have hy := (normalizedWeightFeasible_iff_integral
      (weightedLinearSubstitution N P).support v n hn).mpr ⟨hv,hs,hcap⟩
    rw [show (∑ i : Fin 4, (w i : ℚ)/(m : ℚ)) = ∑ i, x i by simp only [hw]]
    exact hmax N _ hN hy

end
end HC4.Polynomial

#print axioms HC4.Polynomial.exists_global_integralWeightOptimum
