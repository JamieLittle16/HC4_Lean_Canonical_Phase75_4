module

public import HC4.Polynomial.NonnegativeTerminalAssembly

/-!
# Actual finite-support first wall

Increase a nonnegative collection of weights that is invisible
to the old maximal layer. The first event is the minimum of the
zero-clock time and the contact times of actual supported monomials.
Clear the denominator of the selected time to obtain integral weights.

This proves a source-native continuation, not termination of a
sequence of arbitrary wall changes.
-/

public section

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

private theorem firstWall_weight_nonneg
    (v : σ → ℤ) (hv : ∀ i, 0 ≤ v i) (u : σ →₀ ℕ) :
    0 ≤ Finsupp.weight v u := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun i _ => nsmul_nonneg (hv i) _)

theorem firstWall_weight_scaled_add
    (w v : σ → ℤ) (a b : ℤ) (u : σ →₀ ℕ) :
    Finsupp.weight (fun i => b * w i + a * v i) u =
      b * Finsupp.weight w u + a * Finsupp.weight v u := by
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

set_option maxHeartbeats 4000000 in
/-- A nonnegative slope invisible on the old face can be followed
to a genuine new wall or to zero determinant clock. The old face
is exactly the old component of the new face, and the new clock
is strictly smaller after normalizing by the scale factor. -/
theorem exists_weighted_firstWall_or_zeroClock
    (w v : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hcap : IsWeightLE w m P)
    (hW : 0 < (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i))
    (hvsum : 0 < ∑ i : σ, v i)
    (hinvisible : ∀ u ∈ P.support, Finsupp.weight w u = m →
      Finsupp.weight v u = 0) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧
      let w' : σ → ℤ := fun i => b * w i + a * v i
      let m' := b * m
      let W' := (Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i)
      (∀ i, 0 ≤ w' i) ∧ IsWeightLE w' m' P ∧
      0 ≤ W' ∧ W' < b * ((Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i)) ∧
      initialForm w m (initialForm w' m' P) = initialForm w m P ∧
      (W' = 0 ∨ ∃ u ∈ P.support, Finsupp.weight w u < m ∧
        Finsupp.weight v u > 0 ∧ Finsupp.weight w' u = m') := by
  classical
  let W := (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i)
  let V := 2 * (∑ i : σ, v i)
  have hW0 : 0 < W := hW
  have hV : 0 < V := by dsimp [V]; omega
  let S := P.support.filter (fun u => 0 < Finsupp.weight v u)
  let C : Finset (ℤ × ℤ) := insert (W, V)
    (S.image (fun u => (m - Finsupp.weight w u, Finsupp.weight v u)))
  have hC : C.Nonempty := ⟨(W,V), by simp [C]⟩
  have hpos (c : ℤ × ℤ) (hc : c ∈ C) : 0 < c.1 ∧ 0 < c.2 := by
    rcases Finset.mem_insert.mp hc with he | he
    · subst c
      exact ⟨hW0, hV⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
      have hu' := Finset.mem_filter.mp hu
      have hb := hcap hu'.1
      have hn : Finsupp.weight w u ≠ m := by
        intro he
        have hz := hinvisible u hu'.1 he
        omega
      exact ⟨by omega, hu'.2⟩
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image C
    (fun p : ℤ × ℤ => (p.1 : ℚ) / (p.2 : ℚ)) hC
  let a := c.1
  let b := c.2
  have ha : 0 < a := (hpos c hc).1
  have hb : 0 < b := (hpos c hc).2
  have hcross (p : ℤ × ℤ) (hp : p ∈ C) : a * p.2 ≤ p.1 * b := by
    have he := hmin p hp
    change (a : ℚ) / (b : ℚ) ≤ (p.1 : ℚ) / (p.2 : ℚ) at he
    have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hpq : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast (hpos p hp).2
    exact_mod_cast (div_le_div_iff₀ hbq hpq).mp he
  have hclock := hcross (W,V) (by simp [C])
  change a * V ≤ W * b at hclock
  let w' : σ → ℤ := fun i => b * w i + a * v i
  let m' := b * m
  let W' := (Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i)
  have hW' : W' = b * W - a * V := by
    dsimp [W', m', w', W, V]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hAV : 0 < a * V := mul_pos ha hV
  have hcap' : IsWeightLE w' m' P := by
    intro u hu
    change Finsupp.weight (fun i => b * w i + a * v i) u ≤ b * m
    rw [firstWall_weight_scaled_add]
    have hn := firstWall_weight_nonneg v hv u
    by_cases hz : Finsupp.weight v u = 0
    · rw [hz, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hcap hu) (le_of_lt hb)
    · have hp : (m - Finsupp.weight w u, Finsupp.weight v u) ∈ C := by
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨u, Finset.mem_filter.mpr ⟨hu, by omega⟩, rfl⟩
      have he := hcross _ hp
      change a * Finsupp.weight v u ≤ (m - Finsupp.weight w u) * b at he
      nlinarith
  have hold : initialForm w m (initialForm w' m' P) = initialForm w m P := by
    ext u
    simp only [coeff_initialForm]
    by_cases hu : Finsupp.weight w u = m
    · rw [if_pos hu, if_pos hu]
      by_cases hz : coeff u P = 0
      · simp [hz]
      · have hv0 := hinvisible u (MvPolynomial.mem_support_iff.mpr hz) hu
        have he : Finsupp.weight w' u = m' := by
          change Finsupp.weight (fun i => b * w i + a * v i) u = b * m
          rw [firstWall_weight_scaled_add, hu, hv0, mul_zero, add_zero]
        rw [if_pos he]
    · rw [if_neg hu, if_neg hu]
  refine ⟨a, b, ha, hb, ?_⟩
  change (∀ i, 0 ≤ w' i) ∧ IsWeightLE w' m' P ∧
    0 ≤ W' ∧ W' < b * W ∧
    initialForm w m (initialForm w' m' P) = initialForm w m P ∧
    (W' = 0 ∨ ∃ u ∈ P.support, Finsupp.weight w u < m ∧
      Finsupp.weight v u > 0 ∧ Finsupp.weight w' u = m')
  refine ⟨fun i => add_nonneg (mul_nonneg (le_of_lt hb) (hw i))
      (mul_nonneg (le_of_lt ha) (hv i)), hcap', ?_, ?_, hold, ?_⟩
  · rw [hW', mul_comm b W]
    omega
  · rw [hW']
    omega
  · rcases Finset.mem_insert.mp hc with he | he
    · left
      have ha' : a = W := congrArg Prod.fst he
      have hb' : b = V := congrArg Prod.snd he
      rw [hW', ha', hb']
      ring
    · right
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp he
      have hu' := Finset.mem_filter.mp hu
      have ha' : a = m - Finsupp.weight w u := (congrArg Prod.fst heq).symm
      have hb' : b = Finsupp.weight v u := (congrArg Prod.snd heq).symm
      refine ⟨u, hu'.1, by omega, hu'.2, ?_⟩
      change Finsupp.weight (fun i => b * w i + a * v i) u = b * m
      rw [firstWall_weight_scaled_add, ha', hb']
      ring


set_option maxHeartbeats 4000000 in
/-- First contact for arbitrary signed weights and invisible signed slopes.
This permits the negative omitted weight in a Taylor-normalised relative
phase. The argument uses finite support, not positivity of coordinates. -/
theorem exists_signedWeight_firstWall_or_zeroClock
    (w v : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P)
    (hW : 0 < (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i))
    (hvsum : 0 < ∑ i : σ, v i)
    (hinvisible : ∀ u ∈ P.support, Finsupp.weight w u = m →
      Finsupp.weight v u = 0) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧
      let w' : σ → ℤ := fun i => b * w i + a * v i
      let m' := b * m
      let W' := (Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i)
      IsWeightLE w' m' P ∧
      0 ≤ W' ∧ W' < b * ((Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i)) ∧
      initialForm w m (initialForm w' m' P) = initialForm w m P ∧
      (W' = 0 ∨ ∃ u ∈ P.support, Finsupp.weight w u < m ∧
        Finsupp.weight v u > 0 ∧ Finsupp.weight w' u = m') := by
  classical
  let W := (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i)
  let V := 2 * (∑ i : σ, v i)
  have hW0 : 0 < W := hW
  have hV : 0 < V := by dsimp [V]; omega
  let S := P.support.filter (fun u => 0 < Finsupp.weight v u)
  let C : Finset (ℤ × ℤ) := insert (W, V)
    (S.image (fun u => (m - Finsupp.weight w u, Finsupp.weight v u)))
  have hC : C.Nonempty := ⟨(W,V), by simp [C]⟩
  have hpos (c : ℤ × ℤ) (hc : c ∈ C) : 0 < c.1 ∧ 0 < c.2 := by
    rcases Finset.mem_insert.mp hc with he | he
    · subst c
      exact ⟨hW0, hV⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
      have hu' := Finset.mem_filter.mp hu
      have hb := hcap hu'.1
      have hn : Finsupp.weight w u ≠ m := by
        intro he
        have hz := hinvisible u hu'.1 he
        omega
      exact ⟨by omega, hu'.2⟩
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image C
    (fun p : ℤ × ℤ => (p.1 : ℚ) / (p.2 : ℚ)) hC
  let a := c.1
  let b := c.2
  have ha : 0 < a := (hpos c hc).1
  have hb : 0 < b := (hpos c hc).2
  have hcross (p : ℤ × ℤ) (hp : p ∈ C) : a * p.2 ≤ p.1 * b := by
    have he := hmin p hp
    change (a : ℚ) / (b : ℚ) ≤ (p.1 : ℚ) / (p.2 : ℚ) at he
    have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hpq : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast (hpos p hp).2
    exact_mod_cast (div_le_div_iff₀ hbq hpq).mp he
  have hclock := hcross (W,V) (by simp [C])
  change a * V ≤ W * b at hclock
  let w' : σ → ℤ := fun i => b * w i + a * v i
  let m' := b * m
  let W' := (Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i)
  have hW' : W' = b * W - a * V := by
    dsimp [W', m', w', W, V]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hAV : 0 < a * V := mul_pos ha hV
  have hcap' : IsWeightLE w' m' P := by
    intro u hu
    change Finsupp.weight (fun i => b * w i + a * v i) u ≤ b * m
    rw [firstWall_weight_scaled_add]
    by_cases hz : Finsupp.weight v u ≤ 0
    · have hneg := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hz
      have hbound := mul_le_mul_of_nonneg_left (hcap hu) (le_of_lt hb)
      linarith
    · have hp : (m - Finsupp.weight w u, Finsupp.weight v u) ∈ C := by
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨u, Finset.mem_filter.mpr ⟨hu, by omega⟩, rfl⟩
      have he := hcross _ hp
      change a * Finsupp.weight v u ≤ (m - Finsupp.weight w u) * b at he
      nlinarith
  have hold : initialForm w m (initialForm w' m' P) = initialForm w m P := by
    ext u
    simp only [coeff_initialForm]
    by_cases hu : Finsupp.weight w u = m
    · rw [if_pos hu, if_pos hu]
      by_cases hz : coeff u P = 0
      · simp [hz]
      · have hv0 := hinvisible u (MvPolynomial.mem_support_iff.mpr hz) hu
        have he : Finsupp.weight w' u = m' := by
          change Finsupp.weight (fun i => b * w i + a * v i) u = b * m
          rw [firstWall_weight_scaled_add, hu, hv0, mul_zero, add_zero]
        rw [if_pos he]
    · rw [if_neg hu, if_neg hu]
  refine ⟨a, b, ha, hb, ?_⟩
  change IsWeightLE w' m' P ∧
    0 ≤ W' ∧ W' < b * W ∧
    initialForm w m (initialForm w' m' P) = initialForm w m P ∧
    (W' = 0 ∨ ∃ u ∈ P.support, Finsupp.weight w u < m ∧
      Finsupp.weight v u > 0 ∧ Finsupp.weight w' u = m')
  refine ⟨hcap', ?_, ?_, hold, ?_⟩
  · rw [hW', mul_comm b W]
    omega
  · rw [hW']
    omega
  · rcases Finset.mem_insert.mp hc with he | he
    · left
      have ha' : a = W := congrArg Prod.fst he
      have hb' : b = V := congrArg Prod.snd he
      rw [hW', ha', hb']
      ring
    · right
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp he
      have hu' := Finset.mem_filter.mp hu
      have ha' : a = m - Finsupp.weight w u := (congrArg Prod.fst heq).symm
      have hb' : b = Finsupp.weight v u := (congrArg Prod.snd heq).symm
      refine ⟨u, hu'.1, by omega, hu'.2, ?_⟩
      change Finsupp.weight (fun i => b * w i + a * v i) u = b * m
      rw [firstWall_weight_scaled_add, ha', hb']
      ring


set_option maxHeartbeats 4000000 in
/-- Signed first contact refining an old face: negative-slope old terms
may drop, while its slope-zero subface is preserved exactly. -/
theorem exists_signedWeight_refining_firstWall
    (w v : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P)
    (hW : 0 < (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i))
    (hvsum : 0 < ∑ i : σ, v i)
    (hinvisible : ∀ u ∈ P.support, Finsupp.weight w u = m →
      Finsupp.weight v u ≤ 0) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧
      let w' : σ → ℤ := fun i => b * w i + a * v i
      let m' := b * m
      let W' := (Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i)
      IsWeightLE w' m' P ∧
      0 ≤ W' ∧ W' < b * ((Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i)) ∧
      initialForm w m (initialForm w' m' P) = initialForm v 0 (initialForm w m P) ∧
      (W' = 0 ∨ ∃ u ∈ P.support, Finsupp.weight w u < m ∧
        Finsupp.weight v u > 0 ∧ Finsupp.weight w' u = m') := by
  classical
  let W := (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i)
  let V := 2 * (∑ i : σ, v i)
  have hW0 : 0 < W := hW
  have hV : 0 < V := by dsimp [V]; omega
  let S := P.support.filter (fun u => 0 < Finsupp.weight v u)
  let C : Finset (ℤ × ℤ) := insert (W, V)
    (S.image (fun u => (m - Finsupp.weight w u, Finsupp.weight v u)))
  have hC : C.Nonempty := ⟨(W,V), by simp [C]⟩
  have hpos (c : ℤ × ℤ) (hc : c ∈ C) : 0 < c.1 ∧ 0 < c.2 := by
    rcases Finset.mem_insert.mp hc with he | he
    · subst c
      exact ⟨hW0, hV⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
      have hu' := Finset.mem_filter.mp hu
      have hb := hcap hu'.1
      have hn : Finsupp.weight w u ≠ m := by
        intro he
        have hz := hinvisible u hu'.1 he
        omega
      exact ⟨by omega, hu'.2⟩
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image C
    (fun p : ℤ × ℤ => (p.1 : ℚ) / (p.2 : ℚ)) hC
  let a := c.1
  let b := c.2
  have ha : 0 < a := (hpos c hc).1
  have hb : 0 < b := (hpos c hc).2
  have hcross (p : ℤ × ℤ) (hp : p ∈ C) : a * p.2 ≤ p.1 * b := by
    have he := hmin p hp
    change (a : ℚ) / (b : ℚ) ≤ (p.1 : ℚ) / (p.2 : ℚ) at he
    have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hpq : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast (hpos p hp).2
    exact_mod_cast (div_le_div_iff₀ hbq hpq).mp he
  have hclock := hcross (W,V) (by simp [C])
  change a * V ≤ W * b at hclock
  let w' : σ → ℤ := fun i => b * w i + a * v i
  let m' := b * m
  let W' := (Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i)
  have hW' : W' = b * W - a * V := by
    dsimp [W', m', w', W, V]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hAV : 0 < a * V := mul_pos ha hV
  have hcap' : IsWeightLE w' m' P := by
    intro u hu
    change Finsupp.weight (fun i => b * w i + a * v i) u ≤ b * m
    rw [firstWall_weight_scaled_add]
    by_cases hz : Finsupp.weight v u ≤ 0
    · have hneg := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hz
      have hbound := mul_le_mul_of_nonneg_left (hcap hu) (le_of_lt hb)
      linarith
    · have hp : (m - Finsupp.weight w u, Finsupp.weight v u) ∈ C := by
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨u, Finset.mem_filter.mpr ⟨hu, by omega⟩, rfl⟩
      have he := hcross _ hp
      change a * Finsupp.weight v u ≤ (m - Finsupp.weight w u) * b at he
      nlinarith
  have hold : initialForm w m (initialForm w' m' P) =
      initialForm v 0 (initialForm w m P) := by
    ext u
    simp only [coeff_initialForm]
    by_cases hu : Finsupp.weight w u = m
    · have he : Finsupp.weight w' u = m' ↔ Finsupp.weight v u = 0 := by
        change Finsupp.weight (fun i => b * w i + a * v i) u = b*m ↔ _
        rw [firstWall_weight_scaled_add,hu]
        constructor
        · intro h
          have hz : a * Finsupp.weight v u = 0 := by linarith
          exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
        · intro h
          rw [h,mul_zero,add_zero]
      rw [if_pos hu,if_pos hu]
      simp only [he]
    · rw [if_neg hu,if_neg hu]
      split_ifs <;> rfl
  refine ⟨a, b, ha, hb, ?_⟩
  change IsWeightLE w' m' P ∧
    0 ≤ W' ∧ W' < b * W ∧
    initialForm w m (initialForm w' m' P) = initialForm v 0 (initialForm w m P) ∧
    (W' = 0 ∨ ∃ u ∈ P.support, Finsupp.weight w u < m ∧
      Finsupp.weight v u > 0 ∧ Finsupp.weight w' u = m')
  refine ⟨hcap', ?_, ?_, hold, ?_⟩
  · rw [hW', mul_comm b W]
    omega
  · rw [hW']
    omega
  · rcases Finset.mem_insert.mp hc with he | he
    · left
      have ha' : a = W := congrArg Prod.fst he
      have hb' : b = V := congrArg Prod.snd he
      rw [hW', ha', hb']
      ring
    · right
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp he
      have hu' := Finset.mem_filter.mp hu
      have ha' : a = m - Finsupp.weight w u := (congrArg Prod.fst heq).symm
      have hb' : b = Finsupp.weight v u := (congrArg Prod.snd heq).symm
      refine ⟨u, hu'.1, by omega, hu'.2, ?_⟩
      change Finsupp.weight (fun i => b * w i + a * v i) u = b * m
      rw [firstWall_weight_scaled_add, ha', hb']
      ring

end
end HC4.Polynomial

#print axioms HC4.Polynomial.exists_weighted_firstWall_or_zeroClock

#print axioms HC4.Polynomial.exists_signedWeight_firstWall_or_zeroClock

#print axioms HC4.Polynomial.exists_signedWeight_refining_firstWall
