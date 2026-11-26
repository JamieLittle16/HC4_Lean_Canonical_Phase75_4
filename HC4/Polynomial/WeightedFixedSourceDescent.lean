import HC4.Polynomial.WeightedFirstWall

/-!
# Fixed-source wall progress and finite obstruction

On a fixed polynomial the leading support strictly grows at a
nonterminal first wall. Thus maximizing its cardinality among
admissible weights eliminates every invisible coordinate slope.

This is deliberately a fixed-source assertion: a later linear
change of chart need not preserve the leading support cardinality.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

/-- Exact support membership for a weighted layer. -/
theorem mem_support_initialForm_iff
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K) (u : σ →₀ ℕ) :
    u ∈ (initialForm w m P).support ↔
      u ∈ P.support ∧ Finsupp.weight w u = m := by
  classical
  simp only [MvPolynomial.mem_support_iff, coeff_initialForm]
  by_cases h : Finsupp.weight w u = m <;> simp [h]

/-- A new face retaining the old component retains every old
supported monomial. -/
theorem initialForm_support_subset_of_nested
    (w w' : σ → ℤ) (m m' : ℤ) (P : MvPolynomial σ K)
    (h : initialForm w m (initialForm w' m' P) = initialForm w m P) :
    (initialForm w m P).support ⊆ (initialForm w' m' P).support := by
  intro u hu
  rw [← h] at hu
  exact ((mem_support_initialForm_iff w m (initialForm w' m' P) u).mp hu).1

/-- Every nonterminal first wall has a strictly larger leading
support, not just a different weight vector. -/
theorem initialForm_support_card_lt_of_nested_new
    (w w' : σ → ℤ) (m m' : ℤ) (P : MvPolynomial σ K)
    (h : initialForm w m (initialForm w' m' P) = initialForm w m P)
    (u : σ →₀ ℕ) (hu : u ∈ P.support)
    (hbelow : Finsupp.weight w u < m) (hnew : Finsupp.weight w' u = m') :
    (initialForm w m P).support.card < (initialForm w' m' P).support.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨initialForm_support_subset_of_nested w w' m m' P h, ?_⟩
  intro he
  have hmem := (mem_support_initialForm_iff w' m' P u).mpr ⟨hu, hnew⟩
  rw [← he] at hmem
  exact (ne_of_lt hbelow) ((mem_support_initialForm_iff w m P u).mp hmem).2

/-- An actual missing variable supplies the required invisible
slope without an additional wall-existence assumption. -/
theorem exists_firstWall_of_missing_coordinate
    [CharZero K]
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hW : 0 < (Fintype.card σ : ℤ) * m - 2 * (∑ i : σ, w i))
    (k : σ) (hk : pderiv k (initialForm w m P) = 0) :
    ∃ (w' : σ → ℤ) (m' : ℤ),
      (∀ i, 0 ≤ w' i) ∧ 0 < m' ∧ IsWeightLE w' m' P ∧
      0 ≤ (Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i) ∧
      ((Fintype.card σ : ℤ) * m' - 2 * (∑ i : σ, w' i) = 0 ∨
        (initialForm w m P).support.card < (initialForm w' m' P).support.card) := by
  classical
  let v : σ → ℤ := fun i => if i = k then 1 else 0
  have hv (i : σ) : 0 ≤ v i := by
    by_cases hi : i = k <;> simp [v, hi]
  have hsum : (∑ i : σ, v i) = 1 := by simp [v]
  have hinv (u : σ →₀ ℕ) (hu : u ∈ P.support)
      (he : Finsupp.weight w u = m) : Finsupp.weight v u = 0 := by
    have hmem := (mem_support_initialForm_iff w m P u).mpr ⟨hu, he⟩
    have hcoeff := MvPolynomial.mem_support_iff.mp hmem
    have hk0 := exponent_eq_zero_of_pderiv_eq_zero k (initialForm w m P) hk u hcoeff
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp [v, hk0, smul_ite]
    · intro i
      simp
  obtain ⟨a, b, ha, hb, hnonneg, hcap', hW', _, hold, hout⟩ :=
    exists_weighted_firstWall_or_zeroClock w v m P hw hv hcap hW
      (by rw [hsum]; decide) hinv
  refine ⟨fun i => b * w i + a * v i, b * m,
    hnonneg, mul_pos hb hm, hcap', hW', ?_⟩
  rcases hout with hz | ⟨u, hu, hbelow, _, hnew⟩
  · exact Or.inl hz
  · exact Or.inr (initialForm_support_card_lt_of_nested_new w _ m _ P
      hold u hu hbelow hnew)

end

section FourVariables

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 4000000 in
/-- A hypothetical counterexample with an admissible presentation
has a fixed-source maximal face in which every variable occurs.
Any missing coordinate would force a terminal or strictly enlarge
the leading support, contradicting maximality.

This is not a coordinate-invariant maximality claim. -/
theorem exists_counterexample_fullSupport_face
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K)
    (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (w₀ : Fin 4 → ℤ) (m₀ : ℤ)
    (hw₀ : ∀ i, 0 ≤ w₀ i) (hm₀ : 0 < m₀)
    (hcap₀ : IsWeightLE w₀ m₀ P)
    (hclock₀ : 0 ≤ (Fintype.card (Fin 4) : ℤ) * m₀ - 2 * (∑ i : Fin 4, w₀ i)) :
    ∃ (w : Fin 4 → ℤ) (m : ℤ),
      (∀ i, 0 ≤ w i) ∧ 0 < m ∧ IsWeightLE w m P ∧
      0 < (Fintype.card (Fin 4) : ℤ) * m - 2 * (∑ i : Fin 4, w i) ∧
      ∀ k, pderiv k (initialForm w m P) ≠ 0 := by
  classical
  let admissible (w : Fin 4 → ℤ) (m : ℤ) : Prop :=
    (∀ i, 0 ≤ w i) ∧ 0 < m ∧ IsWeightLE w m P ∧
      0 ≤ (Fintype.card (Fin 4) : ℤ) * m - 2 * (∑ i : Fin 4, w i)
  let size (w : Fin 4 → ℤ) (m : ℤ) := (initialForm w m P).support.card
  have hsize (w : Fin 4 → ℤ) (m : ℤ) : size w m ≤ P.support.card := by
    apply Finset.card_le_card
    intro u hu
    exact ((mem_support_initialForm_iff w m P u).mp hu).1
  let S : Finset ℕ := (Finset.range (P.support.card + 1)).filter
    (fun n => ∃ w m, admissible w m ∧ size w m = n)
  have hmem (w : Fin 4 → ℤ) (m : ℤ) (h : admissible w m) :
      size w m ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hsize w m)), w, m, h, rfl⟩
  have hS : S.Nonempty := ⟨size w₀ m₀, hmem w₀ m₀ ⟨hw₀, hm₀, hcap₀, hclock₀⟩⟩
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨w, m, hadm, he⟩ := (Finset.mem_filter.mp hn).2
  obtain ⟨hw, hm, hcap, hclock⟩ := hadm
  have hpos : 0 < (Fintype.card (Fin 4) : ℤ) * m - 2 * (∑ i : Fin 4, w i) := by
    by_contra h
    exact hnoninj (gradient_injective_of_nonnegativeWeight_zeroClock_of_JC2
      hJC2 w hw m hm P hcap (by omega) hdet)
  refine ⟨w, m, hw, hm, hcap, hpos, ?_⟩
  intro k hk
  obtain ⟨w', m', hw', hm', hcap', hclock', hout⟩ :=
    exists_firstWall_of_missing_coordinate w m P hw hm hcap hpos k hk
  rcases hout with hz | hlt
  · exact hnoninj (gradient_injective_of_nonnegativeWeight_zeroClock_of_JC2
      hJC2 w' hw' m' hm' P hcap' hz hdet)
  · have hh := hmax (size w' m') (hmem w' m' ⟨hw', hm', hcap', hclock'⟩)
    change size w' m' ≤ n at hh
    change size w m < size w' m' at hlt
    omega

end FourVariables

end
end HC4.Polynomial

#print axioms HC4.Polynomial.exists_counterexample_fullSupport_face
