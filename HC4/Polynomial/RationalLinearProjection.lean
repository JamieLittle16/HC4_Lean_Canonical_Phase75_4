import Mathlib

/-!
# Exact rational linear projection and attainment

Fourier--Motzkin elimination over the rationals, with non-strict
inequalities only. A finite system with one distinguished scalar
parameter projects to finitely many closed affine inequalities
in that parameter. If the parameter is bounded above and feasible,
its maximum is attained in the rationals.

No topological compactness over the rationals is assumed.
-/

namespace HC4.Polynomial

open scoped BigOperators

noncomputable section

/-- Feasibility of a finite system in one scalar is precisely
consistency of the zero rows and of every lower/upper pair. -/
theorem rational_scalar_feasible_iff
    {ι : Type*} (S : Finset ι) (a b : ι → ℚ) :
    (∃ x : ℚ, ∀ i ∈ S, a i * x ≤ b i) ↔
      (∀ i ∈ S, a i = 0 → 0 ≤ b i) ∧
      (∀ i ∈ S, ∀ j ∈ S, 0 < a i → a j < 0 →
        a i * b j ≥ a j * b i) := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨?_, ?_⟩
    · intro i hi h
      simpa [h] using hx i hi
    · intro i hi j hj hip hjn
      have h1 := mul_le_mul_of_nonneg_left (hx j hj) (le_of_lt hip)
      have h2 := mul_le_mul_of_nonpos_left (hx i hi) (le_of_lt hjn)
      nlinarith
  · rintro ⟨hz, hp⟩
    let L := S.filter (fun i => a i < 0)
    let U := S.filter (fun i => 0 < a i)
    by_cases hL : L.Nonempty
    · obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image L (fun i => b i / a i) hL
      have hj' := Finset.mem_filter.mp hj
      refine ⟨b j / a j, ?_⟩
      intro i hi
      rcases lt_trichotomy (a i) 0 with hn | he | hpos
      · have hh := hmax i (Finset.mem_filter.mpr ⟨hi, hn⟩)
        exact (div_le_iff_of_neg' hn).mp hh
      · simpa [he] using hz i hi he
      · have hh := hp i hi j hj'.1 hpos hj'.2
        have hle : b j / a j ≤ b i / a i := by
          apply (div_le_iff_of_neg hj'.2).mpr
          have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ (a i)⁻¹ by positivity)
          calc
            (b i / a i) * a j = (a i)⁻¹ * (a j * b i) := by ring
            _ ≤ (a i)⁻¹ * (a i * b j) := hh'
            _ = b j := by field_simp
        exact (le_div_iff₀' hpos).mp hle
    · by_cases hU : U.Nonempty
      · obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image U (fun i => b i / a i) hU
        refine ⟨b j / a j, ?_⟩
        intro i hi
        rcases lt_trichotomy (a i) 0 with hn | he | hpos
        · exact (hL ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩).elim
        · simpa [he] using hz i hi he
        · exact (le_div_iff₀' hpos).mp (hmin i (Finset.mem_filter.mpr ⟨hi, hpos⟩))
      · refine ⟨0, ?_⟩
        intro i hi
        have he : a i = 0 := by
          rcases lt_trichotomy (a i) 0 with hn | he | hp
          · exact (hL ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩).elim
          · exact he
          · exact (hU ⟨i, Finset.mem_filter.mpr ⟨hi, hp⟩⟩).elim
        simpa [he] using hz i hi he

/-- A rational affine inequality with n eliminable variables
and one retained scalar parameter. -/
structure RationalProjectionRow (n : ℕ) where
  coeff : Fin n → ℚ
  slope : ℚ
  rhs : ℚ

namespace RationalProjectionRow

instance (n : ℕ) : DecidableEq (RationalProjectionRow n) := Classical.decEq _

def holds {n : ℕ} (r : RationalProjectionRow n) (t : ℚ) (x : Fin n → ℚ) : Prop :=
  (∑ i, r.coeff i * x i) + r.slope * t ≤ r.rhs

def tail {n : ℕ} (r : RationalProjectionRow (n+1)) : RationalProjectionRow n :=
  ⟨fun i => r.coeff i.succ, r.slope, r.rhs⟩

/-- The positive-row and negative-row cancellation. -/
def cancelPair {n : ℕ} (p q : RationalProjectionRow (n+1)) :
    RationalProjectionRow n :=
  ⟨fun i => p.coeff 0 * q.coeff i.succ - q.coeff 0 * p.coeff i.succ,
   p.coeff 0 * q.slope - q.coeff 0 * p.slope,
   p.coeff 0 * q.rhs - q.coeff 0 * p.rhs⟩

def eliminate {n : ℕ} (S : Finset (RationalProjectionRow (n+1))) :
    Finset (RationalProjectionRow n) := by
  classical
  exact (S.filter (fun r => r.coeff 0 = 0)).image tail ∪
    ((S.product S).filter (fun pq => 0 < pq.1.coeff 0 ∧ pq.2.coeff 0 < 0)).image
      (fun pq => cancelPair pq.1 pq.2)

set_option maxHeartbeats 4000000 in
theorem eliminate_iff {n : ℕ} (S : Finset (RationalProjectionRow (n+1)))
    (t : ℚ) (x : Fin n → ℚ) :
    (∀ r ∈ eliminate S, r.holds t x) ↔
      ∃ z : ℚ, ∀ r ∈ S, r.holds t (Fin.cons z x) := by
  classical
  let a := fun r : RationalProjectionRow (n+1) => r.coeff 0
  let b := fun r : RationalProjectionRow (n+1) =>
    r.rhs - ((∑ i : Fin n, r.coeff i.succ * x i) + r.slope * t)
  have hrow (r : RationalProjectionRow (n+1)) (z : ℚ) :
      r.holds t (Fin.cons z x) ↔ a r * z ≤ b r := by
    simp only [holds, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, a, b]
    constructor <;> intro h <;> linarith only [h]
  have hzero (r : RationalProjectionRow (n+1)) :
      r.tail.holds t x ↔ 0 ≤ b r := by
    simp only [tail, holds, b]
    constructor <;> intro h <;> linarith only [h]
  have hpair (p q : RationalProjectionRow (n+1)) :
      (cancelPair p q).holds t x ↔ a p * b q ≥ a q * b p := by
    simp only [cancelPair, holds, a, b, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum]
    constructor <;> intro h <;> linarith
  have he : (∃ z : ℚ, ∀ r ∈ S, r.holds t (Fin.cons z x)) ↔
      ∃ z : ℚ, ∀ r ∈ S, a r * z ≤ b r := by
    constructor <;> rintro ⟨z, hz⟩ <;> refine ⟨z, ?_⟩
    · intro r hr
      exact (hrow r z).mp (hz r hr)
    · intro r hr
      exact (hrow r z).mpr (hz r hr)
  rw [he, rational_scalar_feasible_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro r hr hz
      apply (hzero r).mp
      apply h
      unfold eliminate
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨r, Finset.mem_filter.mpr ⟨hr, hz⟩, rfl⟩)
    · intro p hp q hq hpos hneg
      apply (hpair p q).mp
      apply h
      unfold eliminate
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(p,q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩, hpos,hneg⟩, rfl⟩)
  · rintro ⟨hz, hp⟩ r hr
    unfold eliminate at hr
    rcases Finset.mem_union.mp hr with h | h
    · obtain ⟨p, hmem, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hm, ha⟩ := Finset.mem_filter.mp hmem
      exact (hzero p).mpr (hz p hm ha)
    · obtain ⟨⟨p,q⟩, hmem, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hm, hpos, hneg⟩ := Finset.mem_filter.mp hmem
      obtain ⟨hpm, hqm⟩ := Finset.mem_product.mp hm
      exact (hpair p q).mpr (hp p hpm q hqm hpos hneg)

/-- Eliminate all auxiliary variables, retaining precisely the
feasible set of the distinguished scalar. -/
def project : (n : ℕ) → Finset (RationalProjectionRow n) → Finset (RationalProjectionRow 0)
  | 0, S => S
  | n+1, S => project n (eliminate S)

set_option maxHeartbeats 4000000 in
theorem project_iff (n : ℕ) (S : Finset (RationalProjectionRow n)) (t : ℚ) :
    (∀ r ∈ project n S, r.slope * t ≤ r.rhs) ↔
      ∃ x : Fin n → ℚ, ∀ r ∈ S, r.holds t x := by
  induction n with
  | zero =>
    simp only [project]
    constructor
    · intro h
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      intro r hr
      simpa [holds] using h r hr
    · rintro ⟨x, hx⟩ r hr
      simpa [holds] using hx r hr
  | succ n ih =>
    change (∀ r ∈ project n (eliminate S), r.slope * t ≤ r.rhs) ↔ _
    rw [ih]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz⟩ := (eliminate_iff S t x).mp hx
      exact ⟨Fin.cons z x, hz⟩
    · rintro ⟨x, hx⟩
      refine ⟨Fin.tail x, (eliminate_iff S t (Fin.tail x)).mpr ⟨x 0, ?_⟩⟩
      intro r hr
      simpa using hx r hr

/-- Exact rational maximum attainment for a nonempty finite
system with a bounded retained scalar. -/
theorem exists_max_parameter (n : ℕ) (S : Finset (RationalProjectionRow n))
    (hne : ∃ t : ℚ, ∃ x : Fin n → ℚ, ∀ r ∈ S, r.holds t x)
    (B : ℚ)
    (hbound : ∀ t : ℚ, (∃ x : Fin n → ℚ, ∀ r ∈ S, r.holds t x) → t ≤ B) :
    ∃ t : ℚ, ∃ x : Fin n → ℚ, (∀ r ∈ S, r.holds t x) ∧
      ∀ u : ℚ, (∃ y : Fin n → ℚ, ∀ r ∈ S, r.holds u y) → u ≤ t := by
  classical
  obtain ⟨t₀, x₀, h₀⟩ := hne
  let T := project n S
  let U := T.filter (fun r => 0 < r.slope)
  have ht₀ := (project_iff n S t₀).mpr ⟨x₀, h₀⟩
  have hU : U.Nonempty := by
    by_contra hn
    let v := max t₀ (B+1)
    have hv : ∀ r ∈ T, r.slope * v ≤ r.rhs := by
      intro r hr
      have hs : r.slope ≤ 0 := by
        by_contra hp
        exact hn ⟨r, Finset.mem_filter.mpr ⟨hr, lt_of_not_ge hp⟩⟩
      exact (mul_le_mul_of_nonpos_left (le_max_left _ _) hs).trans (ht₀ r hr)
    have hb := hbound v ((project_iff n S v).mp hv)
    have hh : B+1 ≤ v := le_max_right _ _
    linarith
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image U (fun r => r.rhs / r.slope) hU
  have hr' := Finset.mem_filter.mp hr
  let t := r.rhs / r.slope
  have h₀t : t₀ ≤ t := (le_div_iff₀' hr'.2).mpr (ht₀ r hr'.1)
  have ht : ∀ q ∈ T, q.slope * t ≤ q.rhs := by
    intro q hq
    by_cases hpos : 0 < q.slope
    · exact (le_div_iff₀' hpos).mp (hmin q (Finset.mem_filter.mpr ⟨hq,hpos⟩))
    · exact (mul_le_mul_of_nonpos_left h₀t (le_of_not_gt hpos)).trans (ht₀ q hq)
  obtain ⟨x, hx⟩ := (project_iff n S t).mp ht
  refine ⟨t,x,hx,?_⟩
  intro u hu
  exact (le_div_iff₀' hr'.2).mpr ((project_iff n S u).mpr hu r hr'.1)

end RationalProjectionRow
end
end HC4.Polynomial

#print axioms HC4.Polynomial.RationalProjectionRow.exists_max_parameter
