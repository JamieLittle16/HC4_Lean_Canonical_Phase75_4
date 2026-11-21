import HC4.Polynomial.RankThreeCubicFibrePencils

/-!
# Polynomial coefficient rigidity in the fixed-square reduction

Once a common singular direction is charted and its binary quadratic
coefficient has rank one, the transported derivative factors as a
scalar polynomial times a primitive linear form squared. These lemmas
separate the constant scalar and lock the primitive covector in place.
-/

namespace HC4.Polynomial.RankThreeCubic

open _root_.Polynomial

section

variable {K F : Type*} [Field K] [Field F]
variable (g : K →+* F)

private theorem eq_C_of_map_natDegree_eq_zero {p : Polynomial K}
    (h : (p.map g).natDegree = 0) : p = C (p.coeff 0) := by
  rw [natDegree_map_eq_of_injective g.injective] at h
  exact eq_C_of_natDegree_eq_zero h

private theorem natDegree_eq_zero_of_mul_eq_C {p q : Polynomial F} {c : F}
    (hc : c ≠ 0) (h : p * q = C c) : p.natDegree = 0 ∧ q.natDegree = 0 := by
  have hn : p * q ≠ 0 := by simpa [h] using hc
  have hd := natDegree_mul (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn)
  rw [h, natDegree_C] at hd
  omega

/-- A primitive rank-one square factor cannot have a varying scalar
when its transported value is a nonzero constant. The transported
linear form is its constant term as well. -/
theorem constant_scalar_and_square_root_of_transport
    (a : Polynomial K) (q : Polynomial F) {b : F} (hb : b ≠ 0)
    (h : a.map g * q ^ 2 = C b) :
    a = C (a.coeff 0) ∧ q = C (q.coeff 0) := by
  rcases natDegree_eq_zero_of_mul_eq_C hb h with ⟨ha, hq⟩
  refine ⟨eq_C_of_map_natDegree_eq_zero g ha, ?_⟩
  rw [natDegree_pow] at hq
  exact eq_C_of_natDegree_eq_zero (by omega)

private theorem primitive_pair_constant_of_right_relation
    (a b : Polynomial K) (hab : IsCoprime a b) {r s : F} (hs : s ≠ 0)
    (h : C r * a.map g + C s * b.map g = 0) :
    a = C (a.coeff 0) ∧ b = C (b.coeff 0) := by
  have he : b.map g = C (-r / s) * a.map g := by
    have hC : C s ≠ 0 := C_ne_zero.mpr hs
    apply mul_left_cancel₀ hC
    calc
      C s * b.map g = -(C r * a.map g) := by linear_combination h
      _ = C s * (C (-r / s) * a.map g) := by
        rw [← mul_assoc, ← C_mul, mul_comm s, div_mul_cancel₀ _ hs, C_neg, neg_mul]
  obtain ⟨m, n, hmn⟩ := hab
  have hn : a.map g * (m.map g + C (-r / s) * n.map g) = C (1 : F) := by
    have hmap := congrArg (mapRingHom g) hmn
    change (m * a + n * b).map g = (1 : Polynomial K).map g at hmap
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, he] at hmap
    rw [C_1, ← hmap]
    ring
  have hd := (natDegree_eq_zero_of_mul_eq_C one_ne_zero hn).1
  refine ⟨eq_C_of_map_natDegree_eq_zero g hd, eq_C_of_map_natDegree_eq_zero g ?_⟩
  rw [he]
  exact le_antisymm (le_trans natDegree_mul_le (by simp [hd])) (Nat.zero_le _)

/-- A primitive binary covector with a constant nonzero annihilator
over an extension field is independent of the longitudinal parameter. -/
theorem primitive_pair_constant_of_relation
    (a b : Polynomial K) (hab : IsCoprime a b) {r s : F}
    (hrs : r ≠ 0 ∨ s ≠ 0) (h : C r * a.map g + C s * b.map g = 0) :
    a = C (a.coeff 0) ∧ b = C (b.coeff 0) := by
  rcases hrs with hr | hs
  · exact (primitive_pair_constant_of_right_relation g b a hab.symm hr (by simpa [add_comm] using h)).symm
  · exact primitive_pair_constant_of_right_relation g a b hab hs h

private theorem constant_of_mul_eq_constant
    (m p : Polynomial F) (hm : m ≠ 0) {b : F} (h : m * p = C b) :
    p = C (p.coeff 0) := by
  by_cases hb : b = 0
  · have hp : p = 0 := (mul_eq_zero.mp (by simpa [hb] using h)).resolve_left hm
    simp [hp]
  · exact eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_mul_eq_C hb h).2

/-- The two coefficient routes of the square-direction argument.
If the two transverse velocities have a nonzero fibre derivative,
differentiate the transported linear form to obtain a constant
annihilator. If both derivatives vanish, differentiating the two
gradient outputs supplies the same nonzero multiplier on both
covector entries. Either way the original primitive covector is fixed. -/
theorem primitive_pair_constant_of_square_transport
    (a b : Polynomial K) (hab : IsCoprime a b)
    (r s : F)
    (hlinear : C r * a.map g + C s * b.map g = 0)
    (hgradient : r = 0 → s = 0 →
      ∃ m : Polynomial F, m.coeff 0 = 1 ∧
        m * a.map g = C (g (a.coeff 0)) ∧ m * b.map g = C (g (b.coeff 0))) :
    a = C (a.coeff 0) ∧ b = C (b.coeff 0) := by
  by_cases h : r = 0 ∧ s = 0
  · obtain ⟨m, hm, ha, hb⟩ := hgradient h.1 h.2
    have hn : m ≠ 0 := by
      intro he
      simp [he] at hm
    constructor
    · apply Polynomial.map_injective g g.injective
      simpa [coeff_map] using constant_of_mul_eq_constant m (a.map g) hn ha
    · apply Polynomial.map_injective g g.injective
      simpa [coeff_map] using constant_of_mul_eq_constant m (b.map g) hn hb
  · exact primitive_pair_constant_of_relation g a b hab (not_and_or.mp h) hlinear

end

end HC4.Polynomial.RankThreeCubic
