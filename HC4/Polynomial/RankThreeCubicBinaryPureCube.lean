import Mathlib.Tactic

/-!
# Binary cubic Hessian degeneracy forces a pure cube

Consider a binary cubic, in divided-power coordinates,

  f(u,v) = a*u³ + 3*b*u²*v + 3*c*u*v² + d*v³.

Up to the common factor 6, its Hessian is

  [a*u+b*v, b*u+c*v; b*u+c*v, c*u+d*v].

The determinant is a binary quadratic. Vanishing at the three
points (1,0), (0,1), and (1,1) already forces its three
coefficients to vanish, hence the cubic is a pure cube of a
linear form (possibly the zero polynomial).

The result holds over arbitrary characteristic-zero fields; no
algebraic closure or cube roots are required. In fact the explicit
coordinate proof below works in any field.
-/

namespace HC4.Polynomial.RankThreeCubic

noncomputable section

/-- The determinant of the binary Hessian after dividing all
entries by the common nonzero factor 6. -/
def binaryCubicReducedHessianDet
    {K : Type*} [CommRing K]
    (a b c d u v : K) : K :=
  (a * u + b * v) * (c * u + d * v) -
    (b * u + c * v) ^ 2

/-- The three coefficients of the reduced Hessian determinant. -/
theorem binaryCubicReducedHessianDet_expansion
    {K : Type*} [CommRing K]
    (a b c d u v : K) :
    binaryCubicReducedHessianDet a b c d u v =
      (a * c - b ^ 2) * u ^ 2 +
      (a * d - b * c) * u * v +
      (b * d - c ^ 2) * v ^ 2 := by
  unfold binaryCubicReducedHessianDet
  ring

/-- Three evaluations suffice to force the binary Hessian
quadratic to vanish coefficientwise. -/
theorem binaryCubicReducedHessianDet_threeZeros
    {K : Type*} [CommRing K]
    (a b c d : K)
    (h10 : binaryCubicReducedHessianDet a b c d 1 0 = 0)
    (h01 : binaryCubicReducedHessianDet a b c d 0 1 = 0)
    (h11 : binaryCubicReducedHessianDet a b c d 1 1 = 0) :
    a * c = b ^ 2 ∧ a * d = b * c ∧ b * d = c ^ 2 := by
  have hac : a * c - b ^ 2 = 0 := by
    simpa [binaryCubicReducedHessianDet_expansion] using h10
  have hbd : b * d - c ^ 2 = 0 := by
    simpa [binaryCubicReducedHessianDet_expansion] using h01
  have had : a * d - b * c = 0 := by
    have h := h11
    rw [binaryCubicReducedHessianDet_expansion] at h
    simp only [one_pow, mul_one, one_mul, add_zero] at h
    rw [hac, hbd] at h
    simpa using h
  exact ⟨sub_eq_zero.mp hac, sub_eq_zero.mp had, sub_eq_zero.mp hbd⟩

/-- If the reduced binary cubic Hessian is identically singular,
the binary cubic is either supported solely in v³ or is an
explicit cube a*(u + (b/a)*v)^3.

The first case includes the zero cubic. The second case is
valid without adjoining roots, since the leading coefficient
a is kept outside the cube. -/
theorem binaryCubic_pureCube_of_reducedHessian_threeZeros
    {K : Type*} [Field K]
    (a b c d : K)
    (h10 : binaryCubicReducedHessianDet a b c d 1 0 = 0)
    (h01 : binaryCubicReducedHessianDet a b c d 0 1 = 0)
    (h11 : binaryCubicReducedHessianDet a b c d 1 1 = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0) ∨
      (a ≠ 0 ∧
        ∀ u v : K,
          a * u ^ 3 + 3 * b * u ^ 2 * v +
              3 * c * u * v ^ 2 + d * v ^ 3 =
            a * (u + (b / a) * v) ^ 3) := by
  obtain ⟨hac, had, hbd⟩ :=
    binaryCubicReducedHessianDet_threeZeros a b c d h10 h01 h11
  by_cases ha : a = 0
  · left
    have hb2 : b ^ 2 = 0 := by simpa [ha] using hac.symm
    have hb : b = 0 := (pow_eq_zero hb2)
    have hc2 : c ^ 2 = 0 := by simpa [hb] using hbd.symm
    have hc : c = 0 := (pow_eq_zero hc2)
    exact ⟨ha, hb, hc⟩
  · right
    refine ⟨ha, ?_⟩
    have hc : c = b ^ 2 / a := (eq_div_iff ha).2 (by simpa only [pow_two] using hac)
    have hd : d = b ^ 3 / a ^ 2 := by
      rw [hc] at had
      apply (eq_div_iff (pow_ne_zero 2 ha)).2
      calc
        d * a ^ 2 = a * (a * d) := by ring
        _ = a * (b * (b ^ 2 / a)) := by rw [had]
        _ = b ^ 3 := by field_simp [ha] <;> ring
    intro u v
    rw [hc, hd]
    field_simp [ha]
    ring

/-- A pointwise vanishing binary Hessian minor yields the
same explicit pure-cube classification. -/
theorem binaryCubic_pureCube_of_reducedHessian_zero
    {K : Type*} [Field K]
    (a b c d : K)
    (hzero : ∀ u v : K,
      binaryCubicReducedHessianDet a b c d u v = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0) ∨
      (a ≠ 0 ∧
        ∀ u v : K,
          a * u ^ 3 + 3 * b * u ^ 2 * v +
              3 * c * u * v ^ 2 + d * v ^ 3 =
            a * (u + (b / a) * v) ^ 3) :=
  binaryCubic_pureCube_of_reducedHessian_threeZeros a b c d
    (hzero 1 0) (hzero 0 1) (hzero 1 1)

end
end HC4.Polynomial.RankThreeCubic
