import Mathlib.Tactic

/-!
# Mixed-orientation endpoint coefficient contradiction

The `V=1` mixed-orientation rank-three paper branch ends in two exact extremal
coefficient equations

    2 A D = B C,
    A D = 2 B C,

with nonzero endpoint coefficients.  This tiny state-free lemma owns the final
characteristic-zero scalar contradiction; source-facing files only need to
produce the two equations and the endpoint nonvanishing facts.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The two mixed-orientation extremal equations are incompatible when the
relevant endpoint product is nonzero. -/
theorem mixedOrientation_endpoint_coefficients_impossible
    (A B C D : K)
    (hB : B ≠ 0) (hC : C ≠ 0)
    (h₁ : 2 * A * D = B * C)
    (h₂ : A * D = 2 * B * C) :
    False := by
  have hBC : B * C ≠ 0 := mul_ne_zero hB hC
  have hthreeBC : (3 : K) * (B * C) = 0 := by
    linear_combination 2 * h₁ - 4 * h₂
  exact (mul_ne_zero (by norm_num) hBC) hthreeBC

end

end HC4.Polynomial
