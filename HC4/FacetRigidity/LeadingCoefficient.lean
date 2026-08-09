import Mathlib

/-!
# Positivity of the extremal facet coefficient

For a leading term `c r^d p^M` (or its `q-s` analogue), the extremal
coefficient in the facet determinant equation contains

    M(2M-1) + n(3M-1)d + n²d².

The first summand is already positive for `M>0`, so this integer and its
characteristic-zero scalar image cannot vanish.
-/

namespace HC4.FacetRigidity

/-- The positive integer factor in the extremal facet coefficient. -/
def facetLeadingFactor (n M d : ℕ) : ℕ :=
  M * (2 * M - 1) + n * (3 * M - 1) * d + n ^ 2 * d ^ 2

/-- The extremal factor is strictly positive as soon as `M>0`. -/
theorem facetLeadingFactor_pos
    (n d : ℕ) {M : ℕ} (hM : 0 < M) :
    0 < facetLeadingFactor n M d := by
  have htwice : 0 < 2 * M - 1 := by omega
  have hfirst : 0 < M * (2 * M - 1) := Nat.mul_pos hM htwice
  unfold facetLeadingFactor
  omega

/-- Hence the extremal factor is nonzero. -/
theorem facetLeadingFactor_ne_zero
    (n d : ℕ) {M : ℕ} (hM : 0 < M) :
    facetLeadingFactor n M d ≠ 0 :=
  Nat.ne_of_gt (facetLeadingFactor_pos n d hM)

/-- Its image in any characteristic-zero field is nonzero. -/
theorem facetLeadingFactor_cast_ne_zero
    {K : Type*} [Field K] [CharZero K]
    (n d : ℕ) {M : ℕ} (hM : 0 < M) :
    ((facetLeadingFactor n M d : ℕ) : K) ≠ 0 := by
  exact_mod_cast facetLeadingFactor_ne_zero n d hM

/-- The full leading coefficient `M c² · factor` is nonzero. -/
theorem facetLeadingCoefficient_ne_zero
    {K : Type*} [Field K] [CharZero K]
    (n d : ℕ) {M : ℕ} (hM : 0 < M) {c : K} (hc : c ≠ 0) :
    (M : K) * c ^ 2 * (facetLeadingFactor n M d : K) ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hM) (pow_ne_zero 2 hc)
  · exact facetLeadingFactor_cast_ne_zero n d hM

end HC4.FacetRigidity
