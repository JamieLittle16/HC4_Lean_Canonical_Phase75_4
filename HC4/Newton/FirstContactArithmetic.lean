import Mathlib

/-!
# Arithmetic of the first non-facet contact weight

In the Newton reduction, the first contact weight is

    ω = (1,1,1,1) + λ e_j,

with `λ ≤ m-3`, where `m≥3` is the highest nonlinear degree.  The fixed
quadratic terms then have weight strictly below `m`, while the determinant
weight `4m-8-2λ` is positive.  These elementary inequalities are recorded
separately here.
-/

namespace HC4.Newton

/-- Quadratic terms stay strictly below the first nonlinear contact level. -/
theorem quadratic_weight_below_contact
    {m lam : ℕ} (hm : 3 ≤ m) (hlam : lam ≤ m - 3) :
    2 + lam < m := by
  omega

/-- The determinant weight at first contact is positive. -/
theorem first_contact_determinant_weight_pos
    {m lam : ℕ} (hm : 3 ≤ m) (hlam : lam ≤ m - 3) :
    0 < 4 * m - 8 - 2 * lam := by
  omega

/-- The stronger lower bound used in the manuscript. -/
theorem first_contact_determinant_weight_lower_bound
    {m lam : ℕ} (hm : 3 ≤ m) (hlam : lam ≤ m - 3) :
    2 * m - 2 ≤ 4 * m - 8 - 2 * lam := by
  omega

/-- In particular the determinant weight is strictly positive by the paper's bound. -/
theorem first_contact_positive_via_lower_bound
    {m lam : ℕ} (hm : 3 ≤ m) (hlam : lam ≤ m - 3) :
    0 < 4 * m - 8 - 2 * lam := by
  have hlower := first_contact_determinant_weight_lower_bound hm hlam
  have hpos : 0 < 2 * m - 2 := by omega
  omega

end HC4.Newton
