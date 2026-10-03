import HC4.Polynomial.FiniteStaircaseCrossRoofHullArithmetic
import Mathlib.Tactic

/-!
# Mirrored cross-roof terminal arithmetic

When the same exposed cross-roof line is indexed from its high `z = 0`
endpoint by the `z` coordinate, the homogeneous fixed-`w` terminal relation
has base sum `(jHi+1)+v` and degree `q`.  Under fixed `w` the base sum is
exactly `jLo+1`, whereas `q = jLo+1-kLo` with `kLo>0`, so the relation is
impossible.
-/

namespace HC4.Polynomial

noncomputable section

/-- Mirrored fixed-`w` homogeneous terminal degree relation is impossible. -/
theorem no_crossRoof_fixed_w_mirror_terminal_degree_relation
    {kLo jLo kHi jHi q v : ℕ}
    (hkLo : 0 < kLo)
    (hq : q = jLo + 1 - kLo)
    (hv : v = kHi - jHi - 1)
    (hw : kHi = jLo + 1)
    (hdeg : jHi + 1 + v = q) : False := by
  omega

end

end HC4.Polynomial