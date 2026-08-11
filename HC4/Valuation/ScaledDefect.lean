import Mathlib.Tactic

/-!
# Ramification-normalised determinant defect

An exposure performed after parameter ramification by `R` records its
determinant order in the ramified parameter.  The geometric order is the
quotient `numerator / scale`; comparisons can be made without introducing
rational numbers by cross multiplication.

This file deliberately proves only the comparison arithmetic.  Positive
rationals are not well founded, so `ScaledDefect.LT` must not be used as the
outer termination relation until a uniform denominator or an unramified
re-entry theorem has been supplied.
-/

namespace HC4.Valuation

/-- A determinant order together with the parameter-ramification scale in
which it was measured. -/
structure ScaledDefect where
  numerator : ℕ
  scale : ℕ
  scale_pos : 0 < scale

namespace ScaledDefect

/-- The discrete normalized defect used by the outer induction.  Unlike the
cross-multiplication order on arbitrary rational scales, this takes values in
`ℕ` and is therefore suitable as a well-founded coordinate. -/
def normalizedNat (a : ScaledDefect) : ℕ :=
  a.numerator / a.scale

/-- Strict comparison of normalized orders, implemented by cross
multiplication. -/
def LT (a b : ScaledDefect) : Prop :=
  a.numerator * b.scale < b.numerator * a.scale

instance : _root_.LT ScaledDefect := ⟨ScaledDefect.LT⟩

/-- Equality of the represented normalized orders. -/
def Equivalent (a b : ScaledDefect) : Prop :=
  a.numerator * b.scale = b.numerator * a.scale

/-- The unramified presentation of an ordinary natural-valued defect. -/
def unramified (defect : ℕ) : ScaledDefect :=
  ⟨defect, 1, by omega⟩

/-- Spending a positive amount `c` from the ramified order `R * defect`
strictly decreases the normalized defect. -/
theorem ramified_sub_lt_unramified
    (defect R c : ℕ)
    (hR : 0 < R)
    (hc : 0 < c)
    (hle : c ≤ R * defect) :
    (ScaledDefect.mk (R * defect - c) R hR) <
      ScaledDefect.unramified defect := by
  change (R * defect - c) * 1 < defect * R
  simp only [Nat.mul_one]
  have hpos : 0 < R * defect := lt_of_lt_of_le hc hle
  have hsub : R * defect - c < R * defect := Nat.sub_lt hpos hc
  simpa [Nat.mul_comm] using hsub

/-- Spending a positive amount from `scale * defect` strictly decreases the
natural-number quotient by `scale`.  This is the discrete counterpart of
`ramified_sub_lt_unramified`; no divisibility of the spent amount by the
ramification scale is required. -/
theorem normalizedNat_ramified_sub_lt
    (defect scale cost : ℕ)
    (hscale : 0 < scale)
    (hcost : 0 < cost)
    (hle : cost ≤ scale * defect) :
    (scale * defect - cost) / scale < defect := by
  rw [Nat.div_lt_iff_lt_mul hscale]
  have hpos : 0 < scale * defect := lt_of_lt_of_le hcost hle
  have hsub : scale * defect - cost < scale * defect :=
    Nat.sub_lt hpos hcost
  simpa [Nat.mul_comm] using hsub

/-- Structure-valued form of `normalizedNat_ramified_sub_lt`. -/
theorem normalizedNat_mk_ramified_sub_lt_unramified
    (defect scale cost : ℕ)
    (hscale : 0 < scale)
    (hcost : 0 < cost)
    (hle : cost ≤ scale * defect) :
    normalizedNat (ScaledDefect.mk (scale * defect - cost) scale hscale) <
      normalizedNat (ScaledDefect.unramified defect) := by
  simpa [normalizedNat, unramified] using
    normalizedNat_ramified_sub_lt defect scale cost hscale hcost hle

/-- The combined Smith/ordinary-degree exposure spends `4*D-8`; hence for
`D>2` it strictly decreases normalized defect whenever the exposed family
is integral. -/
theorem adaptiveExposure_lt_unramified
    (defect R D : ℕ)
    (hR : 0 < R)
    (hD : 2 < D)
    (hle : 4 * D - 8 ≤ R * defect) :
    (ScaledDefect.mk (R * defect - (4 * D - 8)) R hR) <
      ScaledDefect.unramified defect := by
  apply ramified_sub_lt_unramified defect R (4 * D - 8) hR
  · omega
  · exact hle

/-- Choosing the ramification index to equal the positive exposure cost
makes the normalized successor defect exactly the preceding natural
number.  Thus the adaptive exposure itself need not introduce an
accumulating rational denominator: for `cost = 4*D-8`, its clock is a
scaled presentation of `defect-1`.

This is an arithmetic statement only; descending the exposed family to an
unramified parameter remains a separate geometric theorem. -/
theorem ramification_by_cost_equivalent_pred
    (defect cost : ℕ)
    (hcost : 0 < cost) :
    Equivalent
      (ScaledDefect.mk (cost * defect - cost) cost hcost)
      (ScaledDefect.unramified (defect - 1)) := by
  unfold Equivalent unramified
  simp only [Nat.mul_one]
  calc
    cost * defect - cost = cost * defect - cost * 1 := by simp
    _ = cost * (defect - 1) :=
      (Nat.mul_sub_left_distrib cost defect 1).symm
    _ = (defect - 1) * cost := Nat.mul_comm _ _

/-- Canonical specialization of `ramification_by_cost_equivalent_pred` to
the combined Smith/degree exposure. -/
theorem adaptiveExposure_canonicalScale_equivalent_pred
    (defect D : ℕ)
    (hD : 2 < D) :
    Equivalent
      (ScaledDefect.mk
        ((4 * D - 8) * defect - (4 * D - 8))
        (4 * D - 8) (by omega))
      (ScaledDefect.unramified (defect - 1)) := by
  exact ramification_by_cost_equivalent_pred
    defect (4 * D - 8) (by omega)

/-- The factor-`20` rigid closing clock has the same normalized-descent
form. -/
theorem rigidClosing_lt_unramified
    (defect q : ℕ)
    (hq : 0 < q)
    (hle : 2 * q ≤ 20 * defect) :
    (ScaledDefect.mk (20 * defect - 2 * q) 20 (by omega)) <
      ScaledDefect.unramified defect := by
  apply ramified_sub_lt_unramified defect 20 (2 * q) (by omega)
  · omega
  · exact hle

/-- The genuine factor-`20` kernel restart strictly decreases the discrete
normalized defect.  In particular, no hypothesis `10 ∣ q` is needed. -/
theorem rigidClosing_normalizedNat_lt
    (defect q : ℕ)
    (hq : 0 < q)
    (hle : 2 * q ≤ 20 * defect) :
    (20 * defect - 2 * q) / 20 < defect := by
  exact normalizedNat_ramified_sub_lt defect 20 (2 * q) (by omega) (by omega) hle

end ScaledDefect

end HC4.Valuation
