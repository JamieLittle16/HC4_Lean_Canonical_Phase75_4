import HC4.Polynomial.WeightedInitial
import Mathlib

/-!
# Weak and strict weight bounds for multivariate polynomials

This module records the support inequalities needed to make the phrase
"top weighted part" precise.  `IsWeightLE w m p` means that every monomial
of `p` has weight at most `m`, while `IsWeightLT w m p` means that every
monomial has weight strictly less than `m`.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped Pointwise

noncomputable section

variable {σ K : Type*} [CommRing K]

/-- Every monomial in `p` has `w`-weight at most `m`. -/
def IsWeightLE (w : σ → ℤ) (m : ℤ) (p : MvPolynomial σ K) : Prop :=
  ∀ ⦃d : σ →₀ ℕ⦄, d ∈ p.support → Finsupp.weight w d ≤ m

/-- Every monomial in `p` has `w`-weight strictly below `m`. -/
def IsWeightLT (w : σ → ℤ) (m : ℤ) (p : MvPolynomial σ K) : Prop :=
  ∀ ⦃d : σ →₀ ℕ⦄, d ∈ p.support → Finsupp.weight w d < m

@[simp]
theorem isWeightLE_zero (w : σ → ℤ) (m : ℤ) :
    IsWeightLE (K := K) w m 0 := by
  intro d hd
  simp at hd

@[simp]
theorem isWeightLT_zero (w : σ → ℤ) (m : ℤ) :
    IsWeightLT (K := K) w m 0 := by
  intro d hd
  simp at hd

/-- A strict upper weight bound is also a weak upper bound. -/
theorem IsWeightLT.isWeightLE {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLT w m p) : IsWeightLE w m p := by
  intro d hd
  exact le_of_lt (hp hd)

/-- Weak weight bounds are preserved under addition. -/
theorem IsWeightLE.add [DecidableEq σ]
    {w : σ → ℤ} {m : ℤ} {p q : MvPolynomial σ K}
    (hp : IsWeightLE w m p) (hq : IsWeightLE w m q) :
    IsWeightLE w m (p + q) := by
  intro d hd
  have hd' : d ∈ p.support ∪ q.support := MvPolynomial.support_add hd
  rcases Finset.mem_union.mp hd' with hdp | hdq
  · exact hp hdp
  · exact hq hdq

/-- Strict weight bounds are preserved under addition. -/
theorem IsWeightLT.add [DecidableEq σ]
    {w : σ → ℤ} {m : ℤ} {p q : MvPolynomial σ K}
    (hp : IsWeightLT w m p) (hq : IsWeightLT w m q) :
    IsWeightLT w m (p + q) := by
  intro d hd
  have hd' : d ∈ p.support ∪ q.support := MvPolynomial.support_add hd
  rcases Finset.mem_union.mp hd' with hdp | hdq
  · exact hp hdp
  · exact hq hdq

/-- Negation does not change the monomial support bound. -/
theorem IsWeightLE.neg
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLE w m p) : IsWeightLE w m (-p) := by
  intro d hd
  have hneg : MvPolynomial.coeff d (-p) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcoeff : MvPolynomial.coeff d p ≠ 0 := by
    intro hz
    apply hneg
    simp [hz]
  exact hp (MvPolynomial.mem_support_iff.mpr hcoeff)

/-- Negation does not change the strict monomial support bound. -/
theorem IsWeightLT.neg
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLT w m p) : IsWeightLT w m (-p) := by
  intro d hd
  have hneg : MvPolynomial.coeff d (-p) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcoeff : MvPolynomial.coeff d p ≠ 0 := by
    intro hz
    apply hneg
    simp [hz]
  exact hp (MvPolynomial.mem_support_iff.mpr hcoeff)

/-- Weak weight bounds are preserved under subtraction. -/
theorem IsWeightLE.sub [DecidableEq σ]
    {w : σ → ℤ} {m : ℤ} {p q : MvPolynomial σ K}
    (hp : IsWeightLE w m p) (hq : IsWeightLE w m q) :
    IsWeightLE w m (p - q) := by
  simpa [sub_eq_add_neg] using hp.add hq.neg

/-- Strict weight bounds are preserved under subtraction. -/
theorem IsWeightLT.sub [DecidableEq σ]
    {w : σ → ℤ} {m : ℤ} {p q : MvPolynomial σ K}
    (hp : IsWeightLT w m p) (hq : IsWeightLT w m q) :
    IsWeightLT w m (p - q) := by
  simpa [sub_eq_add_neg] using hp.add hq.neg

/-- Products add weak upper weight bounds. -/
theorem IsWeightLE.mul [DecidableEq σ]
    {w : σ → ℤ} {m n : ℤ} {p q : MvPolynomial σ K}
    (hp : IsWeightLE w m p) (hq : IsWeightLE w n q) :
    IsWeightLE w (m + n) (p * q) := by
  intro d hd
  have hd' : d ∈ p.support + q.support := MvPolynomial.support_mul p q hd
  rcases Finset.mem_add.mp hd' with ⟨u, hu, v, hv, huv⟩
  subst d
  simpa using add_le_add (hp hu) (hq hv)

/-- A strict factor times a weak factor is strictly below the sum bound. -/
theorem IsWeightLT.mul_le [DecidableEq σ]
    {w : σ → ℤ} {m n : ℤ} {p q : MvPolynomial σ K}
    (hp : IsWeightLT w m p) (hq : IsWeightLE w n q) :
    IsWeightLT w (m + n) (p * q) := by
  intro d hd
  have hd' : d ∈ p.support + q.support := MvPolynomial.support_mul p q hd
  rcases Finset.mem_add.mp hd' with ⟨u, hu, v, hv, huv⟩
  subst d
  simpa using add_lt_add_of_lt_of_le (hp hu) (hq hv)

/-- A weak factor times a strict factor is strictly below the sum bound. -/
theorem IsWeightLE.mul_lt [DecidableEq σ]
    {w : σ → ℤ} {m n : ℤ} {p q : MvPolynomial σ K}
    (hp : IsWeightLE w m p) (hq : IsWeightLT w n q) :
    IsWeightLT w (m + n) (p * q) := by
  intro d hd
  have hd' : d ∈ p.support + q.support := MvPolynomial.support_mul p q hd
  rcases Finset.mem_add.mp hd' with ⟨u, hu, v, hv, huv⟩
  subst d
  simpa using add_lt_add_of_le_of_lt (hp hu) (hq hv)

/-- A weighted-homogeneous polynomial has its defining weight as a weak upper bound. -/
theorem isWeightLE_of_isWeightedHomogeneous
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p m) :
    IsWeightLE w m p := by
  intro d hd
  exact le_of_eq (hp (MvPolynomial.mem_support_iff.mp hd))

/-- Any component above a weak weight bound vanishes. -/
theorem initialForm_eq_zero_of_isWeightLE
    {w : σ → ℤ} {m n : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLE w m p) (hmn : m < n) :
    initialForm w n p = 0 := by
  ext d
  rw [coeff_initialForm]
  split_ifs with hweight
  · have hcoeff : coeff d p = 0 := by
      by_contra hne
      have hle := hp (MvPolynomial.mem_support_iff.mpr hne)
      rw [hweight] at hle
      omega
    simp [hcoeff]
  · simp

/-- The component at or above a strict weight bound vanishes. -/
theorem initialForm_eq_zero_of_isWeightLT
    {w : σ → ℤ} {m n : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLT w m p) (hmn : m ≤ n) :
    initialForm w n p = 0 := by
  ext d
  rw [coeff_initialForm]
  split_ifs with hweight
  · have hcoeff : coeff d p = 0 := by
      by_contra hne
      have hlt := hp (MvPolynomial.mem_support_iff.mpr hne)
      rw [hweight] at hlt
      omega
    simp [hcoeff]
  · simp

/-- Removing the top exact component leaves a strictly lower-weight remainder. -/
theorem sub_initialForm_isWeightLT [DecidableEq σ]
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLE w m p) :
    IsWeightLT w m (p - initialForm w m p) := by
  intro d hd
  by_contra hnot
  have hge : m ≤ Finsupp.weight w d := by omega
  have hle : Finsupp.weight w d ≤ m := by
    apply hp
    by_contra hdp
    have hpzero : coeff d p = 0 := by
      by_contra hne
      exact hdp (MvPolynomial.mem_support_iff.mpr hne)
    have hdiff : coeff d (p - initialForm w m p) = 0 := by
      rw [MvPolynomial.coeff_sub, hpzero, coeff_initialForm]
      split_ifs <;> simp [hpzero]
    exact (MvPolynomial.mem_support_iff.mp hd) hdiff
  have heq : Finsupp.weight w d = m := le_antisymm hle hge
  have hdiff : coeff d (p - initialForm w m p) = 0 := by
    rw [MvPolynomial.coeff_sub, coeff_initialForm]
    simp [heq]
  exact (MvPolynomial.mem_support_iff.mp hd) hdiff

end

end HC4.Polynomial
