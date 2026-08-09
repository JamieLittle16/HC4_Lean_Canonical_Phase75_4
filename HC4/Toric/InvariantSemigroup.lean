import Mathlib

/-!
# The invariant semigroup for symmetric HC4 gradings

For coprime positive weights `a` and `b`, the diagonal action has weights

    (a, b, -b, -a).

An exponent vector `u = (u₁,u₂,u₃,u₄)` is invariant precisely when

    a u₁ + b u₂ = b u₃ + a u₄.

This module proves the arithmetic normal form used in the symmetric-gradings
paper. Every invariant exponent has exactly one of the two forms

    p^i q^j r^k,                 k ≥ 0,
    p^i q^j s^ℓ,                 ℓ > 0,

where the positive-`r` convention is used on the overlap `k = ℓ = 0`.
The proof also records the exponent relation `r + s = b p + a q`.
-/

namespace HC4.Toric

/-- A four-variable monomial exponent vector. -/
@[ext]
structure Exponent where
  x1 : ℕ
  x2 : ℕ
  x3 : ℕ
  x4 : ℕ
  deriving DecidableEq, Repr

namespace Exponent

/-- Coordinatewise addition of exponent vectors. -/
def add (u v : Exponent) : Exponent :=
  ⟨u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3, u.x4 + v.x4⟩

/-- Coordinatewise natural scaling of an exponent vector. -/
def scale (n : ℕ) (u : Exponent) : Exponent :=
  ⟨n * u.x1, n * u.x2, n * u.x3, n * u.x4⟩

@[simp] theorem add_x1 (u v : Exponent) : (add u v).x1 = u.x1 + v.x1 := rfl
@[simp] theorem add_x2 (u v : Exponent) : (add u v).x2 = u.x2 + v.x2 := rfl
@[simp] theorem add_x3 (u v : Exponent) : (add u v).x3 = u.x3 + v.x3 := rfl
@[simp] theorem add_x4 (u v : Exponent) : (add u v).x4 = u.x4 + v.x4 := rfl

@[simp] theorem scale_x1 (n : ℕ) (u : Exponent) : (scale n u).x1 = n * u.x1 := rfl
@[simp] theorem scale_x2 (n : ℕ) (u : Exponent) : (scale n u).x2 = n * u.x2 := rfl
@[simp] theorem scale_x3 (n : ℕ) (u : Exponent) : (scale n u).x3 = n * u.x3 := rfl
@[simp] theorem scale_x4 (n : ℕ) (u : Exponent) : (scale n u).x4 = n * u.x4 := rfl

end Exponent

/-- Exponent of the invariant `p = x₁x₄`. -/
def pExponent : Exponent := ⟨1, 0, 0, 1⟩

/-- Exponent of the invariant `q = x₂x₃`. -/
def qExponent : Exponent := ⟨0, 1, 1, 0⟩

/-- Exponent of `r = x₁^b x₃^a`. -/
def rExponent (a b : ℕ) : Exponent := ⟨b, 0, a, 0⟩

/-- Exponent of `s = x₂^a x₄^b`. -/
def sExponent (a b : ℕ) : Exponent := ⟨0, a, 0, b⟩

/-- The weight-zero condition for weights `(a,b,-b,-a)`. -/
def Balanced (a b : ℕ) (u : Exponent) : Prop :=
  a * u.x1 + b * u.x2 = b * u.x3 + a * u.x4

/-- The `p^i q^j r^k` exponent normal form. -/
def rBranch (a b i j k : ℕ) : Exponent :=
  ⟨i + b * k, j, j + a * k, i⟩

/-- The `p^i q^j s^k` exponent normal form. -/
def sBranch (a b i j k : ℕ) : Exponent :=
  ⟨i, j + a * k, j, i + b * k⟩

@[simp] theorem balanced_rBranch (a b i j k : ℕ) :
    Balanced a b (rBranch a b i j k) := by
  simp [Balanced, rBranch]
  ring

@[simp] theorem balanced_sBranch (a b i j k : ℕ) :
    Balanced a b (sBranch a b i j k) := by
  simp [Balanced, sBranch]
  ring

/-- The toric relation `rs = p^b q^a`, stated at exponent level. -/
theorem toric_exponent_relation (a b : ℕ) :
    Exponent.add (rExponent a b) (sExponent a b) =
      Exponent.add (Exponent.scale b pExponent) (Exponent.scale a qExponent) := by
  ext <;> simp [Exponent.add, Exponent.scale, pExponent, qExponent,
    rExponent, sExponent]

/-- The `r` normal form is literally a sum of the generator exponents. -/
theorem rBranch_as_generators (a b i j k : ℕ) :
    rBranch a b i j k =
      Exponent.add
        (Exponent.add (Exponent.scale i pExponent) (Exponent.scale j qExponent))
        (Exponent.scale k (rExponent a b)) := by
  ext <;> simp [rBranch, Exponent.add, Exponent.scale, pExponent, qExponent,
    rExponent] <;> ring

/-- The `s` normal form is literally a sum of the generator exponents. -/
theorem sBranch_as_generators (a b i j k : ℕ) :
    sBranch a b i j k =
      Exponent.add
        (Exponent.add (Exponent.scale i pExponent) (Exponent.scale j qExponent))
        (Exponent.scale k (sExponent a b)) := by
  ext <;> simp [sBranch, Exponent.add, Exponent.scale, pExponent, qExponent,
    sExponent] <;> ring

/--
If the fourth exponent does not exceed the first, a balanced exponent lies in
the `r` branch.
-/
theorem balanced_rBranch_of_x4_le_x1
    {a b : ℕ} (_ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u) (h41 : u.x4 ≤ u.x1) :
    ∃ k : ℕ, u = rBranch a b u.x4 u.x2 k := by
  rcases u with ⟨u1, u2, u3, u4⟩
  change u4 ≤ u1 at h41
  simp only [Balanced] at hBal
  have h23 : u2 ≤ u3 := by
    by_contra hNot
    have h32 : u3 < u2 := Nat.lt_of_not_ge hNot
    have haLe : a * u4 ≤ a * u1 := Nat.mul_le_mul_left a h41
    have hbLt : b * u3 < b * u2 := Nat.mul_lt_mul_of_pos_left h32 hb
    have hRhsLtLhs : b * u3 + a * u4 < a * u1 + b * u2 := by
      simpa [Nat.add_comm] using Nat.add_lt_add_of_lt_of_le hbLt haLe
    exact (Nat.ne_of_lt hRhsLtLhs) hBal.symm
  have hu1 : u1 = u4 + (u1 - u4) := by omega
  have hu3 : u3 = u2 + (u3 - u2) := by omega
  have hEq : a * (u1 - u4) = b * (u3 - u2) := by
    have h := hBal
    rw [hu1, hu3] at h
    simp only [mul_add] at h
    omega
  have hbDvd : b ∣ u1 - u4 := by
    apply hcop.symm.dvd_of_dvd_mul_left
    exact ⟨u3 - u2, hEq⟩
  rcases hbDvd with ⟨k, hk⟩
  have hOther : u3 - u2 = a * k := by
    have hCancel : b * (a * k) = b * (u3 - u2) := by
      calc
        b * (a * k) = a * (b * k) := by ring
        _ = a * (u1 - u4) := by rw [hk]
        _ = b * (u3 - u2) := hEq
    exact Nat.mul_left_cancel hb hCancel.symm
  have hU1 : u1 = u4 + b * k := by omega
  have hU3 : u3 = u2 + a * k := by omega
  refine ⟨k, ?_⟩
  ext <;> simp [rBranch, hU1, hU3]

/--
If the first exponent is strictly smaller than the fourth, a balanced exponent
lies in the positive `s` branch.
-/
theorem balanced_sBranch_of_x1_lt_x4
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} (hBal : Balanced a b u) (h14 : u.x1 < u.x4) :
    ∃ k : ℕ, 0 < k ∧ u = sBranch a b u.x1 u.x3 k := by
  rcases u with ⟨u1, u2, u3, u4⟩
  change u1 < u4 at h14
  simp only [Balanced] at hBal
  have h32 : u3 ≤ u2 := by
    by_contra hNot
    have h23 : u2 < u3 := Nat.lt_of_not_ge hNot
    have haLt : a * u1 < a * u4 := Nat.mul_lt_mul_of_pos_left h14 ha
    have hbLe : b * u2 ≤ b * u3 := Nat.mul_le_mul_left b (Nat.le_of_lt h23)
    have hLhsLtRhs : a * u1 + b * u2 < b * u3 + a * u4 := by
      simpa [Nat.add_comm] using Nat.add_lt_add_of_lt_of_le haLt hbLe
    exact (Nat.ne_of_lt hLhsLtRhs) hBal
  have hu4 : u4 = u1 + (u4 - u1) := by omega
  have hu2 : u2 = u3 + (u2 - u3) := by omega
  have hEq : a * (u4 - u1) = b * (u2 - u3) := by
    have h := hBal
    rw [hu4, hu2] at h
    simp only [mul_add] at h
    omega
  have hbDvd : b ∣ u4 - u1 := by
    apply hcop.symm.dvd_of_dvd_mul_left
    exact ⟨u2 - u3, hEq⟩
  rcases hbDvd with ⟨k, hk⟩
  have hOther : u2 - u3 = a * k := by
    have hCancel : b * (a * k) = b * (u2 - u3) := by
      calc
        b * (a * k) = a * (b * k) := by ring
        _ = a * (u4 - u1) := by rw [hk]
        _ = b * (u2 - u3) := hEq
    exact Nat.mul_left_cancel hb hCancel.symm
  have hU4 : u4 = u1 + b * k := by omega
  have hU2 : u2 = u3 + a * k := by omega
  have hkPos : 0 < k := by
    by_contra hNot
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hNot
    subst k
    have hEqZero : u4 = u1 := by simpa using hU4
    exact (Nat.ne_of_lt h14) hEqZero.symm
  refine ⟨k, hkPos, ?_⟩
  ext <;> simp [sBranch, hU4, hU2]

/--
The invariant-semigroup normal form.  The `s` branch is required to have a
strictly positive final exponent, so the two alternatives are disjoint.
-/
theorem balanced_iff_normal_form
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {u : Exponent} :
    Balanced a b u ↔
      (∃ i j k : ℕ, u = rBranch a b i j k) ∨
      (∃ i j k : ℕ, 0 < k ∧ u = sBranch a b i j k) := by
  constructor
  · intro hBal
    by_cases h41 : u.x4 ≤ u.x1
    · obtain ⟨k, hk⟩ :=
        balanced_rBranch_of_x4_le_x1 ha hb hcop hBal h41
      exact Or.inl ⟨u.x4, u.x2, k, hk⟩
    · have h14 : u.x1 < u.x4 := Nat.lt_of_not_ge h41
      obtain ⟨k, hkPos, hk⟩ :=
        balanced_sBranch_of_x1_lt_x4 ha hb hcop hBal h14
      exact Or.inr ⟨u.x1, u.x3, k, hkPos, hk⟩
  · rintro (⟨i, j, k, rfl⟩ | ⟨i, j, k, _hkPos, rfl⟩)
    · exact balanced_rBranch a b i j k
    · exact balanced_sBranch a b i j k

/-- Parameters in the `r` branch are unique. -/
theorem rBranch_parameters_unique
    {a b i j k i' j' k' : ℕ} (hb : 0 < b)
    (h : rBranch a b i j k = rBranch a b i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hi : i = i' := by
    simpa [rBranch] using congrArg Exponent.x4 h
  have hj : j = j' := by
    simpa [rBranch] using congrArg Exponent.x2 h
  subst i'
  subst j'
  have hx1 : i + b * k = i + b * k' := by
    simpa [rBranch] using congrArg Exponent.x1 h
  have hbk : b * k = b * k' := Nat.add_left_cancel hx1
  have hk : k = k' := Nat.mul_left_cancel hb hbk
  exact ⟨rfl, rfl, hk⟩

/-- Parameters in the `s` branch are unique. -/
theorem sBranch_parameters_unique
    {a b i j k i' j' k' : ℕ} (hb : 0 < b)
    (h : sBranch a b i j k = sBranch a b i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hi : i = i' := by
    simpa [sBranch] using congrArg Exponent.x1 h
  have hj : j = j' := by
    simpa [sBranch] using congrArg Exponent.x3 h
  subst i'
  subst j'
  have hx4 : i + b * k = i + b * k' := by
    simpa [sBranch] using congrArg Exponent.x4 h
  have hbk : b * k = b * k' := Nat.add_left_cancel hx4
  have hk : k = k' := Nat.mul_left_cancel hb hbk
  exact ⟨rfl, rfl, hk⟩

/-- A positive `s` branch cannot equal any `r` branch. -/
theorem rBranch_ne_positive_sBranch
    {a b i j k i' j' l : ℕ} (hb : 0 < b) (hl : 0 < l) :
    rBranch a b i j k ≠ sBranch a b i' j' l := by
  intro h
  have hx1 : i + b * k = i' := by
    simpa [rBranch, sBranch] using congrArg Exponent.x1 h
  have hx4 : i = i' + b * l := by
    simpa [rBranch, sBranch] using congrArg Exponent.x4 h
  have hbl : 0 < b * l := Nat.mul_pos hb hl
  omega

end HC4.Toric
