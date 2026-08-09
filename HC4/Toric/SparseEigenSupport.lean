import HC4.Toric.CharacterSupport
import Mathlib.Data.Finsupp.Basic

/-!
# Sparse polynomial support under torus characters

A sparse four-variable polynomial is represented only by its coefficient
finsupp on exponent vectors.  This module packages the support consequences of
balancedness and a constant branch character, independently of coefficient
values.
-/

namespace HC4.Toric

/-- Sparse coefficient data indexed by four-variable exponent vectors. -/
abbrev SparsePolynomial (K : Type*) [Zero K] := Exponent →₀ K

/-- Every monomial in the support has original torus weight zero. -/
def HasBalancedSupport {K : Type*} [Zero K]
    (a b : ℕ) (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, Balanced a b u

/-- Every supported monomial has the same secondary branch character. -/
def HasSupportCharacter {K : Type*} [Zero K]
    (c : ℤ) (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, branchCharacter u = c

/-- Sparse support lies on a fixed `r` level. -/
def SparseOnRLevel {K : Type*} [Zero K]
    (a b k : ℕ) (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, ∃ i j : ℕ, u = rBranch a b i j k

/-- Sparse support lies on a fixed `s` level. -/
def SparseOnSLevel {K : Type*} [Zero K]
    (a b k : ℕ) (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, ∃ i j : ℕ, u = sBranch a b i j k

/-- Sparse support lies in the `p,q` cone. -/
def SparseOnPQCone {K : Type*} [Zero K]
    (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, ∃ i j : ℕ,
    u = Exponent.add (Exponent.scale i pExponent) (Exponent.scale j qExponent)

/-- Positive character classifies a nonempty sparse support as one positive `r` level. -/
theorem sparse_positive_character_support
    {K : Type*} [Zero K]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {f : SparsePolynomial K} {c : ℤ} (hc : 0 < c)
    (hne : f.support.Nonempty)
    (hBal : HasBalancedSupport a b f)
    (hchar : HasSupportCharacter c f) :
    ∃ k : ℕ, 0 < k ∧ SparseOnRLevel a b k f := by
  let S : Set Exponent := ↑f.support
  have hS : S.Nonempty := by
    rcases hne with ⟨u, hu⟩
    exact ⟨u, hu⟩
  rcases positive_constant_character_support ha hb hcop hc hS
      (fun u hu => hBal u hu) (fun u hu => hchar u hu) with
    ⟨k, hk, hlevel⟩
  exact ⟨k, hk, fun u hu => hlevel u hu⟩

/-- Negative character classifies a nonempty sparse support as one positive `s` level. -/
theorem sparse_negative_character_support
    {K : Type*} [Zero K]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {f : SparsePolynomial K} {c : ℤ} (hc : c < 0)
    (hne : f.support.Nonempty)
    (hBal : HasBalancedSupport a b f)
    (hchar : HasSupportCharacter c f) :
    ∃ k : ℕ, 0 < k ∧ SparseOnSLevel a b k f := by
  let S : Set Exponent := ↑f.support
  have hS : S.Nonempty := by
    rcases hne with ⟨u, hu⟩
    exact ⟨u, hu⟩
  rcases negative_constant_character_support ha hb hcop hc hS
      (fun u hu => hBal u hu) (fun u hu => hchar u hu) with
    ⟨k, hk, hlevel⟩
  exact ⟨k, hk, fun u hu => hlevel u hu⟩

/-- Character zero classifies sparse support as the `p,q` cone. -/
theorem sparse_zero_character_support
    {K : Type*} [Zero K]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {f : SparsePolynomial K}
    (hBal : HasBalancedSupport a b f)
    (hchar : HasSupportCharacter 0 f) :
    SparseOnPQCone f := by
  exact zero_character_support ha hb hcop
    (fun u hu => hBal u hu) (fun u hu => hchar u hu)

/-- Complete sign trichotomy for a nonempty balanced character support. -/
theorem sparse_character_support_trichotomy
    {K : Type*} [Zero K]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {f : SparsePolynomial K} {c : ℤ}
    (hne : f.support.Nonempty)
    (hBal : HasBalancedSupport a b f)
    (hchar : HasSupportCharacter c f) :
    (c = 0 ∧ SparseOnPQCone f) ∨
      (0 < c ∧ ∃ k : ℕ, 0 < k ∧ SparseOnRLevel a b k f) ∨
      (c < 0 ∧ ∃ k : ℕ, 0 < k ∧ SparseOnSLevel a b k f) := by
  rcases lt_trichotomy c 0 with hcNeg | hcZero | hcPos
  · exact Or.inr (Or.inr ⟨hcNeg,
      sparse_negative_character_support ha hb hcop hcNeg hne hBal hchar⟩)
  · subst c
    exact Or.inl ⟨rfl, sparse_zero_character_support ha hb hcop hBal hchar⟩
  · exact Or.inr (Or.inl ⟨hcPos,
      sparse_positive_character_support ha hb hcop hcPos hne hBal hchar⟩)

end HC4.Toric
