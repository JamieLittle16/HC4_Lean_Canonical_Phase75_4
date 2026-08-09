import HC4.Toric.BranchReversal
import HC4.Toric.SparseEigenSupport

/-!
# Reversal-stable torus eigen-supports

A nonempty support on which the branch character is constant cannot be stable
under coordinate reversal unless that character is zero.  When the support is
also balanced, it therefore lies entirely in the `p,q` cone.
-/

namespace HC4.Toric

/-- A support is closed under coordinate reversal. -/
def ReverseClosed (S : Set Exponent) : Prop :=
  ∀ u ∈ S, reverseExponent u ∈ S

/-- Constant character on a nonempty reversal-closed support must be zero. -/
theorem character_eq_zero_of_reverseClosed
    {S : Set Exponent} {c : ℤ}
    (hne : S.Nonempty) (hrev : ReverseClosed S)
    (hchar : ∀ u ∈ S, branchCharacter u = c) :
    c = 0 := by
  rcases hne with ⟨u, hu⟩
  have hru : reverseExponent u ∈ S := hrev u hu
  have huChar : branchCharacter u = c := hchar u hu
  have hruChar : branchCharacter (reverseExponent u) = c := hchar _ hru
  rw [branchCharacter_reverseExponent, huChar] at hruChar
  linarith

/-- A balanced reversal-closed eigensupport lies in the `p,q` cone. -/
theorem reverseClosed_character_support_onPQCone
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {S : Set Exponent} {c : ℤ}
    (hne : S.Nonempty) (hrev : ReverseClosed S)
    (hBal : ∀ u ∈ S, Balanced a b u)
    (hchar : ∀ u ∈ S, branchCharacter u = c) :
    c = 0 ∧ OnPQCone S := by
  have hc : c = 0 := character_eq_zero_of_reverseClosed hne hrev hchar
  subst c
  exact ⟨rfl, zero_character_support ha hb hcop hBal hchar⟩

/-- Reversal closure for the support of a sparse polynomial. -/
def SparseReverseClosed {K : Type*} [Zero K]
    (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, reverseExponent u ∈ f.support

/-- Sparse reversal-stable constant character must be zero. -/
theorem sparse_character_eq_zero_of_reverseClosed
    {K : Type*} [Zero K] {f : SparsePolynomial K} {c : ℤ}
    (hne : f.support.Nonempty) (hrev : SparseReverseClosed f)
    (hchar : HasSupportCharacter c f) :
    c = 0 := by
  have hS : (↑f.support : Set Exponent).Nonempty := by
    rcases hne with ⟨u, hu⟩
    exact ⟨u, hu⟩
  exact character_eq_zero_of_reverseClosed
    (S := (↑f.support : Set Exponent)) hS
    (fun u hu => hrev u hu) (fun u hu => hchar u hu)

/-- Sparse balanced reversal-stable eigensupport lies in the `p,q` cone. -/
theorem sparse_reverseClosed_character_support_onPQCone
    {K : Type*} [Zero K]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {f : SparsePolynomial K} {c : ℤ}
    (hne : f.support.Nonempty) (hrev : SparseReverseClosed f)
    (hBal : HasBalancedSupport a b f)
    (hchar : HasSupportCharacter c f) :
    c = 0 ∧ SparseOnPQCone f := by
  have hc : c = 0 :=
    sparse_character_eq_zero_of_reverseClosed hne hrev hchar
  subst c
  exact ⟨rfl, sparse_zero_character_support ha hb hcop hBal hchar⟩

/-- A positive-character sparse eigensupport cannot be nonempty and reversal closed. -/
theorem not_nonempty_sparse_reverseClosed_positive_character
    {K : Type*} [Zero K] {f : SparsePolynomial K} {c : ℤ}
    (hc : 0 < c) (hrev : SparseReverseClosed f)
    (hchar : HasSupportCharacter c f) :
    ¬ f.support.Nonempty := by
  intro hne
  have hc0 := sparse_character_eq_zero_of_reverseClosed hne hrev hchar
  linarith

/-- A negative-character sparse eigensupport cannot be nonempty and reversal closed. -/
theorem not_nonempty_sparse_reverseClosed_negative_character
    {K : Type*} [Zero K] {f : SparsePolynomial K} {c : ℤ}
    (hc : c < 0) (hrev : SparseReverseClosed f)
    (hchar : HasSupportCharacter c f) :
    ¬ f.support.Nonempty := by
  intro hne
  have hc0 := sparse_character_eq_zero_of_reverseClosed hne hrev hchar
  linarith

end HC4.Toric
