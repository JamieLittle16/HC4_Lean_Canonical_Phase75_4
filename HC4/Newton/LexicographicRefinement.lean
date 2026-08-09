import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Finite lexicographic weight refinement

This file isolates the order-theoretic core of the Newton--Rees refinement
used in the HC4 reduction.

For two nonnegative integer weights `w₀` and `w₁`, suppose the secondary
weight is bounded by `M` on a finite support `S`. Then the single scaled
weight

    M * w₀ + w₁

has exactly the same maximisers on `S` as lexicographic maximisation of
`(w₀, w₁)`.

The result is deliberately independent of `MvPolynomial`.  It is the finite
dominance lemma needed before specialising to the project's existing
weighted-initial-form API.
-/

namespace HC4.Newton

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- `x` lexicographically dominates `y`: the primary weight of `x` is
strictly larger, or the primary weights tie and the secondary weight of `x`
is at least that of `y`. -/
def lexDominates (w₀ w₁ : α → ℕ) (x y : α) : Prop :=
  w₀ y < w₀ x ∨ (w₀ y = w₀ x ∧ w₁ y ≤ w₁ x)

/-- The single weight obtained by giving the primary weight scale `M`. -/
def scaledWeight (M : ℕ) (w₀ w₁ : α → ℕ) (x : α) : ℕ :=
  M * w₀ x + w₁ x

/-- `x` is a lexicographic maximum of `(w₀,w₁)` on the finite support `S`. -/
def IsLexMaxOn (S : Finset α) (w₀ w₁ : α → ℕ) (x : α) : Prop :=
  x ∈ S ∧ ∀ ⦃y⦄, y ∈ S → lexDominates w₀ w₁ x y

/-- `x` maximises the single scaled weight `M*w₀+w₁` on `S`. -/
def IsScaledMaxOn
    (S : Finset α) (M : ℕ) (w₀ w₁ : α → ℕ) (x : α) : Prop :=
  x ∈ S ∧
    ∀ ⦃y⦄, y ∈ S → scaledWeight M w₀ w₁ y ≤ scaledWeight M w₀ w₁ x

/-- A strict gain in primary weight cannot be cancelled by a secondary
weight lying below the scale `M`. -/
theorem scaledWeight_lt_of_primary_lt
    {M : ℕ} {w₀ w₁ : α → ℕ} {x y : α}
    (hprimary : w₀ y < w₀ x)
    (hsecondary : w₁ y < M) :
    scaledWeight M w₀ w₁ y < scaledWeight M w₀ w₁ x := by
  have hsucc : w₀ y + 1 ≤ w₀ x := Nat.succ_le_iff.mpr hprimary
  have hsmall :
      M * w₀ y + w₁ y < M * w₀ y + M :=
    Nat.add_lt_add_left hsecondary (M * w₀ y)
  have hstep :
      scaledWeight M w₀ w₁ y < M * (w₀ y + 1) := by
    simpa [scaledWeight, Nat.mul_succ] using hsmall
  have hscale : M * (w₀ y + 1) ≤ M * w₀ x :=
    Nat.mul_le_mul_left M hsucc
  have htop : M * w₀ x ≤ scaledWeight M w₀ w₁ x := by
    simp [scaledWeight]
  exact lt_of_lt_of_le hstep (hscale.trans htop)

/-- Lexicographic domination implies domination for the scaled single weight,
provided the secondary weight of the lower-primary point is below `M`. -/
theorem scaledWeight_le_of_lexDominates
    {M : ℕ} {w₀ w₁ : α → ℕ} {x y : α}
    (hy : w₁ y < M)
    (hlex : lexDominates w₀ w₁ x y) :
    scaledWeight M w₀ w₁ y ≤ scaledWeight M w₀ w₁ x := by
  rcases hlex with hprimary | ⟨hprimary, hsecondary⟩
  · exact (scaledWeight_lt_of_primary_lt hprimary hy).le
  · unfold scaledWeight
    rw [hprimary]
    exact Nat.add_le_add_left hsecondary _

/-- Conversely, scaled domination forces lexicographic domination when the
secondary weight of `x` is below `M`. -/
theorem lexDominates_of_scaledWeight_le
    {M : ℕ} {w₀ w₁ : α → ℕ} {x y : α}
    (hx : w₁ x < M)
    (hscaled : scaledWeight M w₀ w₁ y ≤ scaledWeight M w₀ w₁ x) :
    lexDominates w₀ w₁ x y := by
  by_cases hprimary : w₀ y < w₀ x
  · exact Or.inl hprimary
  by_cases heq : w₀ y = w₀ x
  · right
    refine ⟨heq, ?_⟩
    unfold scaledWeight at hscaled
    rw [heq] at hscaled
    omega
  · have hreverse : w₀ x < w₀ y := by omega
    have hstrict :
        scaledWeight M w₀ w₁ x < scaledWeight M w₀ w₁ y :=
      scaledWeight_lt_of_primary_lt hreverse hx
    exfalso
    exact (Nat.not_lt_of_ge hscaled) hstrict

/-- **Finite lexicographic collapse.** If all secondary weights on `S` are
strictly smaller than `M`, then scaled maxima and lexicographic maxima are
the same points. -/
theorem isScaledMaxOn_iff_isLexMaxOn
    {S : Finset α} {M : ℕ} {w₀ w₁ : α → ℕ} {x : α}
    (hbound : ∀ z ∈ S, w₁ z < M) :
    IsScaledMaxOn S M w₀ w₁ x ↔ IsLexMaxOn S w₀ w₁ x := by
  constructor
  · rintro ⟨hxS, hmax⟩
    refine ⟨hxS, ?_⟩
    intro y hyS
    exact lexDominates_of_scaledWeight_le
      (hbound x hxS) (hmax hyS)
  · rintro ⟨hxS, hmax⟩
    refine ⟨hxS, ?_⟩
    intro y hyS
    exact scaledWeight_le_of_lexDominates
      (hbound y hyS) (hmax hyS)

/-- Set-level form of finite lexicographic collapse. -/
theorem scaledMaxima_eq_lexMaxima
    {S : Finset α} {M : ℕ} {w₀ w₁ : α → ℕ}
    (hbound : ∀ z ∈ S, w₁ z < M) :
    {x | IsScaledMaxOn S M w₀ w₁ x} =
      {x | IsLexMaxOn S w₀ w₁ x} := by
  ext x
  exact isScaledMaxOn_iff_isLexMaxOn hbound

end

end HC4.Newton
