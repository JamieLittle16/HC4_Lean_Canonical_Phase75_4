import HC4.Newton.LexicographicInitialForm

/-!
# Iterated finite refinement equals one exposed weight

Phase 89.1 proved that a sufficiently separated single weight
`M*w₀+w₁` has the same maximisers as lexicographic maximisation of
`(w₀,w₁)`. Phase 89.2 lifted that statement to literal equality of
`MvPolynomial` exposed sums.

This file identifies lexicographic maximisation with the genuinely
two-stage finite procedure:

1. retain the points maximising the primary weight `w₀`;
2. among those points, retain the points maximising the secondary weight
   `w₁`.

Combining this with Phase 89.2 gives the finite Newton--Rees bridge:
a two-stage refinement is exposed directly on the original polynomial by
one sufficiently separated weight.
-/

namespace HC4.Newton

noncomputable section

variable {α : Type*}

/-- `x` maximises the primary weight `w₀` on the finite support `S`. -/
def IsPrimaryMaxOn
    (S : Finset α) (w₀ : α → ℕ) (x : α) : Prop :=
  x ∈ S ∧ ∀ ⦃y⦄, y ∈ S → w₀ y ≤ w₀ x

/-- `x` survives the two-stage refinement: it is a primary maximum and its
secondary weight is maximal among all primary maxima. -/
def IsSecondaryMaxOnPrimary
    (S : Finset α) (w₀ w₁ : α → ℕ) (x : α) : Prop :=
  IsPrimaryMaxOn S w₀ x ∧
    ∀ ⦃y⦄, IsPrimaryMaxOn S w₀ y → w₁ y ≤ w₁ x

/-- Lexicographic maximality is exactly the result of first maximising the
primary weight and then maximising the secondary weight on the primary
face. -/
theorem isSecondaryMaxOnPrimary_iff_isLexMaxOn
    {S : Finset α} {w₀ w₁ : α → ℕ} {x : α} :
    IsSecondaryMaxOnPrimary S w₀ w₁ x ↔
      IsLexMaxOn S w₀ w₁ x := by
  constructor
  · rintro ⟨hxPrimary, hxSecondary⟩
    rcases hxPrimary with ⟨hxS, hxMax⟩
    refine ⟨hxS, ?_⟩
    intro y hyS
    have hyLe : w₀ y ≤ w₀ x := hxMax hyS
    by_cases hlt : w₀ y < w₀ x
    · exact Or.inl hlt
    · have hxLe : w₀ x ≤ w₀ y := Nat.le_of_not_gt hlt
      have heq : w₀ y = w₀ x := Nat.le_antisymm hyLe hxLe
      right
      refine ⟨heq, ?_⟩
      apply hxSecondary
      refine ⟨hyS, ?_⟩
      intro z hzS
      have hzLe : w₀ z ≤ w₀ x := hxMax hzS
      simpa [heq] using hzLe
  · rintro ⟨hxS, hlex⟩
    have hxPrimary : IsPrimaryMaxOn S w₀ x := by
      refine ⟨hxS, ?_⟩
      intro y hyS
      rcases hlex hyS with hlt | ⟨heq, _⟩
      · exact Nat.le_of_lt hlt
      · exact Nat.le_of_eq heq
    refine ⟨hxPrimary, ?_⟩
    intro y hyPrimary
    rcases hyPrimary with ⟨hyS, hyMax⟩
    rcases hlex hyS with hlt | ⟨_, hsecondary⟩
    · have hxLe : w₀ x ≤ w₀ y := hyMax hxS
      exact False.elim ((Nat.not_lt_of_ge hxLe) hlt)
    · exact hsecondary

variable {σ R : Type*} [CommSemiring R]

/-- The literal polynomial produced by the two-stage finite refinement:
primary-weight maxima first, then secondary-weight maxima inside the primary
face. -/
noncomputable def iteratedInitialForm
    [DecidableEq σ]
    (p : MvPolynomial σ R)
    (w₀ w₁ : (σ →₀ ℕ) → ℕ) :
    MvPolynomial σ R :=
  selectedInitial p
    (fun d =>
      IsSecondaryMaxOnPrimary p.support w₀ w₁ d)

/-- The two-stage exposed polynomial is exactly the lexicographically
exposed polynomial. -/
theorem iteratedInitialForm_eq_lexInitialForm
    [DecidableEq σ]
    (p : MvPolynomial σ R)
    (w₀ w₁ : (σ →₀ ℕ) → ℕ) :
    iteratedInitialForm p w₀ w₁ =
      lexInitialForm p w₀ w₁ := by
  classical
  unfold iteratedInitialForm lexInitialForm selectedInitial
  have hfaces :
      p.support.filter
          (fun d =>
            IsSecondaryMaxOnPrimary p.support w₀ w₁ d) =
        p.support.filter
          (fun d => IsLexMaxOn p.support w₀ w₁ d) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hiter⟩
      exact
        ⟨hd,
          (isSecondaryMaxOnPrimary_iff_isLexMaxOn).mp hiter⟩
    · rintro ⟨hd, hlex⟩
      exact
        ⟨hd,
          (isSecondaryMaxOnPrimary_iff_isLexMaxOn).mpr hlex⟩
  rw [hfaces]

/-- **Two-stage finite Rees refinement is a single exposed face.**
If every secondary weight on the support is `< M`, then the polynomial
obtained by first taking the primary face and then the secondary face is
exactly the face exposed on the original polynomial by `M*w₀+w₁`. -/
theorem scaledInitialForm_eq_iteratedInitialForm
    [DecidableEq σ]
    (p : MvPolynomial σ R)
    (M : ℕ)
    (w₀ w₁ : (σ →₀ ℕ) → ℕ)
    (hbound : ∀ d ∈ p.support, w₁ d < M) :
    scaledInitialForm p M w₀ w₁ =
      iteratedInitialForm p w₀ w₁ := by
  calc
    scaledInitialForm p M w₀ w₁ =
        lexInitialForm p w₀ w₁ :=
      scaledInitialForm_eq_lexInitialForm p M w₀ w₁ hbound
    _ = iteratedInitialForm p w₀ w₁ :=
      (iteratedInitialForm_eq_lexInitialForm p w₀ w₁).symm

end

end HC4.Newton
